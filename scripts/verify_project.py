#!/usr/bin/env python3
"""Run genuine Lake module builds serially, followed by the library build.

This is a verification driver, not a replacement build system. It never creates
or edits Lake traces, hashes, oleans, or caches. Lake alone produces those files.
Move only the root project's .lake/build directory aside before the first run
if a fresh local-source rebuild is required. Package dependency caches stay put.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


DEFAULT_PROJECT = Path(__file__).resolve().parents[1]
NAMESPACES = ('TheoremA2', 'GinibrePoincare', 'BrascampLieb')


def without_comments(text: str) -> str:
    """Remove Lean line/nested-block comments while retaining line breaks.

    Strings are retained and skipped when recognizing comment delimiters. This
    prevents an example import inside a documentation comment from becoming a
    dependency. Actual imports in this project use ordinary identifier names.
    """
    output: list[str] = []
    index = 0
    depth = 0
    quoted = False
    while index < len(text):
        if depth:
            if text.startswith('/-', index):
                depth += 1
                index += 2
            elif text.startswith('-/', index):
                depth -= 1
                index += 2
            else:
                output.append('\n' if text[index] == '\n' else ' ')
                index += 1
        elif quoted:
            output.append(text[index])
            if text[index] == '\\' and index + 1 < len(text):
                index += 1
                output.append(text[index])
            elif text[index] == '"':
                quoted = False
            index += 1
        elif text.startswith('/-', index):
            output.append(' ')
            depth = 1
            index += 2
        elif text.startswith('--', index):
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        else:
            output.append(text[index])
            if text[index] == '"':
                quoted = True
            index += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(output)


def source_modules(project: Path) -> dict[str, Path]:
    modules: dict[str, Path] = {}
    for namespace in NAMESPACES:
        directory = project / namespace
        if not directory.is_dir():
            raise ValueError(f'Missing source directory: {directory}')
        paths = list(directory.rglob('*.lean'))
        root_source = project / f'{namespace}.lean'
        if root_source.is_file():
            paths.append(root_source)
        for source in paths:
            name = '.'.join(source.relative_to(project).with_suffix('').parts)
            modules[name] = source
    return modules


def topological_order(modules: dict[str, Path]) -> list[str]:
    dependency_map: dict[str, list[str]] = {}
    for name, source in modules.items():
        code = without_comments(source.read_text())
        dependencies: list[str] = []
        for match in re.finditer(r'^\s*(?:public\s+|private\s+)?import\s+([^\n]+)',
                                 code, re.MULTILINE):
            for dependency in match.group(1).split():
                if dependency in modules:
                    dependencies.append(dependency)
                elif any(dependency == n or dependency.startswith(n + '.')
                         for n in NAMESPACES):
                    raise ValueError(f'{name} imports missing local source {dependency}')
        dependency_map[name] = dependencies

    ordered: list[str] = []
    complete: set[str] = set()
    active: list[str] = []

    def visit(name: str) -> None:
        if name in complete:
            return
        if name in active:
            raise ValueError('Import cycle: ' + ' -> '.join(active + [name]))
        active.append(name)
        for dependency in dependency_map[name]:
            visit(dependency)
        active.pop()
        complete.add(name)
        ordered.append(name)

    for name in sorted(modules):
        visit(name)
    return ordered


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_command(command: list[str], project: Path, environment: dict[str, str],
                per_command: Path, aggregate, label: str) -> int:
    header = f'\n=== {label} ===\ncommand: {json.dumps(command)}\n'
    aggregate.write(header)
    aggregate.flush()
    with per_command.open('w') as log:
        log.write(header)
        log.flush()
        started = time.monotonic()
        process = subprocess.Popen(command, cwd=project, env=environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, errors='replace', bufsize=1)
        assert process.stdout is not None
        try:
            for line in process.stdout:
                log.write(line)
                log.flush()
                aggregate.write(line)
                aggregate.flush()
            status = process.wait()
        except BaseException:
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            raise
        footer = f'\nexit_code: {status}\nelapsed_seconds: {time.monotonic() - started:.3f}\n'
        log.write(footer)
        aggregate.write(footer)
        aggregate.flush()
    return status


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=DEFAULT_PROJECT)
    parser.add_argument('--runtime-bin', type=Path,
                        help='Optional explicit Lean runtime bin directory; otherwise use lake on PATH')
    parser.add_argument('--logs', type=Path,
                        help='Fresh log directory; default: project/lake-verification/TIMESTAMP')
    parser.add_argument('--require-fresh', action='store_true',
                        help='Refuse if any root-project local olean is already present')
    parser.add_argument('--audit', type=Path,
                        help='After the full Lake build, run lake env lean -DautoImplicit=false on this file')
    parser.add_argument('--plan-only', action='store_true',
                        help='Validate the source DAG and print targets without executing or writing')
    args = parser.parse_args()
    project = args.project.resolve()
    if args.runtime_bin is None:
        executable = shutil.which('lake')
        if executable is None:
            raise ValueError('lake is not on PATH; install the pinned Lean toolchain first')
        # Keep the name `lake`: an elan shim dispatches using its executable name.
        lake = Path(executable).absolute()
        runtime = lake.parent
    else:
        runtime = args.runtime_bin.resolve()
        lake = runtime / 'lake'
    if not lake.is_file():
        raise ValueError(f'Missing Lake executable: {lake}')
    modules = source_modules(project)
    ordered = topological_order(modules)
    if args.plan_only:
        print(f'{len(ordered)} local modules, in source-import topological order:')
        print('\n'.join(f'+{name}:olean' for name in ordered))
        print('Final library target: TheoremA2')
        return 0
    if args.require_fresh:
        existing = [project / '.lake/build/lib/lean' /
                    modules[name].relative_to(project).with_suffix('.olean')
                    for name in ordered]
        if any(path.exists() for path in existing):
            raise ValueError('Root-project oleans exist; move only .lake/build aside first, '
                             'or omit --require-fresh for a genuine Lake incremental resume.')

    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    logs = (args.logs or project / 'lake-verification' / stamp).resolve()
    logs.mkdir(parents=True, exist_ok=False)
    environment = os.environ.copy()
    environment['PATH'] = str(runtime) + os.pathsep + environment.get('PATH', '')
    environment['LEAN_NUM_THREADS'] = '1'
    # Existing valid dependency builds remain usable. Disable artifact restore
    # and remote cache downloads so a fresh local build genuinely compiles.
    environment['LAKE_ARTIFACT_CACHE'] = 'false'
    environment['LAKE_NO_CACHE'] = 'true'
    environment['TERM'] = 'dumb'
    sources = dict(modules)
    for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json'):
        path = project / name
        if path.is_file():
            sources[name] = path
    if args.audit:
        audit = args.audit if args.audit.is_absolute() else project / args.audit
        audit = audit.resolve()
        if not audit.is_file():
            raise ValueError(f'Missing audit source: {audit}')
        sources['audit:' + str(audit)] = audit
    else:
        audit = None
    frozen = {name: digest(path) for name, path in sources.items()}
    manifest = {
        'project': str(project), 'runtime_bin': str(runtime),
        'module_order': ordered, 'source_sha256': frozen,
        'LEAN_NUM_THREADS': '1',
        'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_NO_CACHE': 'true',
        'note': 'Source inventory only. No Lake build trace or artifact was synthesized.',
    }
    (logs / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (logs / 'module-order.txt').write_text('\n'.join(ordered) + '\n')
    results: list[dict] = []

    def assert_frozen() -> None:
        changed = [name for name, path in sources.items() if digest(path) != frozen[name]]
        if changed:
            raise RuntimeError('Sources changed during verification: ' + ', '.join(changed))

    lock_directory = project / 'compile-logs'
    lock_directory.mkdir(exist_ok=True)
    print(f'Waiting for exclusive compiler slot; genuine build logs: {logs}', flush=True)
    with (lock_directory / 'compiler-slot-0.lock').open('w') as lock, \
            (logs / 'aggregate.log').open('w') as aggregate:
        fcntl.flock(lock, fcntl.LOCK_EX)
        print(f'Acquired compiler slot; verifying {len(ordered)} local modules.', flush=True)
        for number, name in enumerate(ordered, 1):
            assert_frozen()
            print(f'[{number}/{len(ordered)}] Lake {name}', flush=True)
            command = [str(lake), 'build', f'+{name}:olean']
            status = run_command(command, project, environment,
                                 logs / f'{number:03d}-{name}.log', aggregate, name)
            results.append({'module': name, 'exit_code': status})
            (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            if status:
                print(f'FAILED: {name}; see {logs}', flush=True)
                return status if status > 0 else 1
        assert_frozen()
        print('Running final genuine lake build TheoremA2.', flush=True)
        status = run_command([str(lake), 'build', 'TheoremA2'], project, environment,
                             logs / 'final-library.log', aggregate, 'final library build')
        results.append({'target': 'TheoremA2', 'exit_code': status})
        (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if status:
            print(f'FAILED: final library build; see {logs}', flush=True)
            return status if status > 0 else 1
        if audit is not None:
            assert_frozen()
            print(f'Running final axiom audit: {audit}', flush=True)
            status = run_command([str(lake), 'env', 'lean', '-DautoImplicit=false', str(audit)],
                                 project, environment, logs / 'final-audit.log', aggregate,
                                 'final axiom audit')
            results.append({'audit': str(audit), 'exit_code': status})
            (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            if status:
                print(f'FAILED: final audit; see {logs}', flush=True)
                return status if status > 0 else 1
        assert_frozen()
        (logs / 'SUCCESS.txt').write_text(
            f'All {len(ordered)} genuine Lake module targets and the final library target '
            'returned exit code 0.\n'
            + ('The final audit returned exit code 0.\n' if audit is not None else '')
            + 'All inventoried source and configuration hashes were unchanged.\n')
        print(f'Genuine Lake verification completed successfully: {logs}', flush=True)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(f'Verification driver error: {error}', file=sys.stderr, flush=True)
        raise SystemExit(1)
