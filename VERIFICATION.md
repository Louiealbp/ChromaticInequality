# Verification record: unrestricted Theorem A.2

**Release gate: PASSED on 2026-10-21 UTC.** All 146 local source modules, the
whole-library build, and the strengthened 1,890-theorem axiom and expanded
statement audit completed successfully.

## Statement fidelity

The target is Theorem A.2 of the uploaded October 21, 2026 draft of
*The Complexity of Deterministic Connectivity*, by Sanjeev Khanna, Aaron
Putterman, and Madhu Sudan. The statement is on printed page 45 and the final
parameter substitution is on printed page 89. `README.md` records the source
PDF's SHA-256.

The public theorem quantifies over every positive natural number `k` and every
real matrix `S : Matrix (Fin k) (Fin k) ℝ` whose entries are `1` or `-1`.
It uses exactly

\[
a=1/10^7,\qquad \theta=\frac{a}{\sqrt{k}\log(4k)},\qquad
b=\tfrac14\exp\!\left(-\frac{64a^2k}{\log(4k)}\right).
\]

The conclusion is zero imaginary part, real part at least `b`, and `0 < b`.
`characteristic` is the literal independent uniform double average of the
complex exponential. `Audit.lean` checks the same statement with both averages,
the signs, and the bilinear form expanded explicitly. This guards against a
definition silently replacing the requested expectation with a simpler object.

## Compilation and reproducibility

The tested toolchain is:

```text
Lean 4.35.0-rc2, x86_64-unknown-linux-gnu
commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release
mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55
```

The project contains 146 local proof modules: 80 `TheoremA2` modules including
the root import, 9 Brascamp–Lieb wrapper modules, and 57 vendored proof modules.
`Audit.lean` is an additional, separate verification file.

The fresh verification removes all preexisting project-local build objects
from the build path and runs genuine `lake build +Module:olean` commands in
source-import order, followed by `lake build TheoremA2`. Dependency package
caches remain available. Lake's optional artifact-restoration cache is disabled
for this verification. The driver does not synthesize build traces, compiled
proof objects, or success results. Every command's actual exit status is logged.

The portable `verify.sh` performs the same serial module builds, whole-library
build, and independent Lean audit. This limits concurrent compiler memory use.
It requires Python 3, a POSIX shell, and the pinned Lean toolchain; it uses
POSIX `fcntl` file locking. The tested platform is Linux. It fails on a
failed command or on a source/configuration change during verification.

### Recorded successful runs

| Gate | Result | Evidence directory |
| --- | --- | --- |
| Fresh local module builds | 146 of 146 returned exit code 0 | `verification/fresh-build/` |
| Fresh whole-library build and original audit | Both returned exit code 0 | `verification/fresh-build/` |
| Final module and whole-library checks | All returned exit code 0 | `verification/final-build/` |
| Strengthened final audit | 1,890 theorem declarations; exit code 0 | `verification/final-build/final-audit.log` |

Each run includes the actual command outputs, per-command exit statuses,
`results.json`, `source-manifest.json`, and `SUCCESS.txt`. The original
fresh-build audit checked 1,832 declarations. The final audit checks 1,890
by also selecting the unmangled names of private helpers; it still examines
the dependencies of each original declaration. Only `Audit.lean` changed
between these two runs. All 146 proof modules and all three build/toolchain
configuration files are byte-for-byte identical in the two source manifests.

Release packaging separately compares every source against the final
verification manifest and every archived byte against the staged files.
`RELEASE_MANIFEST.json` and `SHA256SUMS` record the delivered file inventory.

All nine dependency checkouts match the manifest revisions, have clean tracked
worktrees, and have no untracked nonignored Lean/configuration files. The exact
read-only audit is in `verification/dependency-and-vendor-audit.json` and its
human-readable companion.

## Axiom and declaration audit

`Audit.lean` requires the public declarations `theorem_A_2`,
`theorem_A_2_explicit`, and `uniformPositivity` to be actual theorem declarations.
It rejects local axiom declarations and checks the full transitive axiom
dependencies of local theorem declarations, including private helper names.
The only permitted axioms are:

```text
propext
Classical.choice
Quot.sound
```

The audit also prints the transitive axiom dependencies of the final theorem,
the actual relative comparison, the actual joint variance and MGF estimates,
the actual all-field spin covariance bound, and the vendored Brascamp–Lieb
endpoint. The independently expanded double-sum statement is typechecked in
the same file.

Source reviews additionally checked for `sorry`, `admit`, custom axioms,
`native_decide`, unsafe/external proof implementations, kernel-check disabling,
and declaration-injection shortcuts. None was found in the proof closure.
The transitive kernel-environment audit is the stronger check for axioms
actually used by the proofs.

## Adversarial review

Three independent agents reviewed complementary parts of the development
throughout implementation and integration. Their final reviews checked:

| Review area | Concrete checks |
| --- | --- |
| Mathematical correspondence | Exact constants and quantifiers; relative errors preserve their actual normalizers; full infinite lattice; both pointwise error supports; exact rank-one Gaussian tilt; no signed probability law. |
| Formal statement and assembly | Literal independent uniform double sum; no dimension, rank, symmetry, or PSD restriction on `S`; all intermediate analytic premises discharged; correct Euclidean/coordinate bridge and all factors of two. |
| Analytic foundations and trust | Actual BL potentials, Hessians, measures, derivatives and integrability; genuine Cramér–Rao integration by parts; actual prior limits; source provenance, package pins, axiom audit logic and private-helper coverage. |

The reviews verified empty disagreement masks, arbitrary external fields,
zero coordinate variances, and singular derived matrices where the relevant
lemma permits them. Positive definiteness is introduced only where an actual
inverse or Gaussian density requires it. The derived Gram matrix is proved
PSD for arbitrary `S`; PSD is not an assumption on the input matrix.

These reviews address the semantic correspondence with the paper. Lean's
kernel checking independently establishes that the supplied proof terms prove
the supplied formal statements under the listed foundational axioms.

## Proof adaptations and dependency provenance

The formalization preserves the paper's relative-comparison strategy and
exact final constants. Three proof-engineering adaptations are fully proved:

1. A.25 uses direct Gaussian change of measure and Jensen, the variational form
   of the entropy argument, on the actual joint decoder likelihood. The
   projected coordinates retain their dependence through one latent Gaussian.
2. The scalar reference estimates use a direct convolution and symmetrized
   cosine proof for the same actual reference function and error constants.
3. A.33 uses concrete global C² extensions and dominated convergence for the
   singular cosine prior. The actual mass, first moment, and second moment
   converge, including the boundary endpoints; the identified positive common
   factor cancels after normalization.

The genuine Brascamp–Lieb proof is included from Djalil Chafai's MIT-licensed
`ginibre-poincare` repository, pinned at
`be028188dd8758cd9a30db1a462eaed9140856d4`. All 57 proof bodies are unchanged.
Exactly three files have import-only adaptations; the other 54 complete-file
hashes match upstream. The supplied license, source manifest, and independent
diff/hash audit record this precisely.

The final theorem has no assumed covariance estimate, MGF bound, lattice-tail
estimate, relative comparison, or analytic certificate. Its only hypotheses
are the positive dimension and the entrywise sign condition.
