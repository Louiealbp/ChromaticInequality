# Theorem 8.2: unrestricted uniform positivity

**Verified release:** all 146 local proof modules were rebuilt from source.
The complete library build and the strengthened 1,890-theorem axiom and
statement audit passed. `VERIFICATION.md` records the results; the complete
command logs and source hashes are included under `verification/`.

This Lean project formalizes Theorem 8.2 of *The Complexity of Deterministic
Connectivity*, by Sanjeev Khanna, Aaron Putterman, and Madhu Sudan, in the
uploaded draft dated October 21, 2026. 
## Exact theorem

For every positive integer `k` and every real `k × k` matrix `S` whose entries
are all `1` or `-1`, let

\[
a=10^{-7},\qquad
\theta=\frac{a}{\sqrt{k}\log(4k)},\qquad
\phi=\mathbb E_{\sigma,\tau\sim\mathrm{Unif}(\{-1,1\}^k)}
       \exp(i\theta\sigma^{\mathsf T}S\tau).
\]

The two sign vectors are independent. The conclusion is

\[
\operatorname{Im}\phi=0,\qquad
\operatorname{Re}\phi\geq
\frac14\exp\!\left(-\frac{64a^2k}{\log(4k)}\right)>0.
\]

The logarithm is outside the square root. There is no dimension cutoff and no
symmetry, rank, or positive-semidefiniteness assumption on `S`.

## Public declarations

After building, use:

```lean
import TheoremA2

#check TheoremA2.theorem_A_2
#check TheoremA2.theorem_A_2_explicit
#check TheoremA2.uniformPositivity
```

The main declaration has the interface:

```lean
theorem theorem_A_2 {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : IsSignMatrix S) : A2Conclusion S
```

`theorem_A_2_explicit` exposes the numerical constants, angle, and lower bound.
`Audit.lean` additionally checks the statement with the expectation expanded
into its literal double sum over `Fin k → Bool`, using the explicit uniform
weights `(2^k)⁻¹` and explicit signs `if b then 1 else -1`.

## Reproducing the verification

The project pins Lean `v4.35.0-rc2` and mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The complete transitive package pins
are recorded in `lake-manifest.json`.

With Lean's toolchain manager, Python 3, and a POSIX shell available, run
from the extracted directory (the tested platform is Linux):

```sh
lake exe cache get
./verify.sh
```

The verification script runs genuine Lake module builds serially, then the
whole-library build and the separate Lean audit. It stops with a nonzero exit
code if any command fails or a proof source changes during verification.
The release contains source files and verification evidence; it contains no
precompiled local proof objects. `SHA256SUMS` records every delivered file
other than itself, and `RELEASE_MANIFEST.json` records the verified source
inventory.

The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
It checks the transitive axioms of every local theorem in the proof namespaces,
rejects local axiom declarations, requires the public exports to be theorem
declarations, and typechecks the independently expanded final statement.

## Proof organization

The proof retains the paper's dimension-uniform analytic structure:

1. Establish the convex-support estimate, Gaussian decoder estimate, and the
   full infinite-lattice cell bound.
2. Compare the signed Gaussian cosine product with its actual positive
   envelope, preserving errors relative to the positive normalizer.
3. Prove the weighted second-moment comparison using the exact rank-one
   Gaussian tilt, a genuine auxiliary-Gaussian integral, and the fourth-moment
   estimate from Brascamp–Lieb.
4. Transfer the comparison to the actual zero-field spin covariance, using
   the proved Fourier identities and Cramér–Rao integration-by-parts bound.
5. Absorb the explicit errors and extend the precision estimate to every
   field through the exact two-copy disagreement-mask argument.
6. Construct the actual joint spin–continuous law, prove its covariance and
   MGF estimates, and use them to bound all noncentral periodic cells.
7. Substitute the exact constants and combine the relative comparison with
   the positive reference normalizer lower bound.

The final theorem has no covariance, MGF, integration-by-parts, lattice-tail,
or relative-comparison premise. Such premises occur only in reusable
intermediate lemmas and are discharged in the final proof.

`PROOF_GUIDE.md` gives the detailed correspondence between the paper and the
Lean modules, including three fully proved adaptations: direct Gaussian
change of measure and Jensen for the lattice estimate, a direct convolution
argument for the scalar reference estimates, and global smooth extensions
with dominated convergence for the singular cosine prior.

## Brascamp–Lieb dependency

The project includes the 57-module source closure of the actual
Brascamp–Lieb theorem from Djalil Chafai's
[ginibre-poincare project](https://github.com/djalilchafai/ginibre-poincare),
pinned at commit `be028188dd8758cd9a30db1a462eaed9140856d4`.
Its theorem is applied to the actual potentials, Hessians, measures, and
observables; no elliptic-solution certificate or target variance inequality
is assumed. The MIT license and the exact upstream/adaptation manifest are
included under `third_party/`.

The trust boundary is Lean's kernel, its standard foundational axioms, the
pinned mathlib dependencies, and the supplied checked proof sources. The
independent statement review addresses the separate question of whether the
formal statement expresses the theorem in the paper.
