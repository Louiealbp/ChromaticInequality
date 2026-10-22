# Proof architecture and correspondence with the paper

**Verified proof architecture.** The complete 146-module source closure was
rebuilt successfully, and the final 1,890-theorem axiom and expanded-statement
audit passed. `VERIFICATION.md` and the included logs identify the exact
source tree checked.

## Statement and quantifiers

The public declaration is `TheoremA2.theorem_A_2`. Its only hypotheses are
`0 < k` and `IsSignMatrix S`, where the latter means that every real entry of
the arbitrary square matrix `S` equals either `1` or `-1`. There is no bound on
`k`, and there is no symmetry, rank, or positive-semidefiniteness hypothesis
on `S`.

`Spin k` is `Fin k → Bool`. The function `sign` sends `false` to `-1` and
`true` to `1`. `characteristic S t` is a literal double normalized finite sum
of the complex exponential of `t * bilinear S σ τ * I`. Each of the two sums
ranges independently over every spin vector. `A2Conclusion S` states that
the imaginary part vanishes, the real part has the exact lower bound, and
that lower bound is strictly positive.

The constants are exact real expressions:

\[
a=1/10^7,\qquad
\theta=\frac{a}{\sqrt{k}\log(4k)},\qquad
b=\frac14\exp\!\left(-\frac{64a^2k}{\log(4k)}\right).
\]

The logarithm is outside the square root. `theorem_A_2_explicit` exposes
these expressions in its statement. `Audit.lean` makes a further independent
type check with `characteristic`, `bilinear`, and the normalized averages
expanded into a literal double sum with factors `(2^k)⁻¹`.

## The proof's main organization

First, `Characteristic.lean` turns the complex expectation into the signed
cosine-product expectation. The main difficulty is that this product can be
negative outside its central cell. Its positive reference expectation also
becomes small as the dimension grows, so an absolute small-probability error
would be insufficient. Both Gaussian comparison and final cell comparison
retain errors relative to their actual positive normalizers.

The proof has two analytic chains. The first obtains an all-field spin
covariance bound. The second uses that bound to control the genuine joint
spin–continuous reference law, then sums the unwanted periodic cells. The
final numerical substitution combines these with the positive reference
normalizer lower bound.

## Convex support and the infinite lattice estimate

`ConvexSupport`, `ConvexSupportMeasure`, and `ConvexSupportMatrix` prove the
convex-set support estimate used in A.22, including the actual matrix
whitening transformation. Gaussian translation, Jensen's inequality,
measurability, and the supporting maximizer are proved for the specified
measure and set.

`GaussianTail`, `PaddedDecoder`, `PaddedDecoderGaussian`, and `LatticeEnergy`
provide the decoder and lattice estimate of A.23–A.25. The lattice is the
full integer lattice. There is no finite search radius, bounded number of
noncentral cells, or independence assumption on the projected coordinates.
Zero coordinate variances are included in the Gaussian decoder argument.

For A.25, the formalization uses Gaussian change of measure and Jensen's
inequality directly. This is the variational form of the paper's entropy
argument: the actual expected logarithmic decoder loss bounds the integral
of the actual decoder likelihood, and the likelihoods sum to one over the
full integer lattice. The projected coordinates use one common latent
Gaussian observation throughout. This adaptation proves the same cell
energy bound and error constants while avoiding a separate entropy API.

The support estimate and lattice bound are used twice: for the Gaussian
envelope comparison and for the final joint reference comparison.

## Actual Gaussian envelope comparison: A.26–A.28

`GaussianCovarianceBasic`, `GaussianCovarianceDensity`, and
`GaussianCovarianceTranslation` construct the actual centered Gaussian law
with its prescribed covariance. The singular positive-semidefinite case is
included where applicable; density and inverse formulas explicitly require
positive definiteness. The determinant normalizing factor is retained.

`CosineEnvelope` constructs a global C² even extension of `-log cos` by
integrating a clamped curvature. It equals `-log cos` on the inner interval
and has proved lower and upper curvature bounds. `GaussianEnvelopeLaw`,
`GaussianEnvelopeEuclidean`, and `GaussianEnvelopeBox` construct its actual
normalized Gibbs laws and their closed-box restriction.

The periodic-cell modules translate each cell back to the central box,
apply the convex support bound, and sum the complete countable family of
cells. `GaussianEnvelopePointwise` compares the actual signed cosine product
with the envelope pointwise. `GaussianEnvelopeTail` bounds the inner-box
exceptional event by the actual MGF and a coordinate union bound.

`GaussianRankOne` proves the exact rank-one covariance change used for the
weighted periodic second moment, including its inverse, determinant factor,
diagonal bound, and change-of-measure identities. `GaussianSquareMGF` uses
an auxiliary real Gaussian to turn a linear MGF bound into the required
quadratic exponential estimate. This also provides the comparison of the
central normalizers before and after the rank-one covariance change.

`GaussianEnvelopeRelative` combines these statements while retaining the
actual envelope normalizer in every error. Its bad-box second moment is
bounded by Cauchy–Schwarz with the fourth moment and the actual exceptional
probability. The signed Gaussian partition is identified with a strictly
positive finite spin partition before any division is used.

`GaussianFourierMoments`, `GaussianFourierProduct`,
`GaussianFourierQuadratic`, and `GaussianSpinFourier` prove the exact
Gaussian Fourier and second-moment identities that transfer this comparison
to the finite spin law. `CramerRaoCore` derives the needed score identities
from mathlib's global integration-by-parts theorem, with Gaussian domination
proving its integrability hypotheses. `EnvelopeCramerRao` specializes this
to the actual envelope potential. `GaussianResolvent` proves the exact
matrix inverse identity in the final covariance transfer.

`GaussianCovariance.zero_field_covariance_bound`, in
`GaussianEnvelopeComparison.lean`, is the resulting
A.28 estimate. Its hypotheses concern positive definiteness, the diagonal
upper bound, and explicit numerical cutoffs. It has no assumed MGF,
covariance certificate, integration-by-parts identity, or relative-error
estimate.

## From zero field to every field: A.29–A.31

`SpinCovarianceNumerics` proves the dimension-uniform error estimates and
scalar absorption inequalities. `SpinCovarianceSpectral` applies the actual
spectral decomposition to the inverse comparison. Adding a constant to the
interaction diagonal leaves the normalized spin law unchanged, because
each spin coordinate has square one; this identity is proved explicitly.

`SpinCovarianceConditional` carries out the exact two-copy disagreement-mask
conditioning. `PrincipalInverse` proves the inverse comparison averaged over
the random principal masks. `SpinCovarianceAllField` combines these finite
probability calculations with the zero-field bound on each principal mask.
The empty mask is handled separately, and each nonempty mask receives its
own valid dimension-dependent logarithmic cutoff.

The final theorem
`SpinCovariance.all_field_covariance_small_diagonal` applies to the literal
Gibbs law at every real field. Its assumptions are only the stated matrix
positivity and small-diagonal condition. This is the result used by A.33.

## Positive cosine reference and the joint law: A.32–A.33

`CosineReference` defines the scalar prior by its actual Lebesgue density
and positive normalizer. `CosineReferenceBounds` proves the majorant and
logarithmic error estimates. It uses a direct convolution and symmetrized
cosine argument in place of the paper's scalar differential-equation
argument. The exact reference function and the exact error constant are
preserved.

`JointReference` constructs the actual measure on the product of the finite
spin space and Euclidean auxiliary space. Its density, probability
normalization, finite marginal, exponential integrability, and symmetry are
proved. `JointReferenceTilt` proves the formulas for every actual normalized
exponential tilt of this measure.

`FiniteExponential` differentiates the genuine finite partition function.
`JointMarginalDifferential` and `JointMarginalPotential` identify the
conditional spin law and compute the actual marginal Hessian and the
gradient of the conditional linear mean. The Hessian is the prior curvature
minus the covariance contribution from summing over the spins.

`JointPrecisionAlgebra` proves positivity and the needed block-inverse
identities for the paper's precision matrix. In the total-variance step,
the **entire conditional variance plus inverse-Hessian energy expression**
is compared as one expression, using its variational formula. Separate
occurrences of the conditional covariance are not replaced independently.

`FiniteContinuousMixture` proves exact disintegration and total variance for
the literal finite/Lebesgue weights. `JointMarginalBounds` and
`JointMarginalIntegrability` provide explicit Gaussian majorants for the
mass and first and second moments. `JointCovarianceSmooth` then applies the
actual pointwise-Hessian Brascamp–Lieb theorem.

For the singular cosine-prior boundary, the formalization uses concrete
global C² extensions of the prior potential instead of increasing inner
boxes. `ScalarExtension`, `BrascampLieb/CosineExtension`, and
`BrascampLieb/CosineApproximation` prove the required curvature bounds and
pointwise density convergence, including convergence to zero at both
endpoints. `JointPriorApproximation` proves dominated convergence of the
actual mass, first moment, and second moment to a positive common factor
times the original tilted density. The common factor is identified and
cancels after normalization. Thus the approximation changes neither the
limiting law nor the set of allowed fields.

`JointReference.actual_joint_tilted_variance` proves the joint variance
bound under every tilt. `TiltedMGF` integrates the actual tilted variance
bound, and `JointReference.actual_joint_mgf` gives the required MGF of the
original mean-zero joint law. The all-field spin premise in these reusable
lemmas is discharged by the unconditional spin theorem in the final
assembly.

## Final cell comparison and exact constants

`WeightedTail` proves (72) for the actual reference-weighted spin sums.
`JointCellIdentity` proves the exact translated-cell identity (73), including
its normalizer. `CellEnergyComparison` proves the relative convex-support
and lattice comparisons (74)–(75). `JointComparison` assembles (76) from the
actual MGF; it retains the factor of the positive reference normalizer in
both error terms.

`ScaledMatrix` proves the exact row and column squared norms of `B = θS`
from the entrywise sign assumption. Positive semidefiniteness is used for
the derived Gram matrix `BBᵀ`, which holds for every such `B`; it is not an
assumption on `S`. `Parameters` verifies all cutoffs and the final lower
bound of `1/4` on the comparison bracket. `ConcreteReduction` proves the
positive normalizer lower bound (77).

`JointFinalReduction` performs these substitutions.
`scaled_spin_covariance_bound` in `UniformPositivity.lean` supplies the actual
all-field spin theorem, and `concreteRelativeComparison` closes the
previously conditional relative-comparison proposition. The public
`theorem_A_2` then follows with the exact angle and lower bound above.

## Brascamp–Lieb source and trust boundary

The project vendors the minimal local source closure of the genuine
Brascamp–Lieb theorem from Djalil Chafai's MIT-licensed `ginibre-poincare`
project, pinned at commit
`be028188dd8758cd9a30db1a462eaed9140856d4`. The license and source manifest
are in `third_party/`. The manifest records the exact upstream source
hashes and the import-only adaptations needed to use the minimal closure.

The exported Brascamp–Lieb theorem concerns the actual C² potential, its
actual Hessian, the actual Gibbs measure, and actual derivatives and
integrability of the observable. It does not assume a solution certificate
for an elliptic equation or the target variance inequality. The local
wrappers derive weighted, normalized, and closed-box forms from this
theorem. The box form uses genuine C² convex penalties and dominated
convergence.

All local theorem declarations in the proof namespaces, including the
Brascamp–Lieb wrappers and private helpers, are included in the final
transitive axiom audit. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The audit also
requires the public unrestricted exports to be theorem declarations and
typechecks the independently expanded statement. The successful release
verification includes both `lake build TheoremA2` and
`lake env lean -DautoImplicit=false Audit.lean` on the final source tree.
