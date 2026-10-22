import TheoremA2.CosineEnvelope
import TheoremA2.Parameters
import TheoremA2.SpinCovarianceAllField

/-!
# Exact quantitative errors for the zero-field precision bound

These are the literal errors in Lemmas A.27–A.28 and Proposition A.29.
No estimate is built into their definitions.
-/

namespace TheoremA2.SpinCovariance

noncomputable section

/-- The two-sided Gaussian coordinate union bound used in A.27. -/
def zeroFieldDelta (d : ℕ) (q : ℝ) : ℝ :=
  2 * (d : ℝ) * Real.exp (-(1 : ℝ) / (32 * q))

/-- The complete relative normalizer error. -/
def zeroFieldAlpha (d : ℕ) (q : ℝ) : ℝ :=
  zeroFieldDelta d q + latticeError d q

/-- The complete relative second-moment error in equation (50). -/
def zeroFieldZeta (d : ℕ) (q : ℝ) : ℝ :=
  (zeroFieldAlpha d q + Real.sqrt (5 * zeroFieldDelta d q) +
    4 * Real.sqrt 2 * latticeError d (2 * q)) / (1 - zeroFieldAlpha d q)

end
end TheoremA2.SpinCovariance
