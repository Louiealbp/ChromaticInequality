module
public import Mathlib.LinearAlgebra.Matrix.PosDef
@[expose] public section
open scoped Matrix BigOperators
namespace GinibrePoincare
noncomputable section

/-- The pointwise Hessian-inverse Cauchy–Schwarz estimate used in the genuine
Brascamp–Lieb inequality. Positive definiteness is a concrete matrix property. -/
theorem correspondenceBrascampLieb_inverse_cauchy_schwarz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a b : ι→ℝ) :
    (a ⬝ᵥ b)^2≤(a ⬝ᵥ H⁻¹*ᵥa)*(b ⬝ᵥ H*ᵥb) := by
  have hc := hH.star_dotProduct_mulVec_mul_le (H⁻¹*ᵥa) b
  have hinv : H*(H⁻¹)=1 := Matrix.mul_nonsing_inv H (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have he : H*ᵥ(H⁻¹*ᵥa)=a := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hs : (H⁻¹*ᵥa) ⬝ᵥ (H*ᵥb)=a ⬝ᵥ b := by
    have hsym : H.transpose=H := by exact hH.isHermitian.isSymm
    rw [Matrix.dotProduct_mulVec]
    have hv : (H⁻¹ *ᵥ a) ᵥ* H = a := by
      calc
        (H⁻¹ *ᵥ a) ᵥ* H = (H⁻¹ *ᵥ a) ᵥ* H.transpose := by rw [hsym]
        _ = H *ᵥ (H⁻¹ *ᵥ a) := Matrix.vecMul_transpose _ _
        _ = a := he
    rw [hv]
  simpa only [star_trivial, he, hs, pow_two, dotProduct_comm] using hc

#print axioms correspondenceBrascampLieb_inverse_cauchy_schwarz
end
end GinibrePoincare
