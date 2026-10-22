import TheoremA2
import Lean.Util.CollectAxioms

/-!
# Final statement and transitive axiom audit

This file is a separate compilation gate. It checks that the unrestricted
public declarations are theorems, checks the transitive axioms of every
theorem in the three local proof namespaces (including private helpers), and checks the theorem once
more with the finite expectation expanded into its literal double sum.

Only Lean's standard classical foundational axioms are permitted. In
particular, `sorryAx` and computation-oracle axioms are not permitted.
-/

open Lean Elab Command
open scoped BigOperators

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let namespaces : Array Name := #[`TheoremA2, `BrascampLieb, `GinibrePoincare]
  let finalTheorems : Array Name := #[``TheoremA2.theorem_A_2,
    ``TheoremA2.theorem_A_2_explicit, ``TheoremA2.uniformPositivity]
  for name in finalTheorems do
    unless Lean.getOriginalConstKind? env name == some .thm do
      throwError "Required unrestricted theorem is missing: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if namespaces.any (fun ns => ns.isPrefixOf (Lean.privateToUserName name)) then
      match info with
      | .axiomInfo _ => throwError "Local proof source declares an axiom: {name}"
      | _ => pure ()
      if Lean.getOriginalConstKind? env name == some .thm then
        let dependencies ← Lean.collectAxioms name
        for dependency in dependencies do
          unless permitted.contains dependency do
            throwError "Unpermitted transitive axiom in {name}: {dependency}"
        count := count + 1
  logInfo m!"Axiom audit passed for {count} local theorem declarations."
  logInfo "Allowed axioms: propext, Classical.choice, Quot.sound."
  logInfo "The unrestricted public declarations are kernel-checked theorems."

/-- Independent statement check with the expectation and signs expanded.
There is no dimension cutoff or condition on the matrix besides its entries. -/
example {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : ∀ i j, S i j = 1 ∨ S i j = -1) :
    let a : ℝ := 1 / 10000000
    let t := a / (Real.sqrt (k : ℝ) * Real.log (4 * (k : ℝ)))
    let b := (1 / 4 : ℝ) *
      Real.exp (-(64 * a ^ 2 * (k : ℝ)) / Real.log (4 * (k : ℝ)))
    let phi : ℂ := ((2 : ℂ) ^ k)⁻¹ *
      ∑ σ : Fin k → Bool, ((2 : ℂ) ^ k)⁻¹ *
        ∑ τ : Fin k → Bool,
          Complex.exp ((((t * ∑ i, ∑ j,
            (if σ i then (1 : ℝ) else -1) * S i j *
              (if τ j then (1 : ℝ) else -1)) : ℝ) : ℂ) * Complex.I)
    phi.im = 0 ∧ b ≤ phi.re ∧ 0 < b := by
  simpa only [TheoremA2.characteristic, TheoremA2.complexAverage,
    TheoremA2.bilinear, TheoremA2.sign, TheoremA2.card_spin,
    Nat.cast_pow, Nat.cast_ofNat] using TheoremA2.theorem_A_2_explicit hk S hS

#print TheoremA2.A2Conclusion
#print TheoremA2.UniformPositivityStatement
#check TheoremA2.theorem_A_2
#check TheoremA2.theorem_A_2_explicit
#print axioms TheoremA2.theorem_A_2
#print axioms TheoremA2.theorem_A_2_explicit
#print axioms TheoremA2.uniformPositivity
#print axioms TheoremA2.concreteRelativeComparison
#print axioms TheoremA2.JointReference.actual_joint_tilted_variance
#print axioms TheoremA2.JointReference.actual_joint_mgf
#print axioms TheoremA2.SpinCovariance.all_field_covariance_small_diagonal
#print axioms GinibrePoincare.correspondenceBrascampLieb_variance
