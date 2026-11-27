/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.MaximalBellClosure
public import LeanPool.VacuumBellSeparation.Bell.NormalStateMarginals

/-!
An actual positive dominated state is a component of a maximal state.
The residual is constructed in the original continuous dual. This does not
prove that the dominated normal states are norm dense for a faithful state.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Dominated state residual given by `(1 - t)⁻¹ • (ω.1 - t • φ.1)`. -/
def dominatedStateResidual (M : VonNeumannAlgebra H) (ω φ : StateSpace M) (t : ℝ) :
    StrongDual ℂ M.toStarSubalgebra := (1 - t)⁻¹ • (ω.1 - t • φ.1)

theorem dominatedStateResidual_isState (M : VonNeumannAlgebra H)
    (ω φ : StateSpace M) {t : ℝ} (ht1 : t < 1)
    (hdom : ∀ T : M.toStarSubalgebra, 0 ≤ T → t • φ.1 T ≤ ω.1 T) :
    IsStateFunctional M (dominatedStateResidual M ω φ t) := by
  let ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ := {
    toLinearMap := (dominatedStateResidual M ω φ t).toLinearMap
    monotone' := by
      intro X Y hXY
      have hp : 0 ≤ ω.1 (Y - X) - t • φ.1 (Y - X) :=
        sub_nonneg.mpr (hdom (Y - X) (sub_nonneg.mpr hXY))
      have he : dominatedStateResidual M ω φ t Y - dominatedStateResidual M ω φ t X =
          (1 - t)⁻¹ • (ω.1 (Y - X) - t • φ.1 (Y - X)) := by
        simp only [dominatedStateResidual, smul_apply,
          sub_apply, map_sub, smul_sub]
        abel
      apply sub_nonneg.mp
      change 0 ≤ dominatedStateResidual M ω φ t Y - dominatedStateResidual M ω φ t X
      rw [he]
      exact smul_nonneg (inv_nonneg.mpr (sub_pos.mpr ht1).le) hp }
  refine ⟨ψ, ?_, fun _ => rfl⟩
  change (1 - t)⁻¹ • (ω.1 1 - t • φ.1 1) = (1 : ℂ)
  have he : ω.1 1 - t • φ.1 1 = (1 - t) • (1 : ℂ) := by
    rw [ω.2.apply_one, φ.2.apply_one, sub_smul, one_smul]
  rw [he, smul_smul, inv_mul_cancel₀ (sub_pos.mpr ht1).ne', one_smul]

theorem dominatedStateResidual_decomposition (M : VonNeumannAlgebra H)
    (ω φ : StateSpace M) {t : ℝ} (ht1 : t < 1) (T : M.toStarSubalgebra) :
    t • φ.1 T + (1 - t) • dominatedStateResidual M ω φ t T = ω.1 T := by
  change t • φ.1 T + (1 - t) • ((1 - t)⁻¹ • (ω.1 T - t • φ.1 T)) = ω.1 T
  rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr ht1).ne', one_smul]
  abel

/-- Domination means an actual inequality on every positive element of the
original joint algebra. The complementary state is proved to exist. -/
theorem jointBellCorrelation_maximal_of_dominated (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (ω φ : StateSpace (jointAlgebra A B))
    (hmax : jointBellCorrelation A B ω.1 = Real.sqrt 2)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdom : ∀ T : (jointAlgebra A B).toStarSubalgebra,
      0 ≤ T → t • φ.1 T ≤ ω.1 T) :
    jointBellCorrelation A B φ.1 = Real.sqrt 2 := by
  let ψ : StateSpace (jointAlgebra A B) :=
    ⟨dominatedStateResidual (jointAlgebra A B) ω φ t,
      dominatedStateResidual_isState _ ω φ ht1 hdom⟩
  have he : (fun T => t • φ.1 T + (1 - t) • ψ.1 T) = ω.1 := by
    funext T
    exact dominatedStateResidual_decomposition _ ω φ ht1 T
  exact (jointBellCorrelation_state_maximal_components A B hcomm φ ψ ht ht1
    (by rw [he]; exact hmax)).1

end VacuumBellSeparation.Bipartite.HC00
