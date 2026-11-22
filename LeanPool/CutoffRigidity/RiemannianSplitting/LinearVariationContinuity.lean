/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.LinearVariationBounds
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-! # Initial-parameter continuity of actual linear variational equations
Joint continuity of the genuine operator coefficients on a compact parameter
and time set supplies uniform coefficient control. The actual ODE stability
estimate then proves continuity of the genuine variational solutions.
-/

@[expose] public section
open Set Metric
open scoped Topology NNReal

namespace CutoffRigidity

variable {P E : Type*} [MetricSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual identity-initialized linear ODE solutions depend continuously on the
parameter of their actual coefficients, without a solution-dependence premise. -/
theorem continuousOn_linearVariation_parameter
    {S : Set P} (hS : IsCompact S) {T : ℝ} (hT : 0 ≤ T)
    {A J : P → ℝ → E →L[ℝ] E}
    (hA : ContinuousOn (fun p : P × ℝ ↦ A p.1 p.2) (S ×ˢ Icc 0 T))
    (hJzero : ∀ p ∈ S, J p 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ p ∈ S, ∀ s ∈ Icc 0 T,
      HasDerivAt (J p) ((A p s).comp (J p s)) s)
    {M : ℝ≥0} (hM : ∀ p ∈ S, ∀ s ∈ Icc 0 T, ‖A p s‖ ≤ M) :
    ContinuousOn (fun p ↦ J p T) S := by
  have hUC := (hS.prod isCompact_Icc).uniformContinuousOn_of_continuous hA
  let N := Real.exp ((M : ℝ) * T)
  let B := max 1 |gronwallBound 0 (M : ℝ) 1 T|
  have hN : 0 < N := Real.exp_pos _
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hJN (p : P) (hp : p ∈ S) (s : ℝ) (hs : s ∈ Icc 0 T) : ‖J p s‖ ≤ N := by
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
    have hh := norm_linearVariation_le_exp hs.1 (hJzero p hp)
      (fun u hu ↦ hJD p hp u (hsub hu)) (fun u hu ↦ hM p hp u (hsub hu))
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 M.coe_nonneg))
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let η := ε / (2 * N * B)
  have hη : 0 < η := div_pos hε (mul_pos (mul_pos (by norm_num) hN) hB)
  obtain ⟨δ, hδ, hδA⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  refine ⟨δ, hδ, ?_⟩
  intro q hq hdist
  have hdiff (s : ℝ) (hs : s ∈ Icc 0 T) : ‖A q s - A p s‖ ≤ η := by
    have hpair : dist (q, s) (p, s) < δ := by simpa using hdist
    have hh := hδA (q, s) ⟨hq, hs⟩ (p, s) ⟨hp, hs⟩ hpair
    exact (by simpa only [dist_eq_norm] using hh : ‖A q s - A p s‖ < η).le
  have hvar := norm_sub_linearVariation_le hT (hJzero q hq) (hJzero p hp)
    (hJD q hq) (hJD p hp) (hM q hq) hη.le hdiff (hJN p hp)
  rw [dist_eq_norm]
  have hBB : gronwallBound 0 (M : ℝ) 1 T ≤ B := (le_abs_self _).trans (le_max_right _ _)
  have hηNB : η * N * B = ε / 2 := by dsimp [η]; field_simp
  calc
    _ ≤ η * N * gronwallBound 0 (M : ℝ) 1 T := hvar
    _ ≤ η * N * B := mul_le_mul_of_nonneg_left hBB (mul_nonneg hη.le hN.le)
    _ = ε / 2 := hηNB
    _ < ε := half_lt_self hε

end CutoffRigidity
