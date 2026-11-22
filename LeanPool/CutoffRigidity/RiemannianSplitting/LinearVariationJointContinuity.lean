/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.LinearVariationContinuity
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Joint parameter-time continuity of actual linear variations -/

@[expose] public section
open Set
open scoped Topology NNReal

namespace CutoffRigidity
variable {P E : Type*} [MetricSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual linear ODE yields a uniform time-Lipschitz estimate. Together
with the proved coefficient dependence, it gives joint parameter-time continuity. -/
theorem continuousOn_linearVariation_joint
    {S : Set P} (hS : IsCompact S) {T : ℝ} (_hT : 0 ≤ T)
    {A J : P → ℝ → E →L[ℝ] E}
    (hA : ContinuousOn (fun p : P × ℝ ↦ A p.1 p.2) (S ×ˢ Icc 0 T))
    (hJzero : ∀ p ∈ S, J p 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ p ∈ S, ∀ s ∈ Icc 0 T,
      HasDerivAt (J p) ((A p s).comp (J p s)) s)
    {M : ℝ≥0} (hM : ∀ p ∈ S, ∀ s ∈ Icc 0 T, ‖A p s‖ ≤ M) :
    ContinuousOn (fun p : P × ℝ ↦ J p.1 p.2) (S ×ˢ Icc 0 T) := by
  let N : ℝ≥0 := ⟨Real.exp ((M : ℝ) * T), (Real.exp_pos _).le⟩
  have hbound (p : P) (hp : p ∈ S) (s : ℝ) (hs : s ∈ Icc 0 T) : ‖J p s‖ ≤ N := by
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
    have hj := norm_linearVariation_le_exp hs.1 (hJzero p hp)
      (fun u hu ↦ hJD p hp u (hsub hu)) (fun u hu ↦ hM p hp u (hsub hu))
    exact hj.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 M.coe_nonneg))
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ (M * N)
  · intro p hp
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
      (fun s hs ↦ (hJD p hp s hs).hasDerivWithinAt)
    intro s hs
    have hn : ‖(A p s).comp (J p s)‖ ≤ (M : ℝ) * (N : ℝ) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hM p hp s hs) (hbound p hp s hs) (norm_nonneg _) M.coe_nonneg)
    exact_mod_cast hn
  · intro s hs
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
    exact continuousOn_linearVariation_parameter hS hs.1
      (hA.mono (Set.prod_mono Subset.rfl hsub)) hJzero
      (fun p hp u hu ↦ hJD p hp u (hsub hu))
      (fun p hp u hu ↦ hM p hp u (hsub hu))

/-- Joint continuity also holds through time zero on a genuine symmetric
window, by reversing the actual linear ODE and gluing its two closed halves. -/
theorem continuousOn_linearVariation_joint_symmetric
    {S : Set P} (hS : IsCompact S) {T : ℝ} (hT : 0 ≤ T)
    {A J : P → ℝ → E →L[ℝ] E}
    (hA : ContinuousOn (fun p : P × ℝ ↦ A p.1 p.2) (S ×ˢ Icc (-T) T))
    (hJzero : ∀ p ∈ S, J p 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ p ∈ S, ∀ s ∈ Icc (-T) T,
      HasDerivAt (J p) ((A p s).comp (J p s)) s)
    {M : ℝ≥0} (hM : ∀ p ∈ S, ∀ s ∈ Icc (-T) T, ‖A p s‖ ≤ M) :
    ContinuousOn (fun p : P × ℝ ↦ J p.1 p.2) (S ×ˢ Icc (-T) T) := by
  have hpos : Icc 0 T ⊆ Icc (-T) T := Icc_subset_Icc (by linarith) le_rfl
  have hp := continuousOn_linearVariation_joint hS hT
    (hA.mono (Set.prod_mono Subset.rfl hpos)) hJzero
    (fun p hp s hs ↦ hJD p hp s (hpos hs))
    (fun p hp s hs ↦ hM p hp s (hpos hs))
  have href (s : ℝ) (hs : s ∈ Icc 0 T) : -s ∈ Icc (-T) T :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hAr : ContinuousOn (fun p : P × ℝ ↦ -A p.1 (-p.2)) (S ×ˢ Icc 0 T) := by
    apply (hA.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn ?_).neg
    intro p hp
    exact ⟨hp.1, href p.2 hp.2⟩
  have hDr : ∀ p ∈ S, ∀ s ∈ Icc 0 T,
      HasDerivAt (fun t ↦ J p (-t)) ((-A p (-s)).comp (J p (-s))) s := by
    intro p hp s hs
    simpa only [Function.comp_def, neg_one_smul, ContinuousLinearMap.neg_comp] using
      (hJD p hp (-s) (href s hs)).scomp s (hasDerivAt_neg s)
  have hn := continuousOn_linearVariation_joint hS hT hAr
    (by simpa only [neg_zero] using hJzero) hDr
    (M := M) (fun p hp s hs ↦ by simpa only [norm_neg] using hM p hp (-s) (href s hs))
  have hn' : ContinuousOn (fun p : P × ℝ ↦ J p.1 p.2) (S ×ˢ Icc (-T) 0) := by
    have hh := hn.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
      (fun p (hp : p ∈ S ×ˢ Icc (-T) 0) ↦
        ⟨hp.1, show -p.2 ∈ Icc 0 T from ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩)
    simpa only [Function.comp_def, Pi.neg_apply, neg_neg] using hh
  apply (hn'.union_of_isClosed hp (hS.isClosed.prod isClosed_Icc)
    (hS.isClosed.prod isClosed_Icc)).mono
  intro p hp
  by_cases h : p.2 ≤ 0
  · exact Or.inl ⟨hp.1, hp.2.1, h⟩
  · exact Or.inr ⟨hp.1, (le_of_not_ge h), hp.2.2⟩

end CutoffRigidity
