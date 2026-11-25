/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscRegularization
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Functoriality of upper-semicontinuous regularization

The upper-semicontinuous regularization is local.  Consequently it commutes
with homeomorphisms, open embeddings and the inverse branches of manifold
charts.  It also commutes with addition of a finite continuous real-valued
function.  These statements retain both infinities of `EReal`.
-/

@[expose] public section

open Set Filter Topology
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A local upper-semicontinuous majorant controls the regularization at the
base point; no global comparison away from a neighborhood is required. -/
theorem uscRegularization_le_of_eventually_le {f g : X → EReal} {x : X}
    (hg : UpperSemicontinuousAt g x)
    (hfg : ∀ᶠ y in 𝓝 x, f y ≤ g y) :
    uscRegularization f x ≤ g x := by
  apply le_of_forall_gt
  intro a hga
  obtain ⟨b, hgb, hba⟩ := exists_between hga
  have hsub : {y | g y < b} ∈ 𝓝 x := hg b hgb
  have hU : {y | f y ≤ g y} ∩ {y | g y < b} ∈ 𝓝 x :=
    inter_mem hfg hsub
  exact ((uscRegularization_le_localSup f hU).trans
    (iSup_le fun y ↦ iSup_le fun hy ↦ (hy.1.trans_lt hy.2).le)).trans_lt hba

/-- Upper-semicontinuous regularization commutes pointwise with a
homeomorphism. -/
theorem uscRegularization_comp_homeomorph_apply (f : Y → EReal) (e : X ≃ₜ Y)
    (x : X) :
    uscRegularization (f ∘ e) x = uscRegularization f (e x) := by
  apply le_antisymm
  · apply uscRegularization_le_of_eventually_le
      ((upperSemicontinuous_uscRegularization f (e x)).comp
        e.continuous.continuousAt)
    exact Eventually.of_forall fun y ↦ le_uscRegularization f (e y)
  · have h := uscRegularization_le_of_eventually_le
      (f := f)
      (g := fun y ↦ uscRegularization (f ∘ e) (e.symm y))
      (x := e x)
      ((upperSemicontinuous_uscRegularization (f ∘ e) (e.symm (e x))).comp
        e.symm.continuous.continuousAt)
      (Eventually.of_forall fun y ↦ by
        simpa [Function.comp_def] using
          (le_uscRegularization (f ∘ e) (e.symm y)))
    simpa using h

/-- Function-level form of homeomorphism covariance. -/
theorem uscRegularization_comp_homeomorph (f : Y → EReal) (e : X ≃ₜ Y) :
    uscRegularization (f ∘ e) = uscRegularization f ∘ e := by
  funext x
  exact uscRegularization_comp_homeomorph_apply f e x

/-- The same covariance holds at a point in the source of an open partial
homeomorphism.  Values of its arbitrary extension outside the source do not
affect either side. -/
theorem uscRegularization_comp_openPartialHomeomorph_apply
    (f : Y → EReal) (e : OpenPartialHomeomorph X Y) {x : X}
    (hx : x ∈ e.source) :
    uscRegularization (f ∘ e) x = uscRegularization f (e x) := by
  apply le_antisymm
  · apply uscRegularization_le_of_eventually_le
      ((upperSemicontinuous_uscRegularization f (e x)).comp
        (e.continuousAt hx))
    exact Eventually.of_forall fun y ↦ le_uscRegularization f (e y)
  · have htarget : e.target ∈ 𝓝 (e x) :=
      e.open_target.mem_nhds (e.map_source hx)
    have hle : ∀ᶠ y in 𝓝 (e x),
        f y ≤ uscRegularization (f ∘ e) (e.symm y) := by
      filter_upwards [htarget] with y hy
      simpa [Function.comp_def, e.right_inv hy] using
        (le_uscRegularization (f ∘ e) (e.symm y))
    have h := uscRegularization_le_of_eventually_le
      (f := f)
      (g := fun y ↦ uscRegularization (f ∘ e) (e.symm y))
      (x := e x)
      ((upperSemicontinuous_uscRegularization (f ∘ e) (e.symm (e x))).comp
        (e.continuousAt_symm (e.map_source hx)))
      hle
    simpa [e.left_inv hx] using h

/-- Pullback along an open embedding commutes with regularization. -/
theorem uscRegularization_comp_isOpenEmbedding_apply
    (f : Y → EReal) {j : X → Y} (hj : IsOpenEmbedding j) (x : X) :
    uscRegularization (f ∘ j) x = uscRegularization f (j x) := by
  let _ : Nonempty X := ⟨x⟩
  let e : OpenPartialHomeomorph X Y := hj.toOpenPartialHomeomorph j
  have hx : x ∈ e.source := by simp [e]
  simpa [e] using uscRegularization_comp_openPartialHomeomorph_apply f e hx

end Topological

section ContinuousTranslation

variable {X : Type*} [TopologicalSpace X]

/-- Adding a finite continuous real-valued function preserves upper
semicontinuity of an extended-real-valued function. -/
theorem upperSemicontinuous_add_coe_continuous
    {f : X → EReal} {c : X → ℝ}
    (hf : UpperSemicontinuous f) (hc : Continuous c) :
    UpperSemicontinuous (fun x ↦ f x + (c x : EReal)) :=
  hf.add' (continuous_coe_real_ereal.comp hc).upperSemicontinuous fun x ↦
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (c x)))
      (Or.inr (EReal.coe_ne_top (c x)))

/-- Pointwise covariance under a finite real translation requires continuity
of the translating function only at the point being regularized. -/
theorem uscRegularization_add_coe_continuousAt_apply
    (f : X → EReal) {c : X → ℝ} {x : X} (hc : ContinuousAt c x) :
    uscRegularization (fun y ↦ f y + (c y : EReal)) x =
      uscRegularization f x + (c x : EReal) := by
  have hcoe : ContinuousAt (fun y ↦ (c y : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp hc
  have hnegcoe : ContinuousAt (fun y ↦ (((-c) y : ℝ) : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp hc.neg
  have hnegpos (y : X) : (((-c) y : ℝ) : EReal) + (c y : EReal) = 0 := by
    rw [← EReal.coe_add]
    norm_num
  have hposneg (y : X) : (c y : EReal) + (((-c) y : ℝ) : EReal) = 0 := by
    rw [← EReal.coe_add]
    norm_num
  have husc : UpperSemicontinuousAt (uscRegularization f) x :=
    upperSemicontinuous_uscRegularization f x
  have huscSum : UpperSemicontinuousAt
      (uscRegularization (fun y ↦ f y + (c y : EReal))) x :=
    upperSemicontinuous_uscRegularization (fun y ↦ f y + (c y : EReal)) x
  apply le_antisymm
  · apply uscRegularization_le_of_eventually_le
      (husc.add'
        hcoe.upperSemicontinuousAt
        (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (c x)))
          (Or.inr (EReal.coe_ne_top (c x)))))
    exact Eventually.of_forall fun y ↦ by
      gcongr
      exact le_uscRegularization f y
  · have h : uscRegularization f x ≤
        uscRegularization (fun y ↦ f y + (c y : EReal)) x +
          (((-c) x : ℝ) : EReal) := by
      apply uscRegularization_le_of_eventually_le
        (huscSum.add'
            hnegcoe.upperSemicontinuousAt
            (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot ((-c) x)))
              (Or.inr (EReal.coe_ne_top ((-c) x)))))
      exact Eventually.of_forall fun y ↦ by
        rw [← (EReal.addLECancellable_coe (c y)).add_le_add_iff_right]
        rw [add_assoc, hnegpos y, add_zero]
        exact le_uscRegularization (fun z ↦ f z + (c z : EReal)) y
    rw [← (EReal.addLECancellable_coe ((-c) x)).add_le_add_iff_right]
    rw [add_assoc, hposneg x, add_zero]
    exact h

/-- Upper-semicontinuous regularization commutes with addition of a finite
continuous real-valued function. -/
theorem uscRegularization_add_coe_continuous
    (f : X → EReal) {c : X → ℝ} (hc : Continuous c) :
    uscRegularization (fun x ↦ f x + (c x : EReal)) =
      fun x ↦ uscRegularization f x + (c x : EReal) := by
  funext x
  exact uscRegularization_add_coe_continuousAt_apply f hc.continuousAt

end ContinuousTranslation

end

end SGPT.Foundations.Analysis.FirstPass
