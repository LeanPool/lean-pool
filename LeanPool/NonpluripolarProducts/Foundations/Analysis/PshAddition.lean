/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic

/-!
# Addition of extended-real plurisubharmonic functions

Finite upper bounds turn addition into addition of nonnegative deficits. The
argument therefore retains negative-infinite values and never subtracts
infinite integrals. Compact discs supply the separate finite upper bounds.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Deficits below finite majorants add. -/
theorem ereal_coe_add_sub_add {C D : ℝ} {a b : EReal} (ha : a ≤ (C : EReal))
    (hb : b ≤ (D : EReal)) :
    ((C + D : ℝ) : EReal) - (a + b) = ((C : EReal) - a) + ((D : EReal) - b) := by
  have ha' : a ≠ ⊤ := ne_of_lt (ha.trans_lt (EReal.coe_lt_top C))
  have hb' : b ≠ ⊤ := ne_of_lt (hb.trans_lt (EReal.coe_lt_top D))
  rw [EReal.coe_add, sub_eq_add_neg, EReal.neg_add (Or.inr hb') (Or.inl ha')]
  simp only [sub_eq_add_neg]
  ac_rfl

/-- Deficits below separate finite upper bounds add, including at poles. -/
theorem finiteDeficit_add (C D : ℝ) {z w : EReal}
    (hz : z ≤ (C : EReal)) (hw : w ≤ (D : EReal)) :
    (((C + D : ℝ) : EReal) - (z + w)).toENNReal =
      ((C : EReal) - z).toENNReal + ((D : EReal) - w).toENNReal := by
  have hzN : 0 ≤ (C : EReal) - z :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C))
      (Or.inl (EReal.coe_ne_bot C))).mpr hz
  have hwN : 0 ≤ (D : EReal) - w :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top D))
      (Or.inl (EReal.coe_ne_bot D))).mpr hw
  rw [ereal_coe_add_sub_add hz hw, EReal.toENNReal_add hzN hwN]

/-- The angular deficit of a sum is the sum of its measurable deficits. -/
theorem DiscPshOn.circleDeficit_add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) (C D : ℝ)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal))
    (hW : ∀ y ∈ affineClosedDisc x v r, w y ≤ (D : EReal)) :
    circleDeficit (fun y => u y + w y) x v r (C + D) =
      circleDeficit u x v r C + circleDeficit w x v r D := by
  unfold circleDeficit
  simp_rw [finiteDeficit_add C D
    (hC _ (circle_mem_affineClosedDisc x v hr _))
    (hW _ (circle_mem_affineClosedDisc x v hr _))]
  exact lintegral_add_left (hu.measurable_circle_deficit x v hr hD C) _

/-- The sum of two disc-PSH functions is disc-PSH, with no finiteness assumption
on their negative parts and with identically negative infinity permitted. -/
theorem DiscPshOn.add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    DiscPshOn (fun y => u y + w y) U := by
  refine ⟨fun y hy => EReal.add_ne_top (hu.ne_top y hy) (hw.ne_top y hy), ?_, ?_⟩
  · intro y hy
    exact UpperSemicontinuousWithinAt.add'
      (hu.upperSemicontinuousOn y hy) (hw.upperSemicontinuousOn y hy)
      (EReal.continuousAt_add (Or.inl (hu.ne_top y hy)) (Or.inr (hw.ne_top y hy)))
  · intro x v r hr hD C hC
    obtain ⟨A, hA⟩ := hu.exists_disc_upper_bound x v hr.le hD
    obtain ⟨B, hB⟩ := hw.exists_disc_upper_bound x v hr.le hD
    let D : ℝ := Max.max A (C - B)
    have hAD : A ≤ D := le_max_left _ _
    have hCD : C ≤ D + B := by
      have : C - B ≤ D := le_max_right _ _
      linarith
    have hDu : ∀ y ∈ affineClosedDisc x v r, u y ≤ (D : EReal) :=
      fun y hy => (hA y hy).trans (EReal.coe_le_coe_iff.mpr hAD)
    have hsum : circleDeficit (fun y => u y + w y) x v r (D + B) ≤
        ENNReal.ofReal (2 * Real.pi) * (((D + B : ℝ) : EReal) - (u x + w x)).toENNReal := by
      rw [hu.circleDeficit_add x v hr.le hD D B hDu hB,
        finiteDeficit_add D B (hDu x (center_mem_affineClosedDisc x v hr.le))
          (hB x (center_mem_affineClosedDisc x v hr.le)), mul_add]
      exact add_le_add (hu.submean x v r hr hD D hDu) (hw.submean x v r hr hD B hB)
    apply (discSubmean_add_bound_iff x v hr.le C (D + B - C)
      (sub_nonneg.mpr hCD) hC).mp
    have hboundeq : C + (D + B - C) = D + B := by ring
    simpa only [hboundeq] using hsum

/-- Addition preserves the genuine ambient PSH germ at a point. -/
theorem PlurisubharmonicAt.add {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (hw : PlurisubharmonicAt w x) :
    PlurisubharmonicAt (fun y => u y + w y) x := by
  obtain ⟨U, hU, hxU, hu⟩ := hu
  obtain ⟨V, hV, hxV, hw⟩ := hw
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    (hu.mono inter_subset_left).add (hw.mono inter_subset_right)⟩

/-- Addition preserves PSH germs on any set. -/
theorem PlurisubharmonicOn.add {u w : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w U) :
    PlurisubharmonicOn (fun y => u y + w y) U :=
  fun x hx => (hu x hx).add (hw x hx)

end SGPT.Foundations.Analysis
