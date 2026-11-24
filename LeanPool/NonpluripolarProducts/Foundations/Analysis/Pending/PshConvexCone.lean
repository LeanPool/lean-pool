/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition

/-!
# Positive scaling of plurisubharmonic functions

Together with `PshAddition`, this gives the convex cone operations on plurisubharmonic
functions. For a strictly positive scalar, the angular deficit below a scaled finite
majorant scales by the same factor. This identity holds at negative-infinite values.
The result for scalar zero follows from `plurisubharmonicAt_const`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Pointwise deficit identities in `EReal` -/

/-- Deficits below finite majorants are homogeneous under positive scaling. -/
theorem ereal_coe_mul_sub_mul {c C : ℝ} (hc : 0 < c) {a : EReal}
    (ha : a ≤ (C : EReal)) :
    ((c * C : ℝ) : EReal) - (c : EReal) * a = (c : EReal) * ((C : EReal) - a) := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos hc, EReal.coe_sub_bot, EReal.coe_sub_bot,
        EReal.coe_mul_top_of_pos hc]
  | top => exact absurd ha (by simp)
  | coe x =>
      rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]
      exact EReal.coe_eq_coe_iff.mpr (by ring)

/-! ### The angular deficit of a sum and of a positive multiple -/

theorem circleDeficit_add {u w : E → EReal} (x v : E) {r : ℝ} (hr : 0 ≤ r)
    {C D : ℝ} (hu : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal))
    (hw : ∀ y ∈ affineClosedDisc x v r, w y ≤ (D : EReal))
    (hmu : Measurable fun t : ℝ =>
      ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal) :
    circleDeficit (fun y => u y + w y) x v r (C + D) =
      circleDeficit u x v r C + circleDeficit w x v r D := by
  unfold circleDeficit
  simp_rw [finiteDeficit_add C D
    (hu _ (circle_mem_affineClosedDisc x v hr _))
    (hw _ (circle_mem_affineClosedDisc x v hr _))]
  exact lintegral_add_left hmu _

theorem circleDeficit_const_mul {u : E → EReal} (x v : E) {r : ℝ} (hr : 0 ≤ r)
    {c C : ℝ} (hc : 0 < c)
    (hu : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) :
    circleDeficit (fun y => (c : EReal) * u y) x v r (c * C) =
      ENNReal.ofReal c * circleDeficit u x v r C := by
  unfold circleDeficit
  have hpt : ∀ t : ℝ,
      (((c * C : ℝ) : EReal) - (c : EReal) * u (x + circleMap 0 r t • v)).toENNReal =
        ENNReal.ofReal c * ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal := by
    intro t
    rw [ereal_coe_mul_sub_mul hc (hu _ (circle_mem_affineClosedDisc x v hr t)),
      EReal.toENNReal_mul (EReal.coe_nonneg.mpr hc.le), EReal.real_coe_toENNReal]
  simp_rw [hpt]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The disc submean inequality for a sum follows from the addition theorem. -/
theorem DiscPshOn.hasDiscSubmeanOn_add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    HasDiscSubmeanOn (fun y => u y + w y) U :=
  (hu.add hw).submean

/-! ### Closure of the disc criterion under positive scaling -/

theorem DiscPshOn.hasDiscSubmeanOn_const_mul {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) {c : ℝ} (hc : 0 < c) :
    HasDiscSubmeanOn (fun y => (c : EReal) * u y) U := by
  intro x v r hr hD C' hC'
  obtain ⟨C, hC⟩ := hu.exists_disc_upper_bound x v hr.le hD
  set C'' : ℝ := Max.max C' (c * C) with hC''def
  set K : ℝ := C'' / c with hKdef
  have hcK : c * K = C'' := by rw [hKdef, mul_div_cancel₀ _ hc.ne']
  have hCK : C ≤ K := by
    rw [hKdef, le_div_iff₀ hc, mul_comm]
    exact le_max_right _ _
  have hKbound : ∀ y ∈ affineClosedDisc x v r, u y ≤ (K : EReal) :=
    fun y hy => (hC y hy).trans (EReal.coe_le_coe_iff.mpr hCK)
  have hx := center_mem_affineClosedDisc x v hr.le
  have key : circleDeficit (fun y => (c : EReal) * u y) x v r C'' ≤
      ENNReal.ofReal (2 * Real.pi) * ((C'' : EReal) - (c : EReal) * u x).toENNReal := by
    rw [← hcK, circleDeficit_const_mul x v hr.le hc hKbound,
      ereal_coe_mul_sub_mul hc (hKbound x hx),
      EReal.toENNReal_mul (EReal.coe_nonneg.mpr hc.le), EReal.real_coe_toENNReal]
    calc ENNReal.ofReal c * circleDeficit u x v r K
        ≤ ENNReal.ofReal c *
            (ENNReal.ofReal (2 * Real.pi) * ((K : EReal) - u x).toENNReal) :=
          by gcongr; exact hu.submean x v r hr hD K hKbound
      _ = ENNReal.ofReal (2 * Real.pi) *
            (ENNReal.ofReal c * ((K : EReal) - u x).toENNReal) := by ring
  have hge : (0 : ℝ) ≤ C'' - C' := by simp [hC''def]
  have hiff := discSubmean_add_bound_iff (u := fun y => (c : EReal) * u y) x v hr.le C'
    (C'' - C') hge hC'
  rw [show C' + (C'' - C') = C'' by ring] at hiff
  exact hiff.mp key

theorem DiscPshOn.const_mul {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) {c : ℝ} (hc : 0 < c) :
    DiscPshOn (fun y => (c : EReal) * u y) U := by
  have hcont : Continuous fun z : EReal => (c : EReal) * z := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    exact (EReal.continuousAt_mul (p := ((c : EReal), z))
      (Or.inl (by simpa using hc.ne')) (Or.inl (by simpa using hc.ne'))
      (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hmono : Monotone fun z : EReal => (c : EReal) * z :=
    fun a b hab => mul_le_mul_of_nonneg_left hab (EReal.coe_nonneg.mpr hc.le)
  refine ⟨fun x hx htop => ?_, hcont.comp_upperSemicontinuousOn hu.upperSemicontinuousOn hmono,
    hu.hasDiscSubmeanOn_const_mul hc⟩
  have h := hu.ne_top x hx
  rcases (EReal.mul_eq_top _ _).mp htop with h1 | h1 | h1 | h1
  · exact EReal.coe_ne_bot c h1.1
  · exact absurd h1.1 (not_lt.mpr (EReal.coe_nonneg.mpr hc.le))
  · exact EReal.coe_ne_top c h1.1
  · exact h h1.2

theorem PlurisubharmonicAt.const_mul {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicAt (fun y => (c : EReal) * u y) x := by
  obtain ⟨U, hU, hxU, hdu⟩ := hu
  exact ⟨U, hU, hxU, hdu.const_mul hc⟩

theorem PlurisubharmonicOn.const_mul {u : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicOn (fun y => (c : EReal) * u y) U :=
  fun x hx => (hu x hx).const_mul hc

end SGPT.Foundations.Analysis
