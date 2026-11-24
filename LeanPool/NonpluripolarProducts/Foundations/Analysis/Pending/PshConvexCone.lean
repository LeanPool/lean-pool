/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic

/-!
# Plurisubharmonic functions form a convex cone

`SGPT.Foundations.Analysis.Plurisubharmonic` records the disc criterion and closure
under `max`, but not the two remaining basic closure properties: a sum of two
plurisubharmonic functions is plurisubharmonic, and a positive real multiple of a
plurisubharmonic function is plurisubharmonic.  Both are needed as soon as
weights of the shape `c • φ` or `φ + ψ` occur, which is everywhere in
multiplier-ideal theory (`FirstPass.MultiplierIdeals` uses the weight
`exp (-c φ)`), so they are proved here once.

Everything is in the extended reals: `⊥` is allowed and `⊤` is excluded, matching
`DiscPshOn`.  For the sum that is exactly what makes the indeterminate `⊥ + ⊤`
impossible.  For the scalar multiple the factor is required to be *strictly*
positive; `c = 0` gives the constant `0` by the convention `0 * ⊥ = 0`, which is
plurisubharmonic by `plurisubharmonicAt_const` instead.

The submean tests are transported through two pointwise deficit identities

  `(C + D) - (a + b) = (C - a) + (D - b)`   for `a ≤ C` and `b ≤ D`,
  `(c * C) - c * a   = c * (C - a)`         for `a ≤ C` and `0 < c`,

valid in `EReal` including at `a = ⊥`.  `EReal.toENNReal` turns them into
identities of `ℝ≥0∞`-valued deficits, and the angular integral is additive
resp. homogeneous.  The only bookkeeping is that `HasDiscSubmeanOn` quantifies
over *every* finite majorant on the disc while the identities produce one
specific majorant; `discSubmean_add_bound_iff` transports the test between
majorants, and compactness of the disc supplies the specific one.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Pointwise deficit identities in `EReal` -/

/-- Deficits below finite majorants add. -/
theorem ereal_coe_add_sub_add {C D : ℝ} {a b : EReal} (ha : a ≤ (C : EReal))
    (hb : b ≤ (D : EReal)) :
    ((C + D : ℝ) : EReal) - (a + b) = ((C : EReal) - a) + ((D : EReal) - b) := by
  have hnb : 0 ≤ (D : EReal) - b :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top D)) (Or.inl (EReal.coe_ne_bot D))).mpr hb
  induction a using EReal.rec with
  | bot =>
      have hb' : ((D : EReal) - b) ≠ ⊥ := fun h => by rw [h] at hnb; simp at hnb
      simp [EReal.top_add_of_ne_bot hb']
  | top => exact absurd ha (by simp)
  | coe x =>
      induction b using EReal.rec with
      | bot =>
          have ha' : ((C : EReal) - (x : EReal)) ≠ ⊥ := by
            rw [← EReal.coe_sub]; exact EReal.coe_ne_bot _
          simp [EReal.add_top_of_ne_bot ha']
      | top => exact absurd hb (by simp)
      | coe y =>
          rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
            ← EReal.coe_add]
          exact EReal.coe_eq_coe_iff.mpr (by ring)

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
  have hpt : ∀ t : ℝ,
      (((C + D : ℝ) : EReal) -
          (u (x + circleMap 0 r t • v) + w (x + circleMap 0 r t • v))).toENNReal =
        ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal +
          ((D : EReal) - w (x + circleMap 0 r t • v)).toENNReal := by
    intro t
    have hmem := circle_mem_affineClosedDisc x v hr t
    have hna : 0 ≤ (C : EReal) - u (x + circleMap 0 r t • v) :=
      (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr
        (hu _ hmem)
    have hnb : 0 ≤ (D : EReal) - w (x + circleMap 0 r t • v) :=
      (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top D)) (Or.inl (EReal.coe_ne_bot D))).mpr
        (hw _ hmem)
    rw [ereal_coe_add_sub_add (hu _ hmem) (hw _ hmem), EReal.toENNReal_add hna hnb]
  simp_rw [hpt]
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

/-! ### Closure of the disc criterion under sums -/

theorem DiscPshOn.hasDiscSubmeanOn_add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    HasDiscSubmeanOn (fun y => u y + w y) U := by
  intro x v r hr hD C' hC'
  obtain ⟨C, hC⟩ := hu.exists_disc_upper_bound x v hr.le hD
  obtain ⟨D, hD'⟩ := hw.exists_disc_upper_bound x v hr.le hD
  -- Raise the pair `(C, D)` so that its sum dominates the given majorant `C'`.
  set C'' : ℝ := Max.max C' (C + D) with hC''def
  have hCD : C + D ≤ C'' := le_max_right _ _
  set D' : ℝ := D + (C'' - (C + D)) with hD'def
  have hDD' : D ≤ D' := by rw [hD'def]; linarith
  have hsum : C + D' = C'' := by rw [hD'def]; ring
  have hwD' : ∀ y ∈ affineClosedDisc x v r, w y ≤ (D' : EReal) :=
    fun y hy => (hD' y hy).trans (EReal.coe_le_coe_iff.mpr hDD')
  have hx := center_mem_affineClosedDisc x v hr.le
  have hna : 0 ≤ (C : EReal) - u x :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr
      (hC x hx)
  have hnb : 0 ≤ (D' : EReal) - w x :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top D')) (Or.inl (EReal.coe_ne_bot D'))).mpr
      (hwD' x hx)
  have key : circleDeficit (fun y => u y + w y) x v r C'' ≤
      ENNReal.ofReal (2 * Real.pi) * ((C'' : EReal) - (u x + w x)).toENNReal := by
    rw [← hsum, circleDeficit_add x v hr.le hC hwD'
      (hu.measurable_circle_deficit x v hr.le hD C),
      ereal_coe_add_sub_add (hC x hx) (hwD' x hx), EReal.toENNReal_add hna hnb, mul_add]
    exact add_le_add (hu.submean x v r hr hD C hC) (hw.submean x v r hr hD D' hwD')
  have hge : (0 : ℝ) ≤ C'' - C' := by simp [hC''def]
  have hiff := discSubmean_add_bound_iff (u := fun y => u y + w y) x v hr.le C'
    (C'' - C') hge hC'
  rw [show C' + (C'' - C') = C'' by ring] at hiff
  exact hiff.mp key

theorem DiscPshOn.add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    DiscPshOn (fun y => u y + w y) U := by
  refine ⟨fun x hx => ?_, ?_, hu.hasDiscSubmeanOn_add hw⟩
  · exact EReal.add_ne_top (hu.ne_top x hx) (hw.ne_top x hx)
  · refine hu.upperSemicontinuousOn.add' hw.upperSemicontinuousOn (fun x hx => ?_)
    exact EReal.continuousAt_add (Or.inl (hu.ne_top x hx)) (Or.inr (hw.ne_top x hx))

theorem PlurisubharmonicAt.add {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (hw : PlurisubharmonicAt w x) :
    PlurisubharmonicAt (fun y => u y + w y) x := by
  obtain ⟨U, hU, hxU, hdu⟩ := hu
  obtain ⟨V, hV, hxV, hdw⟩ := hw
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    (hdu.mono inter_subset_left).add (hdw.mono inter_subset_right)⟩

theorem PlurisubharmonicOn.add {u w : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w U) :
    PlurisubharmonicOn (fun y => u y + w y) U :=
  fun x hx => (hu x hx).add (hw x hx)

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
