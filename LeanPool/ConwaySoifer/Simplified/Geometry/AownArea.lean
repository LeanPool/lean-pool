/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.Charging
import Mathlib.Tactic

/-!
# AownArea

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace ConwaySoifer.Simplified

/-- The region containing `S₀ ∩ H`. -/
def capRegion (s Y : ℝ) : Set Point :=
  {p | 0 ≤ locY p ∧ locY p ≤ Y ∧ 0 ≤ locX p ∧ locX p ≤ 2 * s * (locY p + 1 / 2)}

/-- The same region in the coordinates `(x, y)`. -/
def capBox (s Y : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ Y ∧ 0 ≤ q.1 ∧ q.1 ≤ 2 * s * (q.2 + 1 / 2)}

theorem isClosed_capBox (s Y : ℝ) : IsClosed (capBox s Y) := by
  simp only [capBox, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem capBox_section (s Y : ℝ) (y : ℝ) :
    volume ((fun x => (x, y)) ⁻¹' capBox s Y) =
      Set.indicator (Set.Icc (0 : ℝ) Y) (fun y => ENNReal.ofReal (2 * s * (y + 1 / 2))) y := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) Y
  · have he : (fun x => (x, y)) ⁻¹' capBox s Y = Set.Icc 0 (2 * s * (y + 1 / 2)) := by
      ext x
      simp only [Set.mem_preimage, capBox, Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨-, -, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨hy.1, hy.2, h3, h4⟩
    rw [he, Real.volume_Icc, Set.indicator_of_mem hy, sub_zero]
  · have he : (fun x => (x, y)) ⁻¹' capBox s Y = ∅ := by
      ext x
      simp only [Set.mem_preimage, capBox, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -, -⟩
      exact hy ⟨h1, h2⟩
    rw [he, measure_empty, Set.indicator_of_notMem hy]

theorem integral_cap (s Y : ℝ) : ∫ y in (0 : ℝ)..Y, 2 * s * (y + 1 / 2) = s * (Y + Y ^ 2) := by
  have h1 : ∫ y in (0 : ℝ)..Y, 2 * s * (y + 1 / 2) =
      2 * s * ∫ y in (0 : ℝ)..Y, (y + 1 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
  rw [h1, intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  simp
  ring

theorem volume_capBox (s Y : ℝ) (hs : 0 ≤ s) (hY : 0 ≤ Y) : volume (capBox s Y) = ENNReal.ofReal (s
    * (Y + Y ^ 2)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isClosed_capBox s Y).measurableSet]
  simp_rw [capBox_section s Y]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => by
        simp only [Pi.zero_apply]; nlinarith [hy.1])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
    integral_cap]

theorem capRegion_eq_image (s Y : ℝ) :
    capRegion s Y = areaTriMap (vertex 0) (sideDirection 0 true) (sideDirection 0 false) '' capBox s
        Y := by
  ext p
  constructor
  · intro hp
    refine ⟨(locX p, locY p), hp, ?_⟩
    rw [areaTriMap_apply, areaLinMap_apply, ← add_assoc]
    exact (loc_decomp p).symm
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hq
    rw [areaTriMap_apply, areaLinMap_apply, ← add_assoc]
    have hx : locX (vertex 0 + q.1 • sideDirection 0 true + q.2 • sideDirection 0 false) = q.1 := by
      simp [locX, vertex, sideDirection, neighbor]
    have hy : locY (vertex 0 + q.1 • sideDirection 0 true + q.2 • sideDirection 0 false) = q.2 := by
      simp [locY, vertex, sideDirection, neighbor]
    exact ⟨by rw [hy]; exact h1, by rw [hy]; exact h2, by rw [hx]; exact h3, by rw [hx, hy]; exact
        h4⟩

theorem volume_capRegion (s Y : ℝ) (hs : 0 ≤ s) (hY : 0 ≤ Y) :
    volume (capRegion s Y) = ENNReal.ofReal (s * (Y + Y ^ 2)) := by
  rw [capRegion_eq_image, areaTriMap_image, volume_image_add_left, volume_image_areaLinMap,
    volume_capBox s Y hs hY]
  have : cross (sideDirection 0 true) (sideDirection 0 false) = 1 := by
    simp [cross, sideDirection, neighbor, vertex]
  rw [this, abs_one, ENNReal.ofReal_one, one_mul]

/-- The upper cutoff retains the dependence on the common side. -/
def aownHeight (r : ℝ) : ℝ := Real.sqrt (25 * r ^ 2 / 21) - 1 / 2

theorem aownHeight_nonneg {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s) :
    0 ≤ aownHeight r := by
  have hd := (T 1).sqDist_le (H.toMinAt.vertex_mem 0) H.contact.2.2
  have hr : 1 / 4 ≤ r ^ 2 := by
    rw [H.common] at hd
    norm_num [vertex, extMid0, sqDist] at hd
    exact hd
  have hz := Real.sq_sqrt (show 0 ≤ 25 * r ^ 2 / 21 by positivity)
  have hn := Real.sqrt_nonneg (25 * r ^ 2 / 21)
  unfold aownHeight
  nlinarith

theorem aown_cap_subset {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : (T 1).carrier ∩ hexagon ⊆ capRegion s (aownHeight r) := by
  rintro p ⟨hp, hhex⟩
  obtain ⟨hy0, _, hx0, hxle⟩ := H.aown_subset hs ⟨hp, hhex⟩
  change 0 ≤ locY p ∧ locY p ≤ aownHeight r ∧ 0 ≤ locX p ∧
    locX p ≤ 2 * s * (locY p + 1 / 2)
  refine ⟨hy0, ?_, hx0, hxle⟩
  have hd := (T 1).sqDist_le hp H.contact.2.2
  rw [sqDist_extMid0, H.common] at hd
  have ht : 0 ≤ locY p + 1 / 2 := by
    linarith
  have hsprod := mul_nonneg (show 0 ≤ 1 / 4 - s by linarith) ht
  have hf : 0 ≤ (locX p - 2 * s * (locY p + 1 / 2)) *
      (locX p + 2 * s * (locY p + 1 / 2) - (locY p + 1 / 2)) := by
    apply mul_nonneg_of_nonpos_of_nonpos <;> nlinarith
  have hcoef : 0 ≤ 1 - 2 * s + 4 * s ^ 2 - 21 / 25 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ 8 / 5 - 4 * s by linarith)]
  have hc := mul_nonneg hcoef (sq_nonneg (locY p + 1 / 2))
  have hz := Real.sq_sqrt (show 0 ≤ 25 * r ^ 2 / 21 by positivity)
  have hn := Real.sqrt_nonneg (25 * r ^ 2 / 21)
  unfold aownHeight
  nlinarith

/-- The strengthened area cap from the third pass, in normalized area units. -/
theorem aown_cap {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) :
    2 * (volume ((T 1).carrier ∩ hexagon)).toReal ≤ 50 * s / 21 * r ^ 2 - s / 2 := by
  have hY := aownHeight_nonneg H
  have hs0 := H.s_pos
  have hvol := volume_capRegion s (aownHeight r) H.s_pos.le hY
  have hb := toReal_le_of_subset (aown_cap_subset H hs)
    (show 0 ≤ s * (aownHeight r + aownHeight r ^ 2) by positivity) hvol
  have hz := Real.sq_sqrt (show 0 ≤ 25 * r ^ 2 / 21 by positivity)
  have he : 2 * s * (aownHeight r + aownHeight r ^ 2) = 50 * s / 21 * r ^ 2 - s / 2 := by
    unfold aownHeight
    have hh := congrArg (fun z : ℝ => s * z) hz
    nlinarith
  linarith

/-- Loss of the minimum-section owner from the strengthened cap. -/
theorem aown_loss_zero {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : r ^ 2 - (50 * s / 21 * r ^ 2 - s / 2) ≤ sideLoss T 0 := by
  have hfinI : volume ((T 1).carrier ∩ hexagon) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (T 1).volume_carrier_lt_top).ne
  have hfinO : volume ((T 1).carrier \ hexagon) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (T 1).volume_carrier_lt_top).ne
  have hsplit : (volume ((T 1).carrier ∩ hexagon)).toReal +
      (volume ((T 1).carrier \ hexagon)).toReal = r ^ 2 / 2 := by
    rw [← ENNReal.toReal_add hfinI hfinO, measure_inter_add_sdiff _ measurableSet_hexagon,
      (T 1).volume_carrier, H.common, ENNReal.toReal_ofReal (by positivity)]
  have hc := aown_cap H hs
  change r ^ 2 - (50 * s / 21 * r ^ 2 - s / 2) ≤
    2 * (volume ((T 1).carrier \ hexagon)).toReal
  linarith

/-- No other owner can have midpoint-sized loss on `(0, 1/10]`. -/
theorem aown_no_cost {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) (i : Fin 6) (hi : i ≠ 0) : sideLoss T i < r ^ 2 / 4 := by
  by_contra hcost
  push Not at hcost
  have hb := charged_budget H
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hrecv := aown_loss_zero H hs
  have hp := penalty_le (T := T) (r := r) 0
  have hlo (k : Fin 6) :
      (if k = i then r ^ 2 / 4 - r ^ 2 / 23 else
        if k = 0 then r ^ 2 - (50 * s / 21 * r ^ 2 - s / 2) - r ^ 2 / 23 else s ^ 2) ≤
      sideLoss T k - penalty T r k := by
    split_ifs with hki hk0
    · subst k; rw [penalty, ite_eq_left hcost]; linarith
    · subst k; linarith
    · exact effective_loss_ge H k
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 6))) => hlo k)
  have he : (∑ k : Fin 6, if k = i then r ^ 2 / 4 - r ^ 2 / 23 else
        if k = 0 then r ^ 2 - (50 * s / 21 * r ^ 2 - s / 2) - r ^ 2 / 23 else s ^ 2) =
      r ^ 2 / 4 - 2 * r ^ 2 / 23 + r ^ 2 - (50 * s / 21 * r ^ 2 - s / 2) + 4 * s ^ 2 := by
    fin_cases i <;> simp [Fin.sum_univ_six] at hi ⊢ <;> ring
  rw [he] at hh
  have hm : 0 ≤ (1 / 10 - s) * (311 / 210 - 4 * s) := mul_nonneg (by linarith) (by linarith)
  have hs0 := H.s_pos
  have hprod : 0 ≤ (1 - r ^ 2) * (7 - 1 - 1 / 4 + 2 / 23 + 50 * s / 21) := by
    apply mul_nonneg (sub_nonneg.mpr hr.le)
    positivity
  nlinarith

/-- The small-Aown strengthening holds through the new closed endpoint. -/
theorem aown_strengthening {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : SmallStrengthening .Aown T r := by
  refine ⟨?_, ?_⟩
  · intro i _ _ hi _
    by_contra hover
    push Not at hover
    exact (not_le.mpr (aown_no_cost H hs i (hi rfl))) (H.loss_overfull i hover)
  · intro j m _ _ hj _
    apply H.corner_mids j m
    · intro hm
      have hi : (⟨2 * j.val, by omega⟩ : Fin 6) ≠ 0 := by
        have := hj rfl
        fin_cases j <;> simp_all
      exact (not_le.mpr (aown_no_cost H hs _ hi)) (H.loss_mid _ j m hm)
    · intro hm
      have hi : (⟨2 * j.val + 1, by omega⟩ : Fin 6) ≠ 0 := by
        fin_cases j <;> decide
      exact (not_le.mpr (aown_no_cost H hs _ hi)) (H.loss_mid _ j m hm)

end ConwaySoifer.Simplified
