/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Cap
public import LeanPool.ConwaySoifer.Geometry.Canonical
import Mathlib.Tactic

/-!
# The universal corner cap and the external-midpoint cost

* `cornerCap_volume`: a triangle of side `σ ≤ 1` containing a point of level `2` (for a unit
  level form) has volume `< σ²/46` at levels `≤ 1`.  Applied to a corner owner and the level form
  of its corner cell this is `|A_j ∩ H| / A < r²/23` (research proof, Lemma 2.1).
* `midpoint_cost_volume`: a triangle of side `σ ≤ 1` containing a point of level `3/2` has
  volume `≥ σ²/8` at levels `> 1`.  Applied to a side owner containing an external corner
  midpoint this is `D_i ≥ r²/4` (Lemma 4.1).
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
namespace ConwaySoifer

/-! ### The polynomial inequalities -/

/-- `23 (S-1)² < S p` on the region `S² - S p + p² ≤ 1`, `1 < S`. -/
theorem cap_ineq {S p : ℝ} (hS : 1 < S)
    (hc : S ^ 2 - S * p + p ^ 2 ≤ 1) : 23 * (S - 1) ^ 2 < S * p := by
  by_contra hcon
  push Not at hcon
  have h3 : 3 * S ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 * p - S)]
  have hy : S ≤ 7 / 6 := by
    nlinarith
  set y := S - 1 with hy_def
  have hy0 : 0 < y := by
    linarith
  have hy6 : y ≤ 1 / 6 := by
    linarith
  -- `A = S² - 46 (S-1)² > 0`
  have hA : 0 < S ^ 2 - 46 * (S - 1) ^ 2 := by
    nlinarith
  have hsq : (S - 2 * p) ^ 2 ≤ 4 - 3 * S ^ 2 := by
    nlinarith
  have hAS : S ^ 2 - 46 * (S - 1) ^ 2 ≤ S * (S - 2 * p) := by
    nlinarith
  have hA2 : (S ^ 2 - 46 * (S - 1) ^ 2) ^ 2 ≤ (S * (S - 2 * p)) ^ 2 :=
    pow_le_pow_left₀ hA.le hAS 2
  have hS2 : (S * (S - 2 * p)) ^ 2 ≤ S ^ 2 * (4 - 3 * S ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  -- the quartic `(S-1) · (2028 y³ - 168 y² - 72 y + 8)` is positive
  have hf : 0 < 2028 * y ^ 3 - 168 * y ^ 2 - 72 * y + 8 := by
    nlinarith [mul_nonneg (sq_nonneg (y - 7 / 50)) (by linarith : (0 : ℝ) ≤ y + 197 / 1000),
      sq_nonneg y]
  have hQ : 0 < (S ^ 2 - 46 * (S - 1) ^ 2) ^ 2 - S ^ 2 * (4 - 3 * S ^ 2) := by
    have : (S ^ 2 - 46 * (S - 1) ^ 2) ^ 2 - S ^ 2 * (4 - 3 * S ^ 2) =
        y * (2028 * y ^ 3 - 168 * y ^ 2 - 72 * y + 8) := by
      rw [hy_def]; ring
    rw [this]
    exact mul_pos hy0 hf
  linarith

/-- `(S - 1/2)² ≤ (3/4) (S - R) S` when `R < 1/2`, `1/2 < S ≤ 7/6`. -/
theorem mid_ineq {S R : ℝ} (hR : R < 1 / 2) (hS : S ≤ 7 / 6)
    (hS12 : 1 / 2 < S) : (S - 1 / 2) ^ 2 ≤ 3 / 4 * ((S - R) * S) := by
  have hgap : 0 ≤ (1 / 2 - R) * S :=
    mul_nonneg (by linarith) (by linarith)
  have hinterval : 0 ≤ (S - 1 / 2) * (2 - S) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### Measure bookkeeping -/

theorem toReal_le_of_subset {A B : Set Point} (h : A ⊆ B) {x : ℝ} (hx : 0 ≤ x)
    (hB : volume B = ENNReal.ofReal x) : (volume A).toReal ≤ x := by
  have := measure_mono (μ := volume) h
  rw [hB] at this
  calc (volume A).toReal ≤ (ENNReal.ofReal x).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = x := ENNReal.toReal_ofReal hx

theorem det_of_volume {a b c : Point} {σ : ℝ} (hσ : 0 < σ)
    (hvol : volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (σ ^ 2 / 2)) :
    |triangleDet a b c| = σ ^ 2 := by
  rw [volume_triangle] at hvol
  have h := ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity) |>.mp hvol
  rw [triangleDet_eq_cross]
  linarith

theorem cross_ge_min_vertex (Q : EquilateralTriangle) (u : Point) {p : Point}
    (hp : p ∈ Q.carrier) :
    ∃ i, (∀ j, cross u (Q.vertices i) ≤ cross u (Q.vertices j)) ∧
      cross u (Q.vertices i) ≤ cross u p := by
  obtain ⟨i, hi, hpi⟩ := cross_le_max_vertex Q (-u) hp
  refine ⟨i, fun j => ?_, ?_⟩
  · have := hi j; rw [cross_neg_left, cross_neg_left] at this; linarith
  · rw [cross_neg_left, cross_neg_left] at hpi; linarith

/-- The level values of a hull point lie between the minimal and maximal vertex levels. -/
theorem hull_level_ge {a b c : Point} (u : Point) {p : Point} (hp : p ∈ convexHull ℝ {a, b, c})
    {m : ℝ} (ha : m ≤ cross u a) (hb : m ≤ cross u b) (hc : m ≤ cross u c) : m ≤ cross u p := by
  have hsub : convexHull ℝ {a, b, c} ⊆ {q | m ≤ cross u q} := by
    apply convexHull_min
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> assumption
    · intro x hx y hy s t hs ht hst
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [cross_add_right, cross_smul_right, cross_smul_right]
      have : s * m + t * m = m := by
        rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg hs (sub_nonneg.2 hx), mul_nonneg ht (sub_nonneg.2 hy)]
  exact hsub hp

/-! ### The corner cap for a labelled triangle -/

theorem cornerCap_aux {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (u : Point) (hu : u ≠ 0)
    {a b c : Point} (hdet : triangleDet a b c ≠ 0)
    (hvol : volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (σ ^ 2 / 2))
    (hid : (cross u b - cross u a) ^ 2 - (cross u b - cross u a) * (cross u c - cross u a) +
      (cross u c - cross u a) ^ 2 = σ ^ 2)
    (hab : cross u a ≤ cross u b) (hbc : cross u b ≤ cross u c) (hc2 : 2 ≤ cross u c) :
    (volume (convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1})).toReal < σ ^ 2 / 46 := by
  set ma := cross u a with hma_def
  set mb := cross u b with hmb_def
  set mc := cross u c with hmc_def
  set p := mb - ma with hp_def
  set S := mc - ma with hS_def
  have hp0 : 0 ≤ p := by
    linarith
  have hpS : p ≤ S := by
    linarith
  have hcon : p ^ 2 - p * S + S ^ 2 = σ ^ 2 := by
    rw [hp_def, hS_def]; linarith [hid]
  have hSp : S - p ≤ 1 := by
    have : (S - p) ^ 2 ≤ σ ^ 2 := by
      nlinarith [mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ S)]
    nlinarith
  have hmb : 1 ≤ mb := by
    linarith
  have hσ2 : 0 < σ ^ 2 / 46 := by
    positivity
  by_cases hma : 1 ≤ ma
  · -- the whole triangle is at level `≥ 1`
    have hsub : convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1} ⊆ {p | cross u p = 1} := by
      rintro q ⟨hq, hq1⟩
      simp only [Set.mem_ofPred_eq] at hq1 ⊢
      have := hull_level_ge u hq (m := 1) hma hmb (by linarith)
      linarith
    have := measure_mono_null hsub (volume_level_line u hu 1)
    rw [this, ENNReal.toReal_zero]
    exact hσ2
  · push Not at hma
    have hS1 : 1 < S := by
      linarith
    -- the bottom cap
    have hsub := cap_subset (-u) (-1) (a := b) (b := c) (c := a)
      (by rw [triangleDet_rotate]; exact hdet)
      (by rw [cross_neg_left]; linarith) (by rw [cross_neg_left]; linarith)
      (by rw [cross_neg_left]; linarith)
    have hset : convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1} =
        convexHull ℝ {b, c, a} ∩ {p | -1 ≤ cross (-u) p} := by
      rw [hull3_rotate]
      congr 1
      ext q; simp only [Set.mem_ofPred_eq, cross_neg_left]; constructor <;> intro h <;> linarith
    rw [hset]
    have hcap := volume_capTriangle (-u) (-1) b c a
    have hdet' : |triangleDet b c a| = σ ^ 2 := by
      rw [triangleDet_rotate]; exact det_of_volume hσ hvol
    rw [hdet', cross_neg_left, cross_neg_left, cross_neg_left] at hcap
    have hα : |(-ma - -1) / (-ma - -mb)| = (1 - ma) / p := by
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
      rw [hp_def]; ring
    have hβ : |(-ma - -1) / (-ma - -mc)| = (1 - ma) / S := by
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
      rw [hS_def]; ring
    rw [hα, hβ] at hcap
    have hp_pos : 0 < p := by
      by_contra h
      have : p = 0 := le_antisymm (not_lt.mp h) hp0
      rw [this] at hcon
      nlinarith
    have h1ma0 : 0 < 1 - ma := by
      linarith
    have hS0 : 0 < S := by
      linarith
    have hx : 0 ≤ (1 - ma) / p * ((1 - ma) / S) * (σ ^ 2 / 2) :=
      mul_nonneg (mul_nonneg (div_nonneg h1ma0.le hp_pos.le) (div_nonneg h1ma0.le hS0.le))
        (by positivity)
    have hle := toReal_le_of_subset hsub hx hcap
    refine lt_of_le_of_lt hle ?_
    -- `(1 - ma)² / (p S) · σ²/2 < σ²/46`
    have hkey : 23 * (S - 1) ^ 2 < S * p := cap_ineq hS1 (by nlinarith [hcon, hσ1, hσ])
    have h1ma : 1 - ma ≤ S - 1 := by
      rw [hS_def]; linarith
    have hsq : (1 - ma) ^ 2 ≤ (S - 1) ^ 2 := pow_le_pow_left₀ h1ma0.le h1ma 2
    have hfrac : (1 - ma) / p * ((1 - ma) / S) < 1 / 23 := by
      rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc (1 - ma) / p * ((1 - ma) / S) * (σ ^ 2 / 2)
        < 1 / 23 * (σ ^ 2 / 2) := by
          exact mul_lt_mul_of_pos_right hfrac (by positivity)
      _ = σ ^ 2 / 46 := by
        ring

/-! ### The midpoint cost for a labelled triangle -/

theorem midpointCost_aux {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (u : Point) (hu : u ≠ 0)
    {a b c : Point} (hdet : triangleDet a b c ≠ 0)
    (hvol : volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (σ ^ 2 / 2))
    (hid : (cross u b - cross u a) ^ 2 - (cross u b - cross u a) * (cross u c - cross u a) +
      (cross u c - cross u a) ^ 2 = σ ^ 2)
    (hab : cross u a ≤ cross u b) (hbc : cross u b ≤ cross u c) (hc32 : 3 / 2 ≤ cross u c) :
    σ ^ 2 / 8 ≤ (volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p})).toReal := by
  set ma := cross u a with hma_def
  set mb := cross u b with hmb_def
  set mc := cross u c with hmc_def
  set R := mc - mb with hR_def
  set S := mc - ma with hS_def
  have hR0 : 0 ≤ R := by
    linarith
  have hRS : R ≤ S := by
    linarith
  have hcon : R ^ 2 - R * S + S ^ 2 = σ ^ 2 := by
    rw [hR_def, hS_def]; linarith [hid]
  have hRSle : R * S ≤ σ ^ 2 := by
    nlinarith [sq_nonneg (R - S)]
  have h3 : 3 * S ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 * R - S)]
  have hS76 : S ≤ 7 / 6 := by
    nlinarith
  have hfin : volume (convexHull ℝ {a, b, c}) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hcont : Continuous (fun p : Point => cross u p) := by
    unfold cross; fun_prop
  have hmeas : MeasurableSet {p : Point | 1 < cross u p} :=
    isOpen_lt continuous_const hcont |>.measurableSet
  have hnull := volume_inter_level_line (convexHull ℝ {a, b, c}) u hu 1
  -- the closed and open pieces have the same volume
  have hclosed : volume (convexHull ℝ {a, b, c} ∩ {p | 1 ≤ cross u p}) ≤
      volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p}) := by
    have hsub : convexHull ℝ {a, b, c} ∩ {p | 1 ≤ cross u p} ⊆
        convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p} ∪
          convexHull ℝ {a, b, c} ∩ {p | cross u p = 1} := by
      rintro q ⟨hq, h1⟩
      simp only [Set.mem_ofPred_eq] at h1
      rcases lt_or_eq_of_le h1 with h | h
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, h.symm⟩
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ + _ := measure_union_le _ _
      _ = _ := by
        rw [hnull, add_zero]
  by_cases hR : 1 / 2 ≤ R
  · -- the top cap at level `mc - 1/2 ≥ 1`
    have hsup := cap_supset u (mc - 1 / 2) (a := a) (b := b) (c := c) (by linarith) (by linarith)
      (by linarith)
    have hcap := volume_capTriangle u (mc - 1 / 2) a b c
    rw [det_of_volume hσ hvol] at hcap
    have hS0 : 0 < S := by
      linarith
    have hR0' : 0 < R := by
      linarith
    have hα : |(mc - (mc - 1 / 2)) / (mc - ma)| = 1 / 2 / S := by
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), hS_def]; ring_nf
    have hβ : |(mc - (mc - 1 / 2)) / (mc - mb)| = 1 / 2 / R := by
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), hR_def]; ring_nf
    rw [hα, hβ] at hcap
    have hsub2 : convexHull ℝ {a, b, c} ∩ {p | mc - 1 / 2 ≤ cross u p} ⊆
        convexHull ℝ {a, b, c} ∩ {p | 1 ≤ cross u p} := by
      rintro q ⟨hq, h⟩; exact ⟨hq, by simp only [Set.mem_ofPred_eq] at h ⊢; linarith⟩
    have hge : volume (convexHull ℝ {c, capPoint u (mc - 1 / 2) c a, capPoint u (mc - 1 / 2) c b}) ≤
        volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p}) :=
      le_trans (measure_mono (hsup.trans hsub2)) hclosed
    rw [hcap] at hge
    have hfinI : volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p}) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
    have := ENNReal.toReal_mono hfinI hge
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    refine le_trans ?_ this
    -- `σ²/8 ≤ (1/(2S)) (1/(2R)) σ²/2`
    have hSR : 0 < S * R := mul_pos hS0 hR0'
    have heq : 1 / 2 / S * (1 / 2 / R) * (σ ^ 2 / 2) = σ ^ 2 / (8 * (S * R)) := by
      field_simp; ring
    rw [heq]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  · push Not at hR
    have hmb1 : 1 < mb := by
      linarith
    -- complement of the bottom cap
    have hsplit : volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p}) +
        volume (convexHull ℝ {a, b, c} \ {p | 1 < cross u p}) =
        volume (convexHull ℝ {a, b, c}) :=
      measure_inter_add_sdiff _ hmeas
    have hdiff : convexHull ℝ {a, b, c} \ {p | 1 < cross u p} =
        convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1} := by
      ext q; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_lt]
    rw [hdiff] at hsplit
    have hfinI : volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p}) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
    have hfinC : volume (convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1}) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
    have hsplitR : (volume (convexHull ℝ {a, b, c} ∩ {p | 1 < cross u p})).toReal +
        (volume (convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1})).toReal = σ ^ 2 / 2 := by
      rw [← ENNReal.toReal_add hfinI hfinC, hsplit, hvol, ENNReal.toReal_ofReal (by positivity)]
    -- bound the bottom cap
    have hcapbound : (volume (convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1})).toReal ≤
        3 / 4 * (σ ^ 2 / 2) := by
      by_cases hma : 1 ≤ ma
      · have hsub : convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1} ⊆ {p | cross u p = 1} := by
          rintro q ⟨hq, hq1⟩
          simp only [Set.mem_ofPred_eq] at hq1 ⊢
          have := hull_level_ge u hq (m := 1) hma hmb1.le (by linarith)
          linarith
        have := measure_mono_null hsub (volume_level_line u hu 1)
        rw [this, ENNReal.toReal_zero]
        positivity
      · push Not at hma
        have hsub := cap_subset (-u) (-1) (a := b) (b := c) (c := a)
          (by rw [triangleDet_rotate]; exact hdet)
          (by rw [cross_neg_left]; linarith) (by rw [cross_neg_left]; linarith)
          (by rw [cross_neg_left]; linarith)
        have hset : convexHull ℝ {a, b, c} ∩ {p | cross u p ≤ 1} =
            convexHull ℝ {b, c, a} ∩ {p | -1 ≤ cross (-u) p} := by
          rw [hull3_rotate]
          congr 1
          ext q; simp only [Set.mem_ofPred_eq, cross_neg_left]; constructor <;> intro h <;> linarith
        rw [hset]
        have hcap := volume_capTriangle (-u) (-1) b c a
        have hdet' : |triangleDet b c a| = σ ^ 2 := by
          rw [triangleDet_rotate]; exact det_of_volume hσ hvol
        rw [hdet', cross_neg_left, cross_neg_left, cross_neg_left] at hcap
        set p := mb - ma with hp_def
        have hp0 : 0 < p := by
          rw [hp_def]; linarith
        have hS0 : 0 < S := by
          rw [hS_def]; linarith
        have hα : |(-ma - -1) / (-ma - -mb)| = (1 - ma) / p := by
          rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
          rw [hp_def]; ring
        have hβ : |(-ma - -1) / (-ma - -mc)| = (1 - ma) / S := by
          rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
          rw [hS_def]; ring
        rw [hα, hβ] at hcap
        have h1ma0 : 0 < 1 - ma := by
          linarith
        have hx : 0 ≤ (1 - ma) / p * ((1 - ma) / S) * (σ ^ 2 / 2) :=
          mul_nonneg (mul_nonneg (div_nonneg h1ma0.le hp0.le) (div_nonneg h1ma0.le hS0.le))
            (by positivity)
        have hle := toReal_le_of_subset hsub hx hcap
        refine le_trans hle ?_
        have h1ma : 1 - ma ≤ S - 1 / 2 := by
          rw [hS_def]; linarith
        have hS12 : 1 / 2 < S := by
          linarith
        have hsq : (1 - ma) ^ 2 ≤ (S - 1 / 2) ^ 2 := pow_le_pow_left₀ h1ma0.le h1ma 2
        have hpSR : p = S - R := by
          rw [hp_def, hS_def, hR_def]; ring
        have hkey := mid_ineq hR hS76 hS12
        rw [← hpSR] at hkey
        have hfrac : (1 - ma) / p * ((1 - ma) / S) ≤ 3 / 4 := by
          rw [div_mul_div_comm, div_le_iff₀ (mul_pos hp0 hS0)]
          nlinarith [hsq, hkey]
        exact mul_le_mul_of_nonneg_right hfrac (by positivity)
    linarith

end ConwaySoifer
