/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ApexPairCount
public import LeanPool.DistinctDistances.RefinedClosePairGeometry
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The averaged apex-window row at a general far threshold

Formalizes Lemma A'' of `docs/results/explicit-constant-gain-5-239-2026-10-20.md` (§2) at a
general far threshold `λ`, as used by the rows `AA` of Theorem S4 in
`docs/results/explicit-constant-gain-1-40-2026-10-21.md`. The case `λ² ≥ 3` used by
Theorem C60 is `six_mul_far_pairs_le_apex_window`.

The points lie in the annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` with `0 < σ`. All thresholds are
squared and in units of `ρ²`: `l = λ²`, and `w`, `h` are the squared window ends. The real
`r₄ ≥ 0` is an upper bound for `√(4 - l)`, given in the squared form `4 - l ≤ r₄²`. Write
`P(t) = Σ_j (N_j(t) - 1)` for the number of ordered pairs at squared distance at most `t`,
where `N_j(t)` counts the points within squared distance `t` of `p j`, and `Q = 3D - n + 1`.
The ordered pairs at squared distance more than `lρ²` number `n² - n - P(lρ²)`.

* Apex range (Lemma A''(i), `apex_sq_dist_mem_of_sq_far_general`): if `4 - l ≤ 4σ²`, an apex
  of a pair at squared distance more than `lρ²` sees it at a squared radius strictly between
  `(σ² + 1 - σ r₄)ρ²` and `(2 + r₄)ρ²`, so inside the window `(wρ², hρ²]` when
  `w ≤ σ² + 1 - σ r₄` and `2 + r₄ ≤ h`.
* Circle count (Lemma A''(ii)): Step L0 at `x = 1 - σ²` and `t = l`
  (`scaled_annular_equidistant_triple_close_pair_sharp`), under `(1 - σ²)(σ + 1) ≤ σ l`, puts a
  pair within `lρ²` on every three-point circle about a point of the annulus. This is the chord
  condition `C((w, 2], λ)` for every radius at once. The apex count
  `six_mul_card_pairs_le_of_apex` then gives
  `6 (n² - n - P(lρ²)) ≤ 6 n Q + 4 Σ_z #{q : wρ² < |zq|² ≤ hρ²}`.
* The window count is at most `P(hρ²) - P(wρ²)`.

The result `six_mul_far_pairs_le_apex_window_general` is the S2 row
`2(1 - ε - 𝒜(λ)) + (4/3)(1 - ε - 𝒜(h)) ≤ 2𝔮 + (4/3)(1 - ε - 𝒜(w))` times `3n²`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### Lemma A''(i): the apex range at a general threshold -/

/-- Lemma A''(i) at a general far threshold: in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` with
`0 ≤ σ`, let `l` be a squared threshold and `r₄ ≥ 0` a real with `4 - l ≤ r₄²` (an upper
bound for `√(4 - l)`) and `4 - l ≤ 4σ²`. An apex `z` of a pair `a, b` at squared distance more
than `lρ²` has squared radius `dist z a²` strictly between `(σ² + 1 - σ r₄)ρ²` and
`(2 + r₄)ρ²`. Only the upper annulus bound is needed for `a` and `b`. -/
theorem apex_sq_dist_mem_of_sq_far_general {c z a b : Point} {ρ σ l r₄ : ℝ} (hρ : 0 < ρ)
    (hσ : 0 ≤ σ) (hr₄ : 0 ≤ r₄) (hlr : 4 - l ≤ r₄ ^ 2) (hlσ : 4 - l ≤ 4 * σ ^ 2)
    (hz : σ ^ 2 * ρ ^ 2 ≤ dist z c ^ 2) (hz1 : dist z c ^ 2 ≤ ρ ^ 2)
    (ha1 : dist a c ^ 2 ≤ ρ ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2)
    (hab : l * ρ ^ 2 < dist a b ^ 2) (heq : dist z a = dist z b) :
    (σ ^ 2 + 1 - σ * r₄) * ρ ^ 2 < dist z a ^ 2 ∧ dist z a ^ 2 < (2 + r₄) * ρ ^ 2 := by
  rw [dist_eq_norm] at hz hz1 ha1 hb1
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right a b c] at hab
  have hza : dist z a = ‖(z - c) - (a - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  have hzb : dist z b = ‖(z - c) - (b - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  rw [hza] at heq ⊢
  rw [hzb] at heq
  set Z := z - c
  set A := a - c
  set B := b - c
  clear_value Z A B
  have hρ2 : 0 < ρ ^ 2 := by positivity
  -- parallelogram law: `‖A + B‖² + ‖A - B‖² = 2(‖A‖² + ‖B‖²)`
  have hpar : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  -- `‖A + B‖² < (4 - l)ρ² ≤ r₄²ρ²`, so `‖A + B‖ < r₄ρ`
  have hlr' := mul_le_mul_of_nonneg_right hlr hρ2.le
  have hw2 : ‖A + B‖ ^ 2 < (r₄ * ρ) ^ 2 := by
    rw [mul_pow]
    linarith
  have hw : ‖A + B‖ < r₄ * ρ := (abs_lt_of_sq_lt_sq' hw2 (mul_nonneg hr₄ hρ.le)).2
  have hw0 : 0 ≤ ‖A + B‖ := norm_nonneg _
  -- `σρ ≤ ‖Z‖ ≤ ρ`
  have hζ : σ * ρ ≤ ‖Z‖ :=
    (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hz) (norm_nonneg Z)).2
  have hζ1 : ‖Z‖ ≤ ρ := (abs_le_of_sq_le_sq' hz1 hρ.le).2
  -- `2r² = 2‖Z‖² + ‖A‖² + ‖B‖² - 2⟪Z, A + B⟫`
  have h2 : 2 * ‖Z - A‖ ^ 2 = 2 * ‖Z‖ ^ 2 + ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * ⟪Z, A + B⟫ := by
    have e1 := norm_sub_sq_real Z A
    have e2 := norm_sub_sq_real Z B
    rw [inner_add_right]
    have e3 : ‖Z - A‖ ^ 2 = ‖Z - B‖ ^ 2 := by rw [heq]
    linarith
  obtain ⟨hin1, hin2⟩ := abs_le.mp (abs_real_inner_le_norm Z (A + B))
  constructor
  · -- `2r² > (2‖Z‖ - ‖A + B‖)²/2 + lρ²/2`; then split on the sign of `2σ - r₄`
    rcases le_or_gt r₄ (2 * σ) with hcase | hcase
    · have hk0 : 0 ≤ (2 * σ - r₄) * ρ := mul_nonneg (by linarith) hρ.le
      have hk : (2 * σ - r₄) * ρ ≤ 2 * ‖Z‖ - ‖A + B‖ := by nlinarith
      have hsq := mul_le_mul hk hk hk0 (hk0.trans hk)
      nlinarith
    · have hsq : 0 ≤ (2 * ‖Z‖ - ‖A + B‖) ^ 2 := sq_nonneg _
      have hlσ' := mul_le_mul_of_nonneg_right hlσ hρ2.le
      have hσr : 0 ≤ σ * (r₄ - 2 * σ) * ρ ^ 2 :=
        mul_nonneg (mul_nonneg hσ (by linarith)) hρ2.le
      nlinarith
  · -- `2r² ≤ 2ρ² + 2ρ² + 2‖Z‖‖A + B‖ < (4 + 2r₄)ρ²`
    have hzw : ‖Z‖ * ‖A + B‖ < r₄ * ρ ^ 2 := by
      calc ‖Z‖ * ‖A + B‖ ≤ ρ * ‖A + B‖ := mul_le_mul_of_nonneg_right hζ1 hw0
        _ < ρ * (r₄ * ρ) := mul_lt_mul_of_pos_left hw hρ
        _ = r₄ * ρ ^ 2 := by ring
    nlinarith

/-! ### Lemma A''(ii): no far triangle on a circle -/

/-- Step L0 at `x = 1 - σ²` and `t = l`: when `(1 - σ²)(σ + 1) ≤ σ l`, three points of the
annulus `σ²ρ² ≤ dist · c² ≤ ρ²` equidistant from a point `z` of the annulus are not pairwise at
squared distance more than `lρ²`. -/
private lemma false_of_three_pairwise_sq_far_on_circle {c z a b d : Point} {ρ σ l : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hL0 : (1 - σ ^ 2) * (σ + 1) ≤ σ * l)
    (hz : σ ^ 2 * ρ ^ 2 ≤ dist z c ^ 2)
    (ha : σ ^ 2 * ρ ^ 2 ≤ dist a c ^ 2) (hb : σ ^ 2 * ρ ^ 2 ≤ dist b c ^ 2)
    (hd : σ ^ 2 * ρ ^ 2 ≤ dist d c ^ 2)
    (ha1 : dist a c ^ 2 ≤ ρ ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2) (hd1 : dist d c ^ 2 ≤ ρ ^ 2)
    (hzab : dist z a = dist z b) (hzad : dist z a = dist z d)
    (hab : l * ρ ^ 2 < dist a b ^ 2) (hbd : l * ρ ^ 2 < dist b d ^ 2)
    (had : l * ρ ^ 2 < dist a d ^ 2) : False := by
  have hx : ρ ^ 2 * (1 - (1 - σ ^ 2)) = σ ^ 2 * ρ ^ 2 := by ring
  obtain ⟨i, j, hij, hclose⟩ := scaled_annular_equidistant_triple_close_pair_sharp c z
    ![a, b, d] hρ (x := 1 - σ ^ 2) (t := l) hσ (by linarith) hL0 (by rw [hx]; exact hz)
    (fun i ↦ by rw [hx]; fin_cases i <;> simp [ha, hb, hd])
    (fun i ↦ by fin_cases i <;> simp [ha1, hb1, hd1])
    (fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [← hzab, ← hzad])
  have hba : l * ρ ^ 2 < dist b a ^ 2 := by rwa [dist_comm]
  have hdb : l * ρ ^ 2 < dist d b ^ 2 := by rwa [dist_comm]
  have hda : l * ρ ^ 2 < dist d a ^ 2 := by rwa [dist_comm]
  fin_cases i <;> fin_cases j <;> simp at hij hclose <;> linarith

/-! ### Lemma A'': the averaged apex-window row -/

/-- Averaged apex-window row (Lemma A'' of the S2 file at a general far threshold `λ`; the S2
row `−2𝒜(λ) − (4/3)𝒜(h) + (4/3)𝒜(w) − 6𝔡 − 4ε ≤ −4` times `3n²`). Let the points lie in the
annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` with `0 < σ`, with no three collinear and the degree cap
three. Take squared thresholds `l = λ²`, `w`, `h` and a real `r₄ ≥ 0` with `4 - l ≤ r₄²` (an
upper bound for `√(4 - l)`), `4 - l ≤ 4σ²`, `0 ≤ w ≤ σ² + 1 - σ r₄` and `2 + r₄ ≤ h`, and the
Step L0 condition `(1 - σ²)(σ + 1) ≤ σ l`. Then the ordered pairs at squared distance more than
`lρ²`, which number `n² - n - P(lρ²)`, satisfy
`6 (n² - n - P(lρ²)) ≤ 6 n Q + 4 (P(hρ²) - P(wρ²))`, where `P(t) = Σ_j (N_j(t) - 1)` counts
the ordered pairs at squared distance at most `t` and `Q = 3D - n + 1`. -/
theorem six_mul_far_pairs_le_apex_window_general {p : Config n} {c : Point}
    {ρ σ l w h r₄ : ℝ}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hloσ : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (hr₄ : 0 ≤ r₄) (hlr : 4 - l ≤ r₄ ^ 2)
    (hlσ : 4 - l ≤ 4 * σ ^ 2) (hL0 : (1 - σ ^ 2) * (σ + 1) ≤ σ * l) (hw0 : 0 ≤ w)
    (hw : w ≤ σ ^ 2 + 1 - σ * r₄) (hh : 2 + r₄ ≤ h) :
    6 * ((n : ℝ) * n - n - ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ l * ρ ^ 2)).card : ℝ) - 1)) ≤
      6 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        4 * (∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ h * ρ ^ 2)).card : ℝ) - 1) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ w * ρ ^ 2)).card : ℝ) - 1)) := by
  classical
  have hρ2 : 0 < ρ ^ 2 := by positivity
  -- a point of the annulus forces `σ² ≤ 1`
  have hσ1 : ∀ _ : Fin n, σ ^ 2 ≤ 1 := fun z ↦ by
    have h1 : σ ^ 2 * ρ ^ 2 ≤ 1 * ρ ^ 2 := by linarith [hloσ z, hhi z]
    exact le_of_mul_le_mul_right h1 hρ2
  have hirr : ∀ a : Fin n, ¬l * ρ ^ 2 < dist (p a) (p a) ^ 2 := fun a hlt ↦ by
    rw [dist_self] at hlt
    have hl0 : 0 ≤ l := by linarith [hσ1 a]
    nlinarith
  -- the window `(wρ², hρ²]` satisfies `wρ² ≤ hρ²` once a point exists
  have hwh : ∀ z : Fin n, w * ρ ^ 2 ≤ h * ρ ^ 2 := fun z ↦ by
    have h3 : w ≤ h := by nlinarith [hσ1 z]
    exact mul_le_mul_of_nonneg_right h3 hρ2.le
  have hwlo := mul_le_mul_of_nonneg_right hw hρ2.le
  have hhup := mul_le_mul_of_nonneg_right hh hρ2.le
  -- Lemma A''(i)–(ii): the apex count with far relation `lρ² < d²` and window `(wρ², hρ²]`
  have hant := six_mul_card_pairs_le_of_apex hp hgp3 hcap
    (fun a b ↦ l * ρ ^ 2 < dist (p a) (p b) ^ 2) hirr
    (fun a b hab ↦ by rwa [dist_comm])
    (fun r ↦ w * ρ ^ 2 < r ^ 2 ∧ r ^ 2 ≤ h * ρ ^ 2)
    (fun h0 ↦ by nlinarith [h0.1])
    (fun z a b hab heq ↦ by
      obtain ⟨h1, h2⟩ := apex_sq_dist_mem_of_sq_far_general hρ hσ.le hr₄ hlr hlσ (hloσ z)
        (hhi z) (hhi a) (hhi b) hab heq
      exact ⟨by linarith, by linarith⟩)
    (fun z a b d hzab hzad _ hab hbd had ↦ false_of_three_pairwise_sq_far_on_circle hρ hσ hL0
      (hloσ z) (hloσ a) (hloσ b) (hloσ d) (hhi a) (hhi b) (hhi d) hzab hzad hab hbd had)
  have hrow := card_offDiag_filter_eq_sum_rows
    (fun a b ↦ l * ρ ^ 2 < dist (p a) (p b) ^ 2) hirr
  rw [hrow] at hant
  push_cast at hant
  -- each row splits into the points within `lρ²` and the points farther than `lρ²`
  have hsplit : ∀ z, (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ l * ρ ^ 2)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ l * ρ ^ 2 < dist (p z) (p q) ^ 2)).card : ℝ) = n := fun z ↦ by
    have hs := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun q ↦ dist (p z) (p q) ^ 2 ≤ l * ρ ^ 2)
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at hs
    exact_mod_cast hs
  -- the window and the ball of squared radius `wρ²` are disjoint parts of the `hρ²` ball
  have hwin : ∀ z, (((Finset.univ : Finset (Fin n)).filter (fun q ↦
      w * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ h * ρ ^ 2)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ w * ρ ^ 2)).card : ℝ) ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ h * ρ ^ 2)).card : ℝ) := fun z ↦ by
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin n)).filter (fun q ↦
          w * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ h * ρ ^ 2))
        ((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ w * ρ ^ 2)) :=
      Finset.disjoint_filter.mpr fun q _ h1 h2 ↦ by linarith [h1.1]
    have hsub : (Finset.univ : Finset (Fin n)).filter (fun q ↦
          w * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ h * ρ ^ 2) ∪
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ w * ρ ^ 2) ⊆
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ h * ρ ^ 2) := by
      intro q hq
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with hq | hq
      · exact hq.2
      · exact hq.trans (hwh z)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hc
    exact_mod_cast hc
  have hsplitSum := Finset.sum_congr rfl
    (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) ↦ hsplit z)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsplitSum
  have hwinSum := Finset.sum_le_sum
    (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) ↦ hwin z)
  rw [Finset.sum_add_distrib] at hwinSum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  linarith

end Esgk
