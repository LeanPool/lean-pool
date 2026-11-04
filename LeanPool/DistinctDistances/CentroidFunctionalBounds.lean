/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnulusClusterGeometry
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Centroid functional bounds in a thin annulus

Formalizes the geometric lemmas of Theorem S★ in
`docs/results/explicit-constant-gain-1-85-2026-10-20.md` (§5.3 Lemma A′(i), §5.4 Lemma T,
§5.5 Lemma F). The points lie in the annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` about their centroid
`c`, where `σ` is a lower bound for the doc's `s = √(1 - x)`. All statements are in
unscaled coordinates; the doc's normalized point is `(p_q - c)/ρ`.

* Lemma A′(i): an apex of a pair at squared distance more than `3ρ²` has squared radius in
  `((σ² - σ + 1)ρ², 3ρ²)` when `1/2 ≤ σ` (`apex_sq_dist_mem_of_sq_far_sharp`).
* Lemma F: with the unit-direction functional `F(q) = 1 + ⟨p_q - c, (p_z - c)/|p_z - c|⟩/ρ`,
  a closed ball of radius `θ` about `p_z` holds at most `n / (1 + σ - θ²/(2σρ²))` points
  (`configClosedBall_card_mul_le_unit_direction`).
* Lemma T: the same functional gives the centroid layer-cake bound
  (`centroid_layer_cake_le`); the discrete layer cake turns step lower bounds on ball counts
  into a lower bound for its sum (`discrete_layer_cake_le`, `discrete_layer_cake_le_six`);
  three disjoint balls about an isosceles triple lie in one larger ball
  (`configClosedBall_card_add_add_le_of_isosceles`); and the layer-cake gap at `σ` cannot be
  positive (`false_of_centroid_layer_cake_gap_pos`).

The final assembly of `D(P) > (1/3 + 1/85)n` is not in this module.
-/

@[expose] public section

namespace Esgk

open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### Lemma A′(i): the sharp apex range -/

/-- Lemma A′(i): in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` with `1/2 ≤ σ`, an apex `z` of a pair
`a, b` at squared distance more than `3ρ²` has squared radius `dist z a²` strictly between
`(σ² - σ + 1)ρ²` and `3ρ²`. Only the upper annulus bound is needed for `a` and `b`. -/
theorem apex_sq_dist_mem_of_sq_far_sharp {c z a b : Point} {ρ σ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ σ) (hz : σ ^ 2 * ρ ^ 2 ≤ dist z c ^ 2) (hz1 : dist z c ^ 2 ≤ ρ ^ 2)
    (ha1 : dist a c ^ 2 ≤ ρ ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2)
    (hab : 3 * ρ ^ 2 < dist a b ^ 2) (heq : dist z a = dist z b) :
    (σ ^ 2 - σ + 1) * ρ ^ 2 < dist z a ^ 2 ∧ dist z a ^ 2 < 3 * ρ ^ 2 := by
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
  -- parallelogram law: `‖A + B‖² = 2(‖A‖² + ‖B‖²) - ‖A - B‖² < ρ²`
  have hpar : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have hw2 : ‖A + B‖ ^ 2 < ρ ^ 2 := by linarith
  have hw : ‖A + B‖ < ρ := (abs_lt_of_sq_lt_sq' hw2 hρ.le).2
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
  · -- `4r² > (2‖Z‖ - ‖A + B‖)² + 3ρ² ≥ (2σ - 1)²ρ² + 3ρ²`
    have hk0 : 0 ≤ (2 * σ - 1) * ρ := mul_nonneg (by linarith) hρ.le
    have hk : (2 * σ - 1) * ρ ≤ 2 * ‖Z‖ - ‖A + B‖ := by nlinarith
    have hsq := mul_le_mul hk hk hk0 (hk0.trans hk)
    nlinarith
  · -- `2r² ≤ 2ρ² + 2ρ² + 2‖Z‖‖A + B‖ < 6ρ²`
    have hzw : ‖Z‖ * ‖A + B‖ < ρ ^ 2 := by
      calc ‖Z‖ * ‖A + B‖ ≤ ρ * ‖A + B‖ := mul_le_mul_of_nonneg_right hζ1 hw0
        _ < ρ * ρ := mul_lt_mul_of_pos_left hw hρ
        _ = ρ ^ 2 := by ring
    nlinarith

/-! ### The unit-direction centroid functional -/

/-- Membership in `ConfigClosedBall` is the distance bound. -/
private lemma mem_configClosedBall_iff {p : Config n} {i j : Fin n} {t : ℝ} :
    j ∈ ConfigClosedBall p i t ↔ dist (p i) (p j) ≤ t := by
  simp [ConfigClosedBall]

/-- Twice a centred inner product, in terms of squared distances. -/
private lemma two_mul_inner_sub_center (u w c : Point) :
    2 * ⟪u - c, w - c⟫ = dist u c ^ 2 + dist w c ^ 2 - dist u w ^ 2 := by
  have h := norm_sub_sq_real (u - c) (w - c)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm] at h
  linarith

/-- The unit-direction centroid functional about `p z`, scaled by `ρ‖p z - c‖`: the values
`ρ‖p z - c‖ + ⟪p q - c, p z - c⟫` are nonnegative and sum to `nρ‖p z - c‖`. -/
private lemma unit_direction_functional {p : Config n} {c : Point} {ρ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (z : Fin n) :
    (∀ q, 0 ≤ ρ * ‖p z - c‖ + ⟪p q - c, p z - c⟫) ∧
      ∑ q, (ρ * ‖p z - c‖ + ⟪p q - c, p z - c⟫) = n * (ρ * ‖p z - c‖) := by
  constructor
  · intro q
    have hq : ‖p q - c‖ ≤ ρ := by
      rw [← dist_eq_norm]; exact (abs_le_of_sq_le_sq' (hhi q) hρ.le).2
    have h1 := (abs_le.mp (abs_real_inner_le_norm (p q - c) (p z - c))).1
    have h2 := mul_le_mul_of_nonneg_right hq (norm_nonneg (p z - c))
    linarith
  · rw [Finset.sum_add_distrib, ← sum_inner, hsum, inner_zero_left, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_zero]

/-! ### Lemma F: the unit-functional ball bound -/

/-- Lemma F, the ball count: in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` about the centroid `c`,
with `0 < σ`, the number of points within `θ` of a point `p z`, times
`1 + σ - θ²/(2σρ²)`, is at most `n`. The proof uses the unit-direction functional
`1 + ⟪p q - c, p z - c⟫/(ρ‖p z - c‖)`, which is nonnegative and sums to `n`. -/
theorem configClosedBall_card_mul_le_unit_direction {p : Config n} {c : Point} {ρ σ θ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n) :
    ((ConfigClosedBall p z θ).card : ℝ) * (1 + σ - θ ^ 2 / (2 * σ * ρ ^ 2)) ≤ n := by
  obtain ⟨hf0, hfsum⟩ := unit_direction_functional hsum hρ hhi z
  set f : Fin n → ℝ := fun q ↦ ρ * ‖p z - c‖ + ⟪p q - c, p z - c⟫ with hf
  have hAd : ‖p z - c‖ = dist (p z) c := (dist_eq_norm _ _).symm
  set A := ‖p z - c‖ with hA
  have hσρ : σ * ρ ≤ A := by
    rw [hAd]; exact (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hlo z) dist_nonneg).2
  have hA0 : 0 < A := (mul_pos hσ hρ).trans_le hσρ
  set w := θ ^ 2 / (2 * σ * ρ ^ 2) with hw
  have hw' : 2 * σ * ρ ^ 2 * w = θ ^ 2 := mul_div_cancel₀ _ (by positivity)
  -- pointwise bound on the ball
  have hpt : ∀ q ∈ ConfigClosedBall p z θ, ρ * A * (1 + σ - w) ≤ f q := by
    intro q hq
    rw [mem_configClosedBall_iff] at hq
    have hd : dist (p q) (p z) ^ 2 ≤ θ ^ 2 := by
      rw [dist_comm]; exact pow_le_pow_left₀ dist_nonneg hq 2
    have hin := two_mul_inner_sub_center (p q) (p z) c
    rw [← hAd] at hin
    have hlow : ρ * A * (1 + σ - w) ≤ ρ * A + (σ ^ 2 * ρ ^ 2 + A ^ 2 - θ ^ 2) / 2 := by
      have hpos : 0 < 2 * σ * ρ := by positivity
      refine le_of_mul_le_mul_left ?_ hpos
      have e1 : 2 * σ * ρ * (ρ * A * (1 + σ - w)) =
          2 * σ * ρ ^ 2 * A * (1 + σ) - A * θ ^ 2 := by
        linear_combination (-A) * hw'
      rw [e1]
      have k1 : 0 ≤ σ * ρ * (A - σ * ρ) ^ 2 := by positivity
      have k2 : 0 ≤ θ ^ 2 * (A - σ * ρ) := mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hσρ)
      nlinarith
    simp only [hf]
    linarith [hlo q]
  have hsZ := Finset.card_nsmul_le_sum _ f _ hpt
  rw [nsmul_eq_mul] at hsZ
  have hup := Finset.sum_le_univ_sum_of_nonneg (s := ConfigClosedBall p z θ) hf0
  have hmain : ((ConfigClosedBall p z θ).card : ℝ) * (1 + σ - w) * (ρ * A) ≤
      (n : ℝ) * (ρ * A) := by
    calc ((ConfigClosedBall p z θ).card : ℝ) * (1 + σ - w) * (ρ * A)
        = ((ConfigClosedBall p z θ).card : ℝ) * (ρ * A * (1 + σ - w)) := by ring
      _ ≤ ∑ q, f q := hsZ.trans hup
      _ = (n : ℝ) * (ρ * A) := hfsum
  exact le_of_mul_le_mul_right hmain (mul_pos hρ hA0)

/-! ### Lemma T: the centroid layer cake -/

/-- Lemma T, the centroid layer-cake bound: in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` about
the centroid `c`, a point `p z` with `dist (p z) c = aρ` satisfies
`((a + 1)² + σ² - 4) · #{q : |p z - p q|² ≤ 3ρ²} · ρ² + Σ_q max(0, 3ρ² - |p z - p q|²)
≤ 2anρ²`. This is the doc's bound multiplied by `ρ²`. -/
theorem centroid_layer_cake_le {p : Config n} {c : Point} {ρ σ a : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) {z : Fin n} (ha : dist (p z) c = a * ρ) :
    ((a + 1) ^ 2 + σ ^ 2 - 4) * (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2)).card : ℝ) * ρ ^ 2 +
      ∑ q, max 0 (3 * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤ 2 * a * n * ρ ^ 2 := by
  classical
  obtain ⟨hf0, hfsum⟩ := unit_direction_functional hsum hρ hhi z
  have hAd : ‖p z - c‖ = a * ρ := by rw [← dist_eq_norm, ha]
  rw [hAd] at hf0 hfsum
  set S := (Finset.univ : Finset (Fin n)).filter
    (fun q ↦ dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2) with hS
  set K := ((a + 1) ^ 2 + σ ^ 2 - 4) * ρ ^ 2 with hK
  have hpt : ∀ q, (if q ∈ S then K else 0) + max 0 (3 * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤
      2 * (ρ * (a * ρ) + ⟪p q - c, p z - c⟫) := by
    intro q
    by_cases hq : q ∈ S
    · rw [ite_eq_left hq]
      have hq' : dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2 := (Finset.mem_filter.mp hq).2
      rw [max_eq_right (by linarith)]
      have hin := two_mul_inner_sub_center (p q) (p z) c
      rw [ha, dist_comm (p q) (p z)] at hin
      simp only [hK]
      nlinarith [hlo q]
    · rw [ite_eq_right hq]
      have hq' : 3 * ρ ^ 2 < dist (p z) (p q) ^ 2 := by
        by_contra h
        exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩)
      rw [max_eq_left (by linarith)]
      linarith [hf0 q]
  have hsum' := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) ↦ hpt q)
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, hfsum] at hsum'
  simp only [hK] at hsum'
  linarith

/-! ### The discrete layer cake -/

/-- Telescoping: for `τ` nondecreasing on `0, …, k`, the increments `τ (i+1) - τ i` over the
indices `i < k` with `x ≤ τ i` sum to at most `max 0 (τ k - x)`. -/
private lemma sum_ite_increment_le_max {k : ℕ} (τ : ℕ → ℝ) (hτ : ∀ i < k, τ i ≤ τ (i + 1))
    (x : ℝ) :
    ∑ i ∈ Finset.range k, (if x ≤ τ i then τ (i + 1) - τ i else 0) ≤ max 0 (τ k - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi ↦ hτ i (by omega))
    have hk := hτ k (by omega)
    split_ifs with hx
    · rw [max_eq_right (by linarith)] at ih'
      linarith [le_max_right 0 (τ (k + 1) - x)]
    · rw [max_eq_left (by linarith)] at ih'
      linarith [le_max_left 0 (τ (k + 1) - x)]

/-- The discrete layer cake: for squared radii `τ 0 ≤ τ 1 ≤ … ≤ τ k` and reals `ν i` bounded
by the number of points at squared distance at most `τ i` from `p z`,
`Σ_{i<k} ν i (τ (i+1) - τ i) ≤ Σ_q max(0, τ k - |p z - p q|²)`. No sign condition on `ν` or
`τ` is needed. -/
theorem discrete_layer_cake_le {p : Config n} (z : Fin n) {k : ℕ} (τ ν : ℕ → ℝ)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1))
    (hν : ∀ i < k, ν i ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i)).card : ℝ)) :
    ∑ i ∈ Finset.range k, ν i * (τ (i + 1) - τ i) ≤
      ∑ q, max 0 (τ k - dist (p z) (p q) ^ 2) := by
  classical
  calc ∑ i ∈ Finset.range k, ν i * (τ (i + 1) - τ i)
      ≤ ∑ i ∈ Finset.range k, (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i)).card : ℝ) * (τ (i + 1) - τ i) :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_right
          (hν i (Finset.mem_range.mp hi)) (sub_nonneg.mpr (hτ i (Finset.mem_range.mp hi)))
    _ = ∑ i ∈ Finset.range k, ∑ q,
          (if dist (p z) (p q) ^ 2 ≤ τ i then τ (i + 1) - τ i else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ q, ∑ i ∈ Finset.range k,
          (if dist (p z) (p q) ^ 2 ≤ τ i then τ (i + 1) - τ i else 0) := Finset.sum_comm
    _ ≤ ∑ q, max 0 (τ k - dist (p z) (p q) ^ 2) :=
        Finset.sum_le_sum fun q _ ↦ sum_ite_increment_le_max τ hτ _

/-- The discrete layer cake with six explicit pieces: for squared radii
`τ₀ ≤ τ₁ ≤ … ≤ τ₆` and reals `νᵢ` bounded by the number of points at squared distance at
most `τᵢ` from `p z`, `Σ_{i<6} νᵢ (τᵢ₊₁ - τᵢ) ≤ Σ_q max(0, τ₆ - |p z - p q|²)`. -/
theorem discrete_layer_cake_le_six {p : Config n} (z : Fin n)
    {τ₀ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ ν₀ ν₁ ν₂ ν₃ ν₄ ν₅ : ℝ}
    (h₀ : τ₀ ≤ τ₁) (h₁ : τ₁ ≤ τ₂) (h₂ : τ₂ ≤ τ₃) (h₃ : τ₃ ≤ τ₄) (h₄ : τ₄ ≤ τ₅)
    (h₅ : τ₅ ≤ τ₆)
    (hν₀ : ν₀ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₀)).card : ℝ))
    (hν₁ : ν₁ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₁)).card : ℝ))
    (hν₂ : ν₂ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₂)).card : ℝ))
    (hν₃ : ν₃ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₃)).card : ℝ))
    (hν₄ : ν₄ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₄)).card : ℝ))
    (hν₅ : ν₅ ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ₅)).card : ℝ)) :
    ν₀ * (τ₁ - τ₀) + ν₁ * (τ₂ - τ₁) + ν₂ * (τ₃ - τ₂) + ν₃ * (τ₄ - τ₃) +
        ν₄ * (τ₅ - τ₄) + ν₅ * (τ₆ - τ₅) ≤
      ∑ q, max 0 (τ₆ - dist (p z) (p q) ^ 2) := by
  have h := discrete_layer_cake_le z (k := 6) (fun i ↦ [τ₀, τ₁, τ₂, τ₃, τ₄, τ₅, τ₆].getD i 0)
    (fun i ↦ [ν₀, ν₁, ν₂, ν₃, ν₄, ν₅].getD i 0)
    (fun i hi ↦ by interval_cases i <;> simpa)
    (fun i hi ↦ by interval_cases i <;> simpa)
  simpa [Finset.sum_range_succ] using h

/-! ### Three disjoint balls -/

/-- Balls of radius `t` about two points farther apart than `2t` are disjoint. -/
private lemma configClosedBall_disjoint_of_two_mul_lt {p : Config n} {i j : Fin n} {t : ℝ}
    (h : 2 * t < dist (p i) (p j)) :
    Disjoint (ConfigClosedBall p i t) (ConfigClosedBall p j t) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [mem_configClosedBall_iff] at hki hkj
  have htri := dist_triangle (p i) (p k) (p j)
  rw [dist_comm (p k) (p j)] at htri
  linarith

/-- A closed ball of nonnegative radius `t` is the set of points at squared distance at most
`t²`. -/
theorem configClosedBall_eq_filter_sq_le (p : Config n) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ConfigClosedBall p i t =
      (Finset.univ : Finset (Fin n)).filter (fun j ↦ dist (p i) (p j) ^ 2 ≤ t ^ 2) := by
  ext j
  simp only [ConfigClosedBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (sq_le_sq₀ dist_nonneg ht).symm

/-- Three disjoint balls: if `|p z - p a| = |p z - p b| ≤ T`, `2t < |p z - p a|` and
`2t < |p a - p b|`, the balls of radius `t` about `p z`, `p a` and `p b` are disjoint and lie in
the ball of radius `T + t` about `p z`, so their counts add up to at most its count. -/
theorem configClosedBall_card_add_add_le_of_isosceles {p : Config n} {z a b : Fin n}
    {t T : ℝ} (hzab : dist (p z) (p a) = dist (p z) (p b)) (hza : dist (p z) (p a) ≤ T)
    (ht : 2 * t < dist (p z) (p a)) (hab : 2 * t < dist (p a) (p b)) :
    (ConfigClosedBall p z t).card + (ConfigClosedBall p a t).card +
        (ConfigClosedBall p b t).card ≤ (ConfigClosedBall p z (T + t)).card := by
  have hzb : 2 * t < dist (p z) (p b) := hzab ▸ ht
  have hdZA := configClosedBall_disjoint_of_two_mul_lt ht
  have hdZB := configClosedBall_disjoint_of_two_mul_lt hzb
  have hdAB := configClosedBall_disjoint_of_two_mul_lt hab
  rw [← Finset.card_union_of_disjoint hdZA,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdZB, hdAB⟩)]
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_union, mem_configClosedBall_iff] at hq ⊢
  have hza0 : 0 ≤ dist (p z) (p a) := dist_nonneg
  rcases hq with (hq | hq) | hq
  · linarith
  · linarith [dist_triangle (p z) (p a) (p q)]
  · linarith [dist_triangle (p z) (p b) (p q)]

/-! ### Lemma T, packaged -/

/-- Lemma T, packaged for one point `p z`: in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` about the
centroid `c`, with `0 ≤ σ`, let `A` bound the number of points farther than `√3 ρ` from
`p z`, with `A ≤ σ(n - A)`, let `(σ + 1)² + σ² - 4 ≥ 0`, and let
`Cρ² ≤ Σ_q max(0, 3ρ² - |p z - p q|²)`. Then the layer-cake gap
`((σ + 1)² + σ² - 4)(n - A) + C - 2σn` is not positive. -/
theorem false_of_centroid_layer_cake_gap_pos {p : Config n} {c : Point} {ρ σ A C : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n)
    (hfar : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ 3 * ρ ^ 2 < dist (p z) (p q) ^ 2)).card : ℝ) ≤ A)
    (hA : A ≤ σ * (n - A)) (hcoef : 0 ≤ (σ + 1) ^ 2 + σ ^ 2 - 4)
    (hC : C * ρ ^ 2 ≤ ∑ q, max 0 (3 * ρ ^ 2 - dist (p z) (p q) ^ 2))
    (hG : 0 < ((σ + 1) ^ 2 + σ ^ 2 - 4) * (n - A) + C - 2 * σ * n) : False := by
  classical
  set a := dist (p z) c / ρ with ha_def
  have ha : dist (p z) c = a * ρ := by rw [ha_def, div_mul_cancel₀ _ hρ.ne']
  have hlay := centroid_layer_cake_le hsum hρ hlo hhi ha
  have hσa : σ ≤ a := by
    have h1 : σ * ρ ≤ dist (p z) c :=
      (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hlo z) dist_nonneg).2
    rw [ha] at h1
    exact le_of_mul_le_mul_right h1 hρ
  -- the near count is at least `n - A`
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun q ↦ dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at hsplit
  have hsplitR : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ 3 * ρ ^ 2 < dist (p z) (p q) ^ 2)).card : ℝ) = n := by
    exact_mod_cast hsplit
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnA : 0 ≤ (n : ℝ) - A := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hσ (le_of_lt (not_le.mp h))
    linarith
  have hS : (n : ℝ) - A ≤ (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ 3 * ρ ^ 2)).card : ℝ) := by linarith
  -- the coefficient at `a` is at least the coefficient at `σ`
  have hcoef_a : (σ + 1) ^ 2 + σ ^ 2 - 4 ≤ (a + 1) ^ 2 + σ ^ 2 - 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hσa) (by linarith : 0 ≤ a + σ + 2)]
  have h1 := mul_le_mul_of_nonneg_left hS (hcoef.trans hcoef_a)
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ρ)
  -- `G(a) ≤ 0`
  have hGa : (((a + 1) ^ 2 + σ ^ 2 - 4) * (n - A) + C) * ρ ^ 2 ≤ (2 * a * n) * ρ ^ 2 := by
    nlinarith
  have hGa' := le_of_mul_le_mul_right hGa (by positivity)
  -- `G(a) - G(σ) = (a - σ)²(n - A) + 2(a - σ)(σ(n - A) - A) ≥ 0`
  have h3 : 0 ≤ (a - σ) ^ 2 * (n - A) := mul_nonneg (sq_nonneg _) hnA
  have h4 : 0 ≤ (a - σ) * (σ * (n - A) - A) :=
    mul_nonneg (sub_nonneg.mpr hσa) (by linarith)
  nlinarith

end Esgk
