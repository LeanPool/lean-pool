/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.OneStep
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.GeometryAbsorb

/-!
# Transfer of the weighted bounds one derivative up

The weighted bound at depth `τ` and order `k + 1` from the weighted bounds of orders `≤ k` and a
provisional bound `Y` at order `k + 1`, all at every depth. The one-step estimate is applied on
the backward window of radius `θ τ d / (k + 1)`, which lies one geometric step deeper. The
provisional bound enters with the small coefficient `ε`, which is absorbed in the induction of
`thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A sum over `range (k + 1)` splits off its first term. -/
theorem sum_range_succ_eq_zero_add_Icc (g : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ Finset.range (k + 1), g m = g 0 + ∑ m ∈ Finset.Icc 1 k, g m := by
  have hset : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp)]

/-- For `k ≥ 1` a sum over `range (k + 1)` splits off its first and last terms. -/
theorem sum_range_succ_eq_zero_add_last_add_Icc (g : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ Finset.range (k + 1), g m = g 0 + g k + ∑ m ∈ Finset.Icc 1 (k - 1), g m := by
  rw [sum_range_succ_eq_zero_add_Icc]
  have hset : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
    ext m; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp; omega)]
  ring

/-- The level transfer: from the weighted bounds `A j` at orders `j ≤ k` and a provisional
bound `Y` at order `k + 1`, all at every depth, the order-`k + 1` weighted bound at every depth is
at most `X + ε Y` with `ε = C θ (2 + 6 A₀ + 36 A₁) / (k + 1)`. -/
theorem kahane_level_transfer :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (Ω : Set Vec3) (I : Set ℝ) (R' d s₁ s₂ θ Y : ℝ) (k : ℕ)
    (A F : ℕ → ℝ), IsOpen Ω → IsOpen I → IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
    0 < d → d ≤ 1 → 0 < θ → θ ≤ 1 / 4 → 1 ≤ k → 0 ≤ Y → (∀ j, 0 ≤ A j) →
    (∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      x ∈ Ω ∧ t ∈ I) →
    (∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ (x, t)| ≤ F (γ 0 + γ 1 + γ 2)) →
    (∀ j ≤ k, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = j →
        (∀ i : Fin 3, (τ * d) ^ j * |multiPartial (fun w => u w i) γ (x, t)| ≤ A j) ∧
          (τ * d) ^ j * |multiPartial p γ (x, t)| ≤ A j) →
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 →
        (∀ i : Fin 3, (τ * d) ^ (k + 1) * |multiPartial (fun w => u w i) γ (x, t)| ≤ Y) ∧
          (τ * d) ^ (k + 1) * |multiPartial p γ (x, t)| ≤ Y) →
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 →
        let X := C * (θ / (k + 1) * (F k + 3 * F (k + 1) +
            6 * ∑ m ∈ Finset.Icc 1 k, (k.choose m : ℝ) * (A m * A (k + 1 - m)) +
            18 * ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) * (A (m + 1) * A (k + 1 - m))) +
          2 * (k + 1) * A k / θ)
        let ε := C * θ * (2 + 6 * A 0 + 36 * A 1) / (k + 1)
        (∀ i : Fin 3, (τ * d) ^ (k + 1) * |multiPartial (fun w => u w i) γ (x, t)| ≤
            X + ε * Y) ∧
          (τ * d) ^ (k + 1) * |multiPartial p γ (x, t)| ≤ X + ε * Y := by
  obtain ⟨C, hC, hvel, hpres⟩ := kahane_velocity_pressure_step
  refine ⟨C, hC, ?_⟩
  intro u p f Ω I R' d s₁ s₂ θ Y k A F hΩ hI hsol hd hd1 hθ hθ4 hk hY hA hreg hforce hlev hprov
    τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
  dsimp only
  obtain ⟨hρ, hρ1, hτ', hττ', hwin, hpow⟩ :=
    kahane_window_subset_deeper (R' := R') (s₁ := s₁) (s₂ := s₂) hd hd1 hτ hτ1 hθ hθ4 k
  set ρ : ℝ := θ * τ * d / (k + 1) with hρdef
  set τ' : ℝ := τ * (1 - θ / (k + 1)) with hτ'def
  have hτ'1 : τ' ≤ 1 := hττ'.trans hτ1
  set D : ℝ := τ * d with hDdef
  set D' : ℝ := τ' * d with hD'def
  have hD0 : 0 < D := mul_pos hτ hd
  have hD1 : D ≤ 1 := by nlinarith only [hτ1, hd1, hτ, hd]
  have hD'0 : 0 < D' := mul_pos hτ' hd
  set κ : ℝ := 1 / D' with hκdef
  have hκ0 : 0 < κ := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- weights
  have hDκ : ∀ j : ℕ, j ≤ k + 2 → D ^ j * κ ^ j ≤ 2 := by
    intro j hj
    have h := hpow j hj
    rw [← mul_pow, hκdef, mul_one_div, div_pow, div_le_iff₀ (by positivity)]
    exact h
  have hconv : ∀ (j : ℕ) (a B : ℝ), D' ^ j * a ≤ B → a ≤ B * κ ^ j := by
    intro j a B h
    rw [hκdef, one_div_pow, mul_one_div, le_div_iff₀ (by positivity)]
    linarith only [h]
  -- the window lies at depth `τ'` and in the closed outer region
  have hdeep := hwin x t hx ht₁ ht₂
  have hin0 : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      vec3EuclideanNorm z.1 ≤ R' + d ∧ s₁ - d ^ 2 ≤ z.2 ∧ z.2 ≤ s₂ := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hdeep z hz
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    exact ⟨by nlinarith only [h1, hτ', hd], by nlinarith only [h2, hτ', hd2], h3⟩
  have hwinS : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t ⊆
      spaceTimeSet Ω I := fun z hz => by
    obtain ⟨h1, h2, h3⟩ := hin0 z hz
    exact hreg z.1 z.2 h1 h2 h3
  -- the window bounds
  set c : ℕ → ℝ := fun j => if j ≤ k then A j * κ ^ j else Y * κ ^ j with hcdef
  have hc : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      ∀ γ' : Fin 3 → ℕ, γ' 0 + γ' 1 + γ' 2 ≤ k + 1 → ∀ j : Fin 3,
        |multiPartial (fun w => u w j) γ' z| ≤ c (γ' 0 + γ' 1 + γ' 2) := by
    intro z hz γ' hγ' j
    obtain ⟨h1, h2, h3⟩ := hdeep z hz
    by_cases hle : γ' 0 + γ' 1 + γ' 2 ≤ k
    · have := (hlev _ hle τ' hτ' hτ'1 z.1 z.2 h1 h2 h3 γ' rfl).1 j
      simp only [hcdef, ↓reduceIte, hle]
      exact hconv _ _ _ this
    · have heq : γ' 0 + γ' 1 + γ' 2 = k + 1 := by omega
      have := (hprov τ' hτ' hτ'1 z.1 z.2 h1 h2 h3 γ' heq).1 j
      simp only [hcdef, ↓reduceIte, hle]
      rw [heq]
      exact hconv _ _ _ this
  have hPw : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      ∀ γ' : Fin 3 → ℕ, γ' 0 + γ' 1 + γ' 2 = k + 1 →
        |multiPartial p γ' z| ≤ Y * κ ^ (k + 1) := by
    intro z hz γ' hγ'
    obtain ⟨h1, h2, h3⟩ := hdeep z hz
    exact hconv _ _ _ (hprov τ' hτ' hτ'1 z.1 z.2 h1 h2 h3 γ' hγ').2
  have hQw : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      ∀ γ' : Fin 3 → ℕ, γ' 0 + γ' 1 + γ' 2 = k →
        |multiPartial p γ' z| ≤ A k * κ ^ k := by
    intro z hz γ' hγ'
    obtain ⟨h1, h2, h3⟩ := hdeep z hz
    exact hconv _ _ _ (hlev k le_rfl τ' hτ' hτ'1 z.1 z.2 h1 h2 h3 γ' hγ').2
  have hFw : ∀ (n : ℕ), ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      ∀ γ' : Fin 3 → ℕ, γ' 0 + γ' 1 + γ' 2 = n → ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ' z| ≤ F n := by
    intro n z hz γ' hγ' i
    obtain ⟨h1, h2, h3⟩ := hin0 z hz
    have := hforce z.1 z.2 h1 h2 h3 γ' i
    rwa [hγ'] at this
  have hmem : ((x, t) : Vec3 × ℝ) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t := by
    refine ⟨?_, ?_, le_rfl⟩
    · show vec3EuclideanNorm (x - x) ≤ ρ
      rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le
    · have : 0 ≤ ρ ^ 2 := sq_nonneg ρ
      show t - ρ ^ 2 ≤ t
      linarith only [this]
  have hF0 : ∀ n, 0 ≤ F n := by
    intro n
    have := hFw n (x, t) hmem ![n, 0, 0] (by simp) 0
    exact (abs_nonneg _).trans this
  -- sums in terms of `κ`
  set V : ℝ := ∑ m ∈ Finset.Icc 1 k, (k.choose m : ℝ) * (A m * A (k + 1 - m)) with hV
  set P' : ℝ := ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) * (A (m + 1) * A (k + 1 - m))
    with hP'
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun m _ => by
    have := hA m; have := hA (k + 1 - m); positivity
  have hP'0 : 0 ≤ P' := Finset.sum_nonneg fun m _ => by
    have := hA (m + 1); have := hA (k + 1 - m); positivity
  have hSv : ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c m * c (k + 1 - m)) =
      κ ^ (k + 1) * (A 0 * Y + V) := by
    rw [sum_range_succ_eq_zero_add_Icc, hV, mul_add, Finset.mul_sum]
    have h0 : (k.choose 0 : ℝ) * (c 0 * c (k + 1 - 0)) = κ ^ (k + 1) * (A 0 * Y) := by
      simp only [hcdef, ↓reduceIte, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        Nat.zero_le k, Nat.not_succ_le_self k, pow_zero, mul_one]
      ring
    rw [h0]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmk⟩ := Finset.mem_Icc.1 hm
    simp only [hcdef, ↓reduceIte, hmk, (show k + 1 - m ≤ k by omega)]
    have hpw : κ ^ m * κ ^ (k + 1 - m) = κ ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    linear_combination (↑(k.choose m) * A m * A (k + 1 - m)) * hpw
  have hSp : ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) =
      κ ^ (k + 2) * (2 * (A 1 * Y) + P') := by
    rw [sum_range_succ_eq_zero_add_last_add_Icc _ hk, hP']
    have h0 : (k.choose 0 : ℝ) * (c (0 + 1) * c (k + 1 - 0)) = κ ^ (k + 2) * (A 1 * Y) := by
      simp only [hcdef, ↓reduceIte, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        zero_add,
        hk, Nat.not_succ_le_self k]
      ring
    have hkk : (k.choose k : ℝ) * (c (k + 1) * c (k + 1 - k)) = κ ^ (k + 2) * (A 1 * Y) := by
      simp only [hcdef, ↓reduceIte, Nat.choose_self, Nat.cast_one, one_mul,
        show k + 1 - k = 1 by omega, hk, Nat.not_succ_le_self k]
      ring
    rw [h0, hkk]
    have hmid : ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) =
        ∑ m ∈ Finset.Icc 1 (k - 1), κ ^ (k + 2) * ((k.choose m : ℝ) *
          (A (m + 1) * A (k + 1 - m))) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      obtain ⟨hm1, hmk⟩ := Finset.mem_Icc.1 hm
      simp only [hcdef, ↓reduceIte, (show m + 1 ≤ k by omega),
        (show k + 1 - m ≤ k by omega)]
      have hpw : κ ^ (m + 1) * κ ^ (k + 1 - m) = κ ^ (k + 2) := by
        rw [← pow_add]; congr 1; omega
      linear_combination (↑(k.choose m) * A (m + 1) * A (k + 1 - m)) * hpw
    rw [hmid, ← Finset.mul_sum]
    ring
  -- the four weight factors
  have hρeq : ρ = θ / ((k : ℝ) + 1) * D := by rw [hρdef, hDdef]; ring
  have hθk : 0 ≤ θ / ((k : ℝ) + 1) := by positivity
  have e1 : D ^ (k + 1) * ρ ≤ θ / ((k : ℝ) + 1) := by
    rw [hρeq]
    have : D ^ (k + 1) * D ≤ 1 := by
      rw [← pow_succ]; exact pow_le_one₀ hD0.le hD1
    have h := mul_le_mul_of_nonneg_left this hθk
    linarith only [h]
  have e2 : D ^ (k + 1) * ρ * κ ^ (k + 1) ≤ 2 * (θ / ((k : ℝ) + 1)) := by
    rw [hρeq]
    have h1 := hDκ (k + 1) (by omega)
    have h2 : D ^ (k + 1) * κ ^ (k + 1) * D ≤ 2 * 1 := by
      have := mul_le_mul h1 hD1 hD0.le (by norm_num)
      linarith only [this]
    have h3 := mul_le_mul_of_nonneg_left h2 hθk
    nlinarith only [h3]
  have e4 : D ^ (k + 1) * ρ * κ ^ (k + 2) ≤ 2 * (θ / ((k : ℝ) + 1)) := by
    rw [hρeq]
    have h1 := hDκ (k + 2) le_rfl
    have hid : D ^ (k + 1) * (θ / ((k : ℝ) + 1) * D) * κ ^ (k + 2) =
        θ / ((k : ℝ) + 1) * (D ^ (k + 2) * κ ^ (k + 2)) := by ring
    rw [hid]
    have := mul_le_mul_of_nonneg_left h1 hθk
    linarith only [this]
  have e3 : D ^ (k + 1) * κ ^ k / ρ ≤ 2 * ((k : ℝ) + 1) / θ := by
    rw [hρeq]
    have h1 := hDκ k (by omega)
    have hid : D ^ (k + 1) * κ ^ k / (θ / ((k : ℝ) + 1) * D) =
        ((k : ℝ) + 1) / θ * (D ^ k * κ ^ k) := by
      field_simp
      ring
    rw [hid]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1) / θ)
    have e : ((k : ℝ) + 1) / θ * 2 = 2 * ((k : ℝ) + 1) / θ := by ring
    linarith only [this, e]
  have hA0 := hA 0
  have hA1 := hA 1
  have hAk := hA k
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hDk0 : 0 ≤ D ^ (k + 1) := by positivity
  refine ⟨fun i => ?_, ?_⟩
  · have hvb := hvel u p f Ω I hΩ hI hsol x t ρ k c (Y * κ ^ (k + 1)) (F k) hρ hρ1 hwinS hc hPw
      (hFw k) γ hγ i
    rw [hSv] at hvb
    have hck : c k = A k * κ ^ k := by simp only [hcdef, ↓reduceIte, le_refl k]
    rw [hck] at hvb
    have h1 := mul_le_mul_of_nonneg_left hvb hDk0
    have hid : D ^ (k + 1) * (C * (ρ * (F k + 3 * (κ ^ (k + 1) * (A 0 * Y + V)) +
        Y * κ ^ (k + 1)) + A k * κ ^ k / ρ)) =
        C * ((D ^ (k + 1) * ρ) * F k + 3 * (D ^ (k + 1) * ρ * κ ^ (k + 1)) * (A 0 * Y + V) +
          (D ^ (k + 1) * ρ * κ ^ (k + 1)) * Y + (D ^ (k + 1) * κ ^ k / ρ) * A k) := by
      ring
    rw [hid] at h1
    have g1 := mul_le_mul_of_nonneg_right e1 (hF0 k)
    have g2 := mul_le_mul_of_nonneg_right e2 (by positivity : (0 : ℝ) ≤ A 0 * Y + V)
    have g3 := mul_le_mul_of_nonneg_right e2 hY
    have g4 := mul_le_mul_of_nonneg_right e3 hAk
    have hsum : (D ^ (k + 1) * ρ) * F k + 3 * (D ^ (k + 1) * ρ * κ ^ (k + 1)) * (A 0 * Y + V) +
        (D ^ (k + 1) * ρ * κ ^ (k + 1)) * Y + (D ^ (k + 1) * κ ^ k / ρ) * A k ≤
        θ / ((k : ℝ) + 1) * F k + 3 * (2 * (θ / ((k : ℝ) + 1))) * (A 0 * Y + V) +
          2 * (θ / ((k : ℝ) + 1)) * Y + 2 * ((k : ℝ) + 1) / θ * A k := by
      linarith only [g1, g2, g3, g4]
    have h2 := mul_le_mul_of_nonneg_left hsum hC0
    have hgap : C * (θ / ((k : ℝ) + 1) * (F k + 3 * F (k + 1) + 6 * V + 18 * P') +
        2 * ((k : ℝ) + 1) * A k / θ) + C * θ * (2 + 6 * A 0 + 36 * A 1) / ((k : ℝ) + 1) * Y -
        C * (θ / ((k : ℝ) + 1) * F k + 3 * (2 * (θ / ((k : ℝ) + 1))) * (A 0 * Y + V) +
          2 * (θ / ((k : ℝ) + 1)) * Y + 2 * ((k : ℝ) + 1) / θ * A k) =
        C * (θ / ((k : ℝ) + 1)) * (3 * F (k + 1) + 18 * P' + 36 * (A 1 * Y)) := by
      field_simp
      ring
    have hgap0 : 0 ≤ C * (θ / ((k : ℝ) + 1)) * (3 * F (k + 1) + 18 * P' + 36 * (A 1 * Y)) := by
      have := hF0 (k + 1); positivity
    linarith only [h1, h2, hgap, hgap0]
  · have htI : t ∈ I := (hwinS hmem).2
    have hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → y ∈ Ω := fun y hy =>
      (hwinS (show ((y, t) : Vec3 × ℝ) ∈ _ from ⟨hy, hmem.2⟩)).1
    have hmemy : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ((y, t) : Vec3 × ℝ) ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t :=
      fun y hy => ⟨hy, hmem.2⟩
    have hpb := hpres u p f Ω I hΩ hI hsol x t ρ k c (A k * κ ^ k) (F (k + 1)) hρ hρ1 htI hball
      (fun y hy => hc (y, t) (hmemy y hy)) (fun y hy => hQw (y, t) (hmemy y hy))
      (fun y hy => hFw (k + 1) (y, t) (hmemy y hy)) γ hγ
    rw [hSp] at hpb
    have h1 := mul_le_mul_of_nonneg_left hpb hDk0
    have hid : D ^ (k + 1) * (C * (ρ * (3 * F (k + 1) + 9 * (κ ^ (k + 2) *
        (2 * (A 1 * Y) + P'))) + A k * κ ^ k / ρ)) =
        C * (3 * (D ^ (k + 1) * ρ) * F (k + 1) + 9 * (D ^ (k + 1) * ρ * κ ^ (k + 2)) *
          (2 * (A 1 * Y) + P') + (D ^ (k + 1) * κ ^ k / ρ) * A k) := by
      ring
    rw [hid] at h1
    have g1 := mul_le_mul_of_nonneg_right e1 (hF0 (k + 1))
    have g2 := mul_le_mul_of_nonneg_right e4 (by positivity : (0 : ℝ) ≤ 2 * (A 1 * Y) + P')
    have g4 := mul_le_mul_of_nonneg_right e3 hAk
    have hsum : 3 * (D ^ (k + 1) * ρ) * F (k + 1) + 9 * (D ^ (k + 1) * ρ * κ ^ (k + 2)) *
        (2 * (A 1 * Y) + P') + (D ^ (k + 1) * κ ^ k / ρ) * A k ≤
        3 * (θ / ((k : ℝ) + 1)) * F (k + 1) + 9 * (2 * (θ / ((k : ℝ) + 1))) *
          (2 * (A 1 * Y) + P') + 2 * ((k : ℝ) + 1) / θ * A k := by
      linarith only [g1, g2, g4]
    have h2 := mul_le_mul_of_nonneg_left hsum hC0
    have hgap : C * (θ / ((k : ℝ) + 1) * (F k + 3 * F (k + 1) + 6 * V + 18 * P') +
        2 * ((k : ℝ) + 1) * A k / θ) + C * θ * (2 + 6 * A 0 + 36 * A 1) / ((k : ℝ) + 1) * Y -
        C * (3 * (θ / ((k : ℝ) + 1)) * F (k + 1) + 9 * (2 * (θ / ((k : ℝ) + 1))) *
          (2 * (A 1 * Y) + P') + 2 * ((k : ℝ) + 1) / θ * A k) =
        C * (θ / ((k : ℝ) + 1)) * (F k + 6 * V + 2 * Y + 6 * (A 0 * Y)) := by
      field_simp
      ring
    have hgap0 : 0 ≤ C * (θ / ((k : ℝ) + 1)) * (F k + 6 * V + 2 * Y + 6 * (A 0 * Y)) := by
      have := hF0 k; positivity
    linarith only [h1, h2, hgap, hgap0]

end CIV
