/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.BlockLower
public import LeanPool.RunsOfMultiples.LowerEstimates
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Runs of multiples: the lower bound

For every large `n` there is an `n`-element set `S` of positive integers with
`∑ a ∈ S, kVal S a ≥ c n log n log log n`.

Route (see `docs/runs-of-multiples.pdf`, §2):
* `Sm X y` is the set of `y`-smooth numbers in `[1, X]`. If `a ∈ Sm X y` then `j * a ∈ Sm (X * y) y`
  for all `1 ≤ j ≤ y`.
* Rankin's trick (via Mathlib's Euler product over smooth numbers) with `σ = 1 / log y` gives
  `|Sm (y ^ K) y| ≤ exp (K + C₀ y / log y)`.
* Pigeonhole over `X_i = y ^ i`, `i ≤ K = ⌈y / log y⌉`, gives a block `B = Sm (y ^ (i+1)) y`
  with `|B| ≤ exp (C₂ y / log y)` containing `G = Sm (y ^ i) y`, `|G| ≥ δ |B|`, all of whose
  first `y` multiples lie in `B`.
* `⌊n / |B|⌋` scaled copies `M ^ j • B` plus padding give the set for every large `n`.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-! ### Elementary analytic estimates -/

lemma inv_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) : (1 - exp (-u))⁻¹ ≤ exp (1 / u) := by
  have h1 : 1 + u ≤ exp u := by linarith [add_one_le_exp u]
  have h2 : exp (-u) ≤ (1 + u)⁻¹ := by rw [exp_neg]; exact inv_anti₀ (by linarith) h1
  have h3 : u / (1 + u) ≤ 1 - exp (-u) := by
    have : u / (1 + u) = 1 - (1 + u)⁻¹ := by field_simp; ring
    linarith
  have h4 : 0 < u / (1 + u) := by positivity
  calc (1 - exp (-u))⁻¹ ≤ (u / (1 + u))⁻¹ := inv_anti₀ h4 h3
    _ = 1 / u + 1 := by field_simp
    _ ≤ exp (1 / u) := add_one_le_exp _

/-! ### Smooth numbers and Rankin's bound -/

/-- The `y`-smooth numbers in `[1, X]`. -/
def Sm (X y : ℕ) : Finset ℕ := Nat.smoothNumbersUpTo X (y + 1)

lemma pos_of_mem_Sm {X y m : ℕ} (hm : m ∈ Sm X y) : 0 < m :=
  Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.1 hm).2)

lemma one_mem_Sm {X y : ℕ} (hX : 1 ≤ X) : 1 ∈ Sm X y :=
  Nat.mem_smoothNumbersUpTo.2 ⟨hX, Nat.mem_smoothNumbers.2 ⟨one_ne_zero, fun p hp => by simp at hp⟩⟩

lemma Sm_mono {X X' y : ℕ} (h : X ≤ X') : Sm X y ⊆ Sm X' y := by
  intro m hm
  rw [Sm, Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans h, hm.2⟩

lemma mul_mem_Sm {X y a j : ℕ} (ha : a ∈ Sm X y) (hj1 : 1 ≤ j) (hjy : j ≤ y) :
    j * a ∈ Sm (X * y) y := by
  rw [Sm, Nat.mem_smoothNumbersUpTo] at ha ⊢
  refine ⟨?_, Nat.mul_mem_smoothNumbers (Nat.mem_smoothNumbers_of_lt hj1 (by omega)) ha.2⟩
  rw [mul_comm X y]
  exact Nat.mul_le_mul hjy ha.1

/-- The completely multiplicative function `m ↦ m ^ (-σ)`. -/
noncomputable def rpowHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by push_cast; exact Real.mul_rpow m.cast_nonneg n.cast_nonneg

lemma rankin_sum (σ : ℝ) (hσ : 0 < σ) (y X : ℕ) :
    ∑ m ∈ Sm X y, (m : ℝ) ^ (-σ) ≤ ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowHom σ) ?_ (y + 1)).2
  · have h' := (hasSum_subtype_iff_indicator (f := fun m => rpowHom σ m)).mp h
    refine le_trans (le_of_eq ?_) (sum_le_hasSum (Nat.smoothNumbersUpTo X (y + 1)) ?_ h')
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [Set.indicator_of_mem (Nat.mem_smoothNumbersUpTo.mp hm).2]
      rfl
    · intro i _
      apply Set.indicator_nonneg
      intro j _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro p hp
    simp only [rpowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- Rankin's trick: `|Sm X y| ≤ X ^ σ ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`. -/
lemma rankin_card (σ : ℝ) (hσ : 0 < σ) (y X : ℕ) (hX : 0 < X) :
    ((Sm X y).card : ℝ) ≤ (X : ℝ) ^ σ * ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have h1 : ∀ m ∈ Sm X y, (X : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast pos_of_mem_Sm hm
    rw [Sm, Nat.mem_smoothNumbersUpTo] at hm
    exact Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hm.1) (by linarith)
  have h2 : ((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    calc ((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ) = ∑ m ∈ Sm X y, (X : ℝ) ^ (-σ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Sm X y, (m : ℝ) ^ (-σ) := sum_le_sum h1
      _ ≤ _ := rankin_sum σ hσ y X
  have h3 : (X : ℝ) ^ σ * (X : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hXpos]; simp
  calc ((Sm X y).card : ℝ) = ((Sm X y).card : ℝ) * ((X : ℝ) ^ σ * (X : ℝ) ^ (-σ)) := by
        rw [h3, mul_one]
    _ = (X : ℝ) ^ σ * (((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Each Euler factor with `σ = 1 / log y` is at most `exp (log y / log p)`. -/
lemma factor_le {y p : ℕ} (hy : 2 ≤ y) (hp : 2 ≤ p) :
    (1 - (p : ℝ) ^ (-(1 / log y)))⁻¹ ≤ exp (log y / log p) := by
  have hly : 0 < log (y : ℝ) := log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast (show 1 < p by omega))
  have hpos : (0 : ℝ) < p := by positivity
  have : (p : ℝ) ^ (-(1 / log y)) = exp (-(log p / log y)) := by
    rw [rpow_def_of_pos hpos]; congr 1; ring
  rw [this]
  have := inv_one_sub_exp_neg_le (div_pos hlp hly)
  rwa [one_div_div] at this

/-- Splitting the primes at `√y`. -/
lemma sum_log_div_le (y : ℕ) (hy : 2 ≤ y) :
    ∑ p ∈ (y + 1).primesBelow, log y / log p ≤
      2 * (y + 1).primesBelow.card + Nat.sqrt y * (log y / log 2) := by
  have hly : 0 < log (y : ℝ) := log_pos (by exact_mod_cast (show 1 < y by omega))
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set P := (y + 1).primesBelow with hP
  rw [← sum_filter_add_sum_filter_not P (fun p => p * p ≤ y)]
  have hsmall : ∑ p ∈ P with p * p ≤ y, log y / log p ≤ Nat.sqrt y * (log y / log 2) := by
    have hcard : (P.filter (fun p => p * p ≤ y)).card ≤ Nat.sqrt y := by
      calc (P.filter (fun p => p * p ≤ y)).card ≤ (Icc 1 (Nat.sqrt y)).card := by
            refine card_le_card fun p hp => ?_
            rw [mem_filter, hP, Nat.mem_primesBelow] at hp
            exact mem_Icc.2 ⟨hp.1.2.one_lt.le, Nat.le_sqrt.2 hp.2⟩
        _ = Nat.sqrt y := by simp
    calc ∑ p ∈ P with p * p ≤ y, log y / log p ≤ ∑ p ∈ P with p * p ≤ y, log y / log 2 := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter, hP, Nat.mem_primesBelow] at hp
          exact div_le_div_of_nonneg_left hly.le hl2
            (log_le_log (by norm_num) (by exact_mod_cast hp.1.2.two_le))
      _ = (P.filter (fun p => p * p ≤ y)).card * (log y / log 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ Nat.sqrt y * (log y / log 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hbig : ∑ p ∈ P with ¬ p * p ≤ y, log y / log p ≤ 2 * P.card := by
    calc ∑ p ∈ P with ¬ p * p ≤ y, log y / log p ≤ ∑ p ∈ P with ¬ p * p ≤ y, (2 : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter, hP, Nat.mem_primesBelow] at hp
          have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.2.one_lt
          have hlp : 0 < log (p : ℝ) := log_pos hp1
          rw [div_le_iff₀ hlp]
          have hyp : (y : ℝ) ≤ (p : ℝ) * p := by exact_mod_cast (not_le.1 hp.2).le
          have := log_le_log (by positivity) hyp
          rw [log_mul (by positivity) (by positivity)] at this
          linarith
      _ = 2 * (P.filter (fun p => ¬ p * p ≤ y)).card := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * P.card := by gcongr; exact filter_subset _ _
  linarith

/-- The constant in the Rankin bound. -/
noncomputable def C₀ : ℝ := 2 * (2 * log 4 + 2) + 16 / log 2

lemma C₀_pos : 0 < C₀ := by
  have : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold C₀; positivity

lemma sum_log_div_le' (y : ℕ) (hy : 2 ≤ y) :
    ∑ p ∈ (y + 1).primesBelow, log y / log p ≤ C₀ * (y / log y) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h1 := sum_log_div_le y hy
  have h2 := card_primesBelow_le y hy
  have h3 : (Nat.sqrt y : ℝ) * (log y / log 2) ≤ 16 / log 2 * (y / log y) := by
    calc (Nat.sqrt y : ℝ) * (log y / log 2) ≤ √(y : ℝ) * (log y / log 2) :=
          mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt
            (div_nonneg (log_nonneg hy1.le) hl2.le)
      _ = (√(y : ℝ) * log y) / log 2 := by ring
      _ ≤ (16 * (y / log y)) / log 2 := div_le_div_of_nonneg_right (sqrt_mul_log_le hy1) hl2.le
      _ = 16 / log 2 * (y / log y) := by ring
  unfold C₀
  nlinarith

/-- `|Sm (y ^ K) y| ≤ exp (K + C₀ y / log y)`. -/
lemma card_Sm_le (y K : ℕ) (hy : 2 ≤ y) :
    ((Sm (y ^ K) y).card : ℝ) ≤ exp (K + C₀ * (y / log y)) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  set σ := 1 / log (y : ℝ) with hσdef
  have hσ : 0 < σ := by positivity
  have h1 := rankin_card σ hσ y (y ^ K) (pow_pos (by omega) K)
  have h2 : ((y ^ K : ℕ) : ℝ) ^ σ = exp K := by
    rw [Nat.cast_pow, rpow_def_of_pos (by positivity), log_pow, hσdef]
    congr 1
    field_simp
  have h3 : ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      exp (∑ p ∈ (y + 1).primesBelow, log y / log p) := by
    rw [exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesBelow.1 hp).2.one_lt
      have := Real.rpow_lt_one_of_one_lt_of_neg hp1 (show -σ < 0 by linarith)
      exact inv_nonneg.2 (by linarith)
    · intro p hp
      exact factor_le hy (Nat.mem_primesBelow.1 hp).2.two_le
  have h4 := sum_log_div_le' y hy
  rw [h2] at h1
  calc ((Sm (y ^ K) y).card : ℝ) ≤ exp K * ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
        h1
    _ ≤ exp K * exp (∑ p ∈ (y + 1).primesBelow, log y / log p) :=
        mul_le_mul_of_nonneg_left h3 (exp_pos _).le
    _ = exp (K + ∑ p ∈ (y + 1).primesBelow, log y / log p) := (exp_add _ _).symm
    _ ≤ exp (K + C₀ * (y / log y)) := exp_le_exp.2 (by linarith)

/-! ### Pigeonhole: a block with many elements having long runs -/

lemma pigeon (f : ℕ → ℝ) (r : ℝ) (h0 : 1 ≤ f 0) (hr : 0 ≤ r) (K : ℕ) (hK : f K < r ^ K) :
    ∃ i < K, f (i + 1) < r * f i := by
  by_contra h
  push Not at h
  have : ∀ i ≤ K, r ^ i ≤ f i := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ i ih =>
      intro hi
      calc r ^ (i + 1) = r * r ^ i := by ring
        _ ≤ r * f i := mul_le_mul_of_nonneg_left (ih (by omega)) hr
        _ ≤ f (i + 1) := h i (by omega)
  exact absurd (this K le_rfl) (not_le.2 hK)

/-- The block: for every `y ≥ 2` there are `G ⊆ B`, `|G| ≥ δ |B|`, `|B| ≤ exp (C₂ y / log y)`,
such that the first `y` multiples of every `a ∈ G` lie in `B`. -/
lemma block : ∃ δ : ℝ, 0 < δ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ y : ℕ, 2 ≤ y → ∃ B G : Finset ℕ,
    (∀ a ∈ B, 0 < a) ∧ G ⊆ B ∧ (∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) ∧ 0 < B.card ∧
      δ * B.card ≤ G.card ∧ (B.card : ℝ) ≤ exp (C₂ * (y / log y)) := by
  have hC₀ := C₀_pos
  refine ⟨exp (-(2 + C₀)), exp_pos _, 2 + C₀, by linarith, fun y hy => ?_⟩
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  set Q := (y : ℝ) / log y with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef, one_lt_div hly]
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < y by linarith)]
  set K := ⌈Q⌉₊ with hKdef
  have hKQ : Q ≤ K := Nat.le_ceil Q
  have hKQ' : (K : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKpos : (0 : ℝ) < K := by linarith
  set f : ℕ → ℝ := fun i => ((Sm (y ^ i) y).card : ℝ) with hf
  have hf0 : 1 ≤ f 0 := by
    simp only [hf, pow_zero, Nat.one_le_cast]
    exact card_pos.2 ⟨1, one_mem_Sm le_rfl⟩
  have hfK : f K ≤ exp ((2 + C₀) * Q) := by
    refine (card_Sm_le y K hy).trans (exp_le_exp.2 ?_)
    nlinarith
  have hfK' : f K < exp (2 + C₀) ^ K := by
    rw [← exp_nat_mul]
    refine (card_Sm_le y K hy).trans_lt (exp_lt_exp.2 ?_)
    nlinarith
  obtain ⟨i, hiK, hi⟩ := pigeon f (exp (2 + C₀)) hf0 (exp_pos _).le K hfK'
  have hmono : ∀ {i j : ℕ}, i ≤ j → Sm (y ^ i) y ⊆ Sm (y ^ j) y :=
    fun hij => Sm_mono (Nat.pow_le_pow_right (by omega) hij)
  refine ⟨Sm (y ^ (i + 1)) y, Sm (y ^ i) y, fun a ha => pos_of_mem_Sm ha,
    hmono (Nat.le_succ i), ?_, card_pos.2 ⟨1, one_mem_Sm (Nat.one_le_pow _ _ (by omega))⟩, ?_, ?_⟩
  · intro a ha j hj1 hjy
    rw [pow_succ]
    exact mul_mem_Sm ha hj1 hjy
  · rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)]
    exact hi.le
  · calc ((Sm (y ^ (i + 1)) y).card : ℝ) ≤ f K := by
          simp only [hf]
          exact_mod_cast card_le_card (hmono (by omega))
      _ ≤ _ := hfK

/-! ### The lower bound -/

theorem lower_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ,
    (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
  obtain ⟨δ, hδ, C₂, hC₂, hblock⟩ := block
  exact lower_bound_of_block hδ hC₂ hblock

end RunsOfMultiples
