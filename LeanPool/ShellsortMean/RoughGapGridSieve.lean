/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.FiniteFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! An elementary sampling inequality on a common finite Fourier grid. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapGridSieve
open Finset ZMod Shellsort.FiniteFourier
open scoped ComplexConjugate
variable {N : ℕ} [NeZero N]

theorem grid_parseval (f : ZMod N → ℂ) :
    ∑ k, ‖dft f k‖ ^ 2 = (N : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  let g := fun j => conj (f j)
  have h := dft_transpose f (fun k ↦ dft g (-k))
  rw [dft_comp_neg, dft_dft] at h
  have a (k : ZMod N) : dft f k * dft g (-k) = ((‖dft f k‖ ^ 2 : ℝ) : ℂ) := by
    rw [show dft g (-k) = conj (dft f k) from dft_conj_neg f k, Complex.mul_conj, Complex.sq_norm]
  have b (j : ZMod N) : f j * ((N : ℂ) • g (- -j)) = N * ((‖f j‖ ^ 2 : ℝ) : ℂ) := by
    simp [g, Complex.sq_norm, ← Complex.mul_conj, mul_left_comm]
  apply Complex.ofReal_injective
  push_cast
  simpa only [a, b, mul_sum, Complex.ofReal_pow, Complex.ofReal_natCast] using h

private theorem char_step (j : ℤ) :
    ‖stdAddChar (-(j : ZMod N)) - 1‖ ≤ 2 * Real.pi * |(j : ℝ)| / N := by
  rw [← Int.cast_neg, stdAddChar_coe]
  let x : ℝ := - (2 * Real.pi * j / N)
  have eq : (2 * (Real.pi : ℂ) * Complex.I * ((-j : ℤ) : ℂ) / N) = Complex.I * (x : ℂ) := by
    dsimp [x]; push_cast; ring
  rw [eq]
  apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)).trans_eq
  dsimp [x]; rw [abs_neg, abs_div, abs_mul, abs_mul]
  simp [abs_of_nonneg Real.pi_pos.le]

private def diff (f : ZMod N → ℂ) (j : ZMod N) := (stdAddChar (-j) - 1) * f j

private theorem dft_diff (f : ZMod N → ℂ) (k : ZMod N) :
    dft (diff f) k = dft f (k + 1) - dft f k := by
  simp only [dft_apply, smul_eq_mul, diff, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [mul_add, mul_one, neg_add, AddChar.map_add_eq_mul]
  ring

/-- The discrete Bernstein bound uses integer representatives of the physical
support and applies just as well to a support centered at zero. -/
theorem grid_bernstein (f : ZMod N → ℂ) (L : ℝ) (_hL : 0 ≤ L)
    (hs : ∀ k, f k ≠ 0 → ∃ j : ℤ, (j : ZMod N) = k ∧ |(j : ℝ)| ≤ L) :
    (∑ k, ‖dft f (k + 1) - dft f k‖ ^ 2) ≤
      (2 * Real.pi * L / N) ^ 2 * ((N : ℝ) * ∑ j, ‖f j‖ ^ 2) := by
  simp_rw [← dft_diff]
  rw [grid_parseval]
  have each (k : ZMod N) : ‖diff f k‖ ≤ (2 * Real.pi * L / N) * ‖f k‖ := by
    by_cases h : f k = 0
    · simp [diff, h]
    obtain ⟨j, rfl, hj⟩ := hs k h
    rw [diff, norm_mul]
    gcongr
    exact (char_step (N := N) j).trans (by gcongr)
  calc
    (N : ℝ) * ∑ j, ‖diff f j‖ ^ 2 ≤ N * ∑ j, ((2 * Real.pi * L / N)*‖f j‖) ^ 2 := by
      gcongr with j
      exact each j
    _ = _ := by simp_rw [mul_pow]; rw [← mul_sum]; ring

private theorem packed_sum {ι : Type*} [Fintype ι] {q : ℕ}
    (a : ι → ZMod N)
    (pack : Function.Injective (fun t : ι × Fin q ↦ a t.1 + (t.2.val : ZMod N)))
    (g : ZMod N → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∑ i, ∑ j : Fin q, g (a i + (j.val : ZMod N))) ≤ ∑ k, g k := by
  classical
  let e : ι × Fin q → ZMod N := fun t ↦ a t.1 + (t.2.val : ZMod N)
  calc
    _ = ∑ t : ι × Fin q, g (e t) := by simp [e, Fintype.sum_prod_type]
    _ = ∑ k ∈ univ.image e, g k := (sum_image (fun _ _ _ _ h ↦ pack h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

/-- Sampling the leading slot of pairwise disjoint cyclic arcs. -/
theorem positive_drop_sampling {ι : Type*} [Fintype ι] {q : ℕ}
    (a : ι → ZMod N)
    (pack : Function.Injective (fun t : ι × Fin q ↦ a t.1 + (t.2.val : ZMod N)))
    (g : ZMod N → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (q : ℝ) * ∑ i, g (a i) ≤
      (∑ k, g k) + q * ∑ k, max (g k - g (k + 1)) 0 := by
  classical
  let drop := fun k : ZMod N ↦ max (g k - g (k + 1)) 0
  have path (b : ZMod N) (j : ℕ) :
      g b ≤ g (b + j) + ∑ k ∈ range j, drop (b + k) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ, Nat.cast_succ, ← add_assoc]
      have e := le_max_left (g (b + j) - g (b + j + 1)) (0 : ℝ)
      change _ ≤ drop (b + j) at e
      simp only [add_assoc] at e ⊢
      linarith
  have atpoint (i : ι) (j : Fin q) : g (a i) ≤ g (a i + j.val) +
      ∑ k : Fin q, drop (a i + k.val) := by
    apply (path (a i) j.val).trans
    gcongr
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ drop (a i + k)) q]
    exact sum_le_sum_of_subset_of_nonneg (range_mono j.isLt.le)
      (fun k _ _ ↦ le_max_right _ _)
  have ss := sum_le_sum (s := (univ : Finset ι)) (fun i _ ↦
    sum_le_sum (s := (univ : Finset (Fin q))) (fun j _ ↦ atpoint i j))
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_sum] at ss
  apply ss.trans
  exact add_le_add (packed_sum a pack g hg)
    (mul_le_mul_of_nonneg_left (packed_sum a pack drop (fun _ ↦ le_max_right _ _)) (by positivity))

private theorem sum_translate (u : ZMod N → ℝ) :
    (∑ k, u (k + 1)) = ∑ k, u k :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun _ ↦ rfl)

/-- The total positive variation is half the absolute variation on the circle. -/
theorem positive_variation (g : ZMod N → ℝ) :
    2 * (∑ k, max (g k - g (k + 1)) 0) = ∑ k, |g k - g (k + 1)| := by
  have cell (a b : ℝ) : 2 * max (a - b) 0 = |a - b| + (a - b) := by
    by_cases h : 0 ≤ a - b
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (le_of_not_ge h)]; ring
  rw [mul_sum]; simp_rw [cell]
  rw [sum_add_distrib, sum_sub_distrib, sum_translate]; ring

private theorem weighted_product {ι : Type*} [Fintype ι] (a b : ι → ℝ) (c E : ℝ)
    (hc : 0 ≤ c) (hE : 0 ≤ E) (ha : (∑ i, (a i) ^ 2) = E)
    (hb : (∑ i, (b i) ^ 2) ≤ c ^ 2 * E) : (∑ i, a i * b i) ≤ c * E := by
  have h := sum_mul_sq_le_sq_mul_sq univ a b
  rw [ha] at h
  have t := h.trans (mul_le_mul_of_nonneg_left hb hE)
  by_contra! fail
  have u := mul_self_lt_mul_self (mul_nonneg hc hE) fail
  nlinarith

theorem grid_positive_bernstein (f : ZMod N → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ k, f k ≠ 0 → ∃ j : ℤ, (j : ZMod N) = k ∧ |(j : ℝ)| ≤ L) :
    (∑ k, max (‖dft f k‖ ^ 2 - ‖dft f (k + 1)‖ ^ 2) 0)
       ≤ (2 * Real.pi * L) * (∑ j, ‖f j‖ ^ 2) := by
  let a := fun k : ZMod N ↦ ‖dft f k‖
  let b := fun k : ZMod N ↦ ‖dft f (k + 1) - dft f k‖
  let c := 2 * Real.pi * L / N
  let E := (N : ℝ) * (∑ j, ‖f j‖ ^ 2)
  have inn : (∑ k, (a k) ^ 2) = E := grid_parseval f
  have next : (∑ k, (a (k + 1)) ^ 2) = E :=
    (sum_translate (fun k ↦ (a k) ^ 2)).trans inn
  have deriv : (∑ k, (b k) ^ 2) ≤ c ^ 2 * E := grid_bernstein f L hL hs
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have p := weighted_product a b c E hc hE inn deriv
  have q := weighted_product (fun k ↦ a (k + 1)) b c E hc hE next deriv
  have cell (k : ZMod N) : |(a k) ^ 2 - (a (k + 1)) ^ 2| ≤ a k * b k + a (k + 1) * b k := by
    have habs : |a k - a (k + 1)| ≤ b k := by
      dsimp [a, b]; rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
    have ha : 0 ≤ a k + a (k + 1) := by dsimp [a]; positivity
    rw [sq_sub_sq, abs_mul, abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_right habs ha]
  have total := sum_le_sum (s := (univ : Finset (ZMod N))) (fun k _ ↦ cell k)
  rw [sum_add_distrib] at total
  have cycle := positive_variation (fun k ↦ (a k) ^ 2)
  have ce : c * E = (2 * Real.pi * L) * (∑ j, ‖f j‖ ^ 2) := by
    dsimp [c, E]; field_simp [NeZero.ne (N : ℝ)]
  change ∑ k, max ((a k) ^ 2 - (a (k + 1)) ^ 2) 0 ≤ _
  linarith

/-- Whole-grid large sieve for disjoint q-point arcs starting at a sample.
Every frequency coefficient has a representative of absolute size at most L. -/
theorem packed_fourier_samples {ι : Type*} [Fintype ι] {q : ℕ} (hq : 0 < q)
    (a : ι → ZMod N)
    (pack : Function.Injective (fun t : ι × Fin q ↦ a t.1 + (t.2.val : ZMod N)))
    (f : ZMod N → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ k, f k ≠ 0 → ∃ j : ℤ, (j : ZMod N) = k ∧ |(j : ℝ)| ≤ L) :
    (∑ i, ‖dft f (a i)‖ ^ 2) ≤ ((N : ℝ) / q + 2 * Real.pi * L) * (∑ j, ‖f j‖ ^ 2) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have sm := positive_drop_sampling a pack (fun k ↦ ‖dft f k‖ ^ 2) (fun _ ↦ sq_nonneg _)
  rw [grid_parseval] at sm
  have h := sm.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (grid_positive_bernstein f L hL hs) hq'.le))
  apply (le_of_mul_le_mul_left _ hq')
  calc
    _ ≤ _ := h
    _ = _ := by field_simp


end Shellsort.RoughGapGridSieve
