/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapGridSieve

/-! Rational sampling windows on a common finite Fourier grid. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapFareyGrid
open Finset ZMod
open Shellsort.RoughGapGridSieve

/-- Numerators of distinct proper rational sample points on a common grid.
A positive difference of distinct cross products supplies one full grid step. -/
private theorem gap_of_cross (N q R x y a b c d : ℕ)
    (hN : N = q * R ^ 2) (_Npos : 0 < N)
    (hx : x * b = N * a) (hy : y * d = N * c) (hb : 0 < b) (hd : 0 < d)
    (br : b ≤ R) (dr : d ≤ R) (lt : x < y) : x + q ≤ y := by
  have diff : a * d < c * b := by
    by_contra! hh
    have h := Nat.mul_le_mul_left N hh
    have h' := Nat.mul_lt_mul_of_pos_right lt (Nat.mul_pos hb hd)
    nlinarith [congrArg (·*d) hx, congrArg (·*b) hy]
  have h := Nat.mul_le_mul_left N (Nat.succ_le_of_lt diff)
  have r1 : (y - x) * (b * d) = N * (c * b - a * d) := by
    rw [Nat.sub_mul, Nat.mul_sub]
    have h1 : y * (b * d) = N * (c * b) := by nlinarith [congrArg (·*b) hy]
    have h2 : x * (b * d) = N * (a * d) := by nlinarith [congrArg (·*d) hx]
    rw [h1, h2]
  have lower : N ≤ (y - x) * (b * d) := by
    rw [r1]
    exact Nat.le_mul_of_pos_right N (Nat.sub_pos_of_lt diff)
  have upper : (y - x) * (b * d) ≤ (y - x) * R ^ 2 :=
    Nat.mul_le_mul_left _ (by simpa [pow_two] using Nat.mul_le_mul br dr)
  have rpos : 0 < R ^ 2 := pow_pos (lt_of_lt_of_le hb br) _
  have sep : q ≤ y - x := by
    exact Nat.le_of_mul_le_mul_right (by simpa [← hN] using lower.trans upper) rpos
  omega

/-- R bounds each denominator, the grid size N is q R² and every sample
is exactly on the grid. Pairwise distinct reduced fractions can use the
cross-product inequality directly, without a coprimality hypothesis. -/
theorem farey_windows {ι : Type*} {N q R : ℕ} [NeZero N]
    (hN : N = q * R ^ 2) (a b x : ι → ℕ)
    (proper : ∀ i, a i < b i) (den : ∀ i, b i ≤ R)
    (onGrid : ∀ i, x i * b i = N * a i)
    (distinct : ∀ {i j}, a i * b j = a j * b i → i = j) :
    Function.Injective (fun t : ι × Fin q ↦ (x t.1 : ZMod N) + (t.2.val : ZMod N)) := by
  have Npos : 0 < N := NeZero.pos N
  have bpos (i : ι) : 0 < b i := Nat.zero_lt_of_lt (proper i)
  have gridlt (i : ι) : x i < N := by
    have e := onGrid i
    have e' := Nat.mul_lt_mul_of_pos_left (proper i) Npos
    exact Nat.lt_of_mul_lt_mul_right (e ▸ e')
  have top (i : ι) : x i + q ≤ N := gap_of_cross N q R (x i) N
    (a i) (b i) 1 1 hN Npos (onGrid i) rfl (bpos i) (by decide) (den i)
    (Nat.succ_le_of_lt (lt_of_lt_of_le (bpos i) (den i))) (gridlt i)
  intro t u he
  rcases t with ⟨i, v⟩; rcases u with ⟨j, w⟩
  change ((x i : ZMod N) + v.val) = ((x j : ZMod N) + w.val) at he
  rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (by have := top i; omega),
    Nat.mod_eq_of_lt (by have := top j; omega)] at he
  have hxy : x i = x j := by
    rcases lt_trichotomy (x i) (x j) with h|h|h
    · have h' := gap_of_cross N q R (x i) (x j) (a i) (b i) (a j) (b j)
        hN Npos (onGrid i) (onGrid j) (bpos i) (bpos j) (den i) (den j) h
      omega
    · exact h
    · have h' := gap_of_cross N q R (x j) (x i) (a j) (b j) (a i) (b i)
        hN Npos (onGrid j) (onGrid i) (bpos j) (bpos i) (den j) (den i) h
      omega
  have hij : i = j := by
    apply distinct
    apply Nat.eq_of_mul_eq_mul_left Npos
    have hi := congrArg (·*b j) (onGrid i)
    have hj := congrArg (·*b i) (onGrid j)
    rw [hxy] at hi
    nlinarith
  subst j
  have : v = w := Fin.ext (by omega)
  subst w
  rfl

theorem rational_grid_sieve {ι : Type*} [Fintype ι] {N q R : ℕ} [NeZero N]
    (hq : 0 < q) (hN : N = q * R ^ 2) (a b x : ι → ℕ)
    (proper : ∀ i, a i < b i) (den : ∀ i, b i ≤ R)
    (onGrid : ∀ i, x i * b i = N * a i)
    (distinct : ∀ {i j}, a i * b j = a j * b i → i = j)
    (f : ZMod N → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (support : ∀ k, f k ≠ 0 → ∃ j : ℤ, (j : ZMod N) = k ∧ |(j : ℝ)| ≤ L) :
    (∑ i, ‖dft f (x i : ZMod N)‖ ^ 2) ≤ ((R : ℝ) ^ 2 + 2 * Real.pi * L) * (∑ j, ‖f j‖ ^ 2) := by
  have h := packed_fourier_samples hq (fun i ↦ (x i : ZMod N))
    (farey_windows hN a b x proper den onGrid distinct) f L hL support
  have eq : (N : ℝ) / q = (R : ℝ) ^ 2 := by
    have hq' : (q : ℝ) ≠ 0 := by positivity
    have cast : (N : ℝ) = q * (R : ℝ) ^ 2 := by exact_mod_cast hN
    rw [cast]; field_simp
  simpa [eq] using h

private def padded {ι : Type*} [Fintype ι] {N : ℕ}
    (pos : ι → ZMod N) (v : ι → ℂ) (k : ZMod N) : ℂ := by
  classical
  exact if h : ∃ i, pos i = k then v h.choose else 0

private theorem padded_at {ι : Type*} [Fintype ι] {N : ℕ}
    (pos : ι → ZMod N) (inj : Function.Injective pos) (v : ι → ℂ) (i : ι) :
    padded pos v (pos i) = v i := by
  classical
  have h : ∃ j, pos j = pos i := ⟨i, rfl⟩
  simp only [padded, dite_eq_left h, inj h.choose_spec]

private theorem sum_padded {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    {A : Type*} [AddCommMonoid A] (pos : ι → ZMod N) (inj : Function.Injective pos)
    (v : ι → ℂ) (w : ZMod N → ℂ → A) (zero : ∀ k, w k 0 = 0) :
    (∑ k, w k (padded pos v k)) = ∑ i, w (pos i) (v i) := by
  classical
  have r : (∑ k ∈ univ.image pos, w k (padded pos v k)) =
      ∑ k, w k (padded pos v k) := by
    apply sum_subset (subset_univ _)
    intro k _ hk
    have hn : ¬∃ i, pos i = k := by simpa using hk
    simp [padded, hn, zero]
  rw [← r, sum_image (fun _ _ _ _ h ↦ inj h)]
  simp only [padded_at pos inj]

private def wave (j : ℤ) (a b : ℕ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * j * a / b)

private theorem gridWave {N : ℕ} [NeZero N] (j : ℤ) (a b x : ℕ)
    (hb : 0 < b) (eq : x * b = N * a) :
    stdAddChar (-((j : ZMod N) * (x : ZMod N))) = wave j a b := by
  rw [show - ((j : ZMod N) * (x : ZMod N)) = ((-(j * (x : ℤ)) : ℤ) : ZMod N) by push_cast; ring,
      stdAddChar_coe, wave]
  apply congrArg Complex.exp
  have eb : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have eq' : (x : ℂ) * b = N * (a : ℂ) := by exact_mod_cast eq
  push_cast
  field_simp [eb, NeZero.ne (N : ℂ)]
  linear_combination - (j : ℂ) * eq'

/-- A finite large sieve for the actual polynomial supported in the centered
band indexed by j-m/2. The common grid is constructed, not hypothesized. -/
theorem centered_short_interval_sieve {ι : Type*} [Fintype ι] (R m : ℕ) (hR : 0 < R)
    (a b : ι → ℕ) (proper : ∀ i, a i < b i) (den : ∀ i, b i ≤ R)
    (distinct : ∀ {i j}, a i * b j = a j * b i → i = j) (v : Fin m → ℂ) :
    (∑ i, ‖∑ j : Fin m, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      ((j.val : ℂ) - (m / 2 : ℕ)) * a i / b i) * v j‖ ^ 2) ≤
        ((R : ℝ) ^ 2 + 2 * Real.pi * (m / 2 : ℕ)) * (∑ j, ‖v j‖ ^ 2) := by
  classical
  let q := R.factorial * (m + 1)
  let N := q * R ^ 2
  have qpos : 0 < q := Nat.mul_pos R.factorial_pos (by omega)
  have Npos : 0 < N := Nat.mul_pos qpos (pow_pos hR _)
  let : NeZero N := ⟨Npos.ne'⟩
  have mlt : m < N := by
    have h1 : m + 1 ≤ q := Nat.le_mul_of_pos_left _ R.factorial_pos
    have h2 : q ≤ N := Nat.le_mul_of_pos_right _ (pow_pos hR _)
    omega
  let x := fun i ↦ (N / b i) * a i
  have onGrid (i : ι) : x i * b i = N * a i := by
    have d1 := Nat.dvd_factorial (Nat.zero_lt_of_lt (proper i)) (den i)
    have d2 : b i ∣ N := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left d1 _) _
    dsimp [x]; rw [mul_right_comm, Nat.div_mul_cancel d2]
  let c := m / 2
  let pos := fun j : Fin m ↦ (j.val : ZMod N) - (c : ZMod N)
  have inj : Function.Injective pos := by
    intro j k eq
    change (j.val : ZMod N) - c = (k.val : ZMod N) - c at eq
    have he := sub_left_inj.mp eq
    have he' := congrArg ZMod.val he
    rw [val_natCast_of_lt (j.isLt.trans mlt), val_natCast_of_lt (k.isLt.trans mlt)] at he'
    exact Fin.ext he'
  have supp : ∀ k, padded pos v k ≠ 0 →
      ∃ j : ℤ, (j : ZMod N) = k ∧ |(j : ℝ)| ≤ (c : ℝ) := by
    intro k nz
    by_cases h : ∃ i, pos i = k
    · obtain ⟨i, rfl⟩ := h
      refine ⟨(i.val : ℤ) - c, by simp [pos], ?_⟩
      have upper : i.val ≤ 2 * c := by dsimp [c]; omega
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, abs_le]
      have up : (i.val : ℝ) ≤ 2 * (c : ℝ) := by exact_mod_cast upper
      have lo : 0 ≤ (i.val : ℝ) := by positivity
      constructor <;> linarith
    · simp [padded, h] at nz
  have eqf (i : ι) : dft (padded pos v) (x i : ZMod N) =
      ∑ j : Fin m, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        ((j.val : ℂ) - (m / 2 : ℕ)) * a i / b i) * v j := by
    simp only [dft_apply, smul_eq_mul]
    rw [sum_padded pos inj v (fun k z ↦ stdAddChar (-(k * (x i : ZMod N))) * z) (by simp)]
    apply sum_congr rfl; intro j _
    have idj : pos j = (((j.val : ℤ) - c : ℤ) : ZMod N) := by simp [pos]
    rw [idj, gridWave _ _ _ _ (Nat.zero_lt_of_lt (proper i)) (onGrid i)]
    unfold wave
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  have en := sum_padded pos inj v (fun _ z ↦ ‖z‖ ^ 2) (by simp)
  have final := rational_grid_sieve qpos (N := N) (R := R) rfl a b x proper den onGrid
    distinct (padded pos v) (c : ℝ) (by positivity) supp
  simp_rw [eqf] at final
  simpa only [en, c] using final

private theorem wave_add (j k : ℤ) (a b : ℕ) :
    wave (j + k) a b = wave j a b * wave k a b := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

private theorem wave_unit (j : ℤ) (a b : ℕ) : ‖wave j a b‖ = 1 := by
  unfold wave
  have eq : -2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * a / b =
      ((-2 * Real.pi * (j : ℝ) * a / b : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [eq, Complex.norm_exp_ofReal_mul_I]

/-- The actual short-interval bound, for coefficients in an arbitrary translated
integer interval and distinct proper rational samples of denominators at most R. -/
theorem short_interval_sieve {ι : Type*} [Fintype ι] (R m : ℕ) (hR : 0 < R) (start : ℤ)
    (a b : ι → ℕ) (proper : ∀ i, a i < b i) (den : ∀ i, b i ≤ R)
    (distinct : ∀ {i j}, a i * b j = a j * b i → i = j) (v : Fin m → ℂ) :
    (∑ i, ‖∑ j : Fin m, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      ((start : ℂ) + j.val) * a i / b i) * v j‖ ^ 2) ≤
        ((R : ℝ) ^ 2 + Real.pi * m) * (∑ j, ‖v j‖ ^ 2) := by
  let D (j : Fin m) := (j.val : ℤ) - (m / 2 : ℕ)
  let c := start + (m / 2 : ℕ)
  have term (j : Fin m) (i : ι) : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      ((start : ℂ) + j.val) * a i / b i) * v j =
      wave c (a i) (b i) * (wave (D j) (a i) (b i) * v j) := by
    rw [← mul_assoc, ← wave_add]
    have eq : c + D j = start + j.val := by dsimp [c, D]; omega
    rw [eq]; unfold wave; push_cast; rfl
  have center (i : ι) (j : Fin m) : wave (D j) (a i) (b i) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (m / 2 : ℕ)) * a i / b i) := by
    unfold wave D
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  simp_rw [term, ← mul_sum, norm_mul, wave_unit, one_mul, center]
  apply (centered_short_interval_sieve R m hR a b proper den distinct v).trans
  have h : (2 : ℝ) * (m / 2 : ℕ) ≤ m := by exact_mod_cast (show 2 * (m / 2) ≤ m by omega)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]




end Shellsort.RoughGapFareyGrid
