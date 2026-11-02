/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.Defs
public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
public import LeanPool.IwaniecLinearSieve.Rosser
import LeanPool.IwaniecLinearSieve.LinearSieve.Corollaries
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Auxiliary facts for [I71, Theorem 4]

* the telescoping identity `∑_{a ≤ p < b} R(p)/p = R(a) - R(b)` (from `R_eq`), and the bound
  for the depth-one source term of the upper sieve via `R_asymp`;
* monotonicity of `δ(s, y)` in `s`, and `δ(max s s₀, y) ≤ δ(s₀, y) δ(s, y)`;
* the inner level of the recursion: `(y/p)^{1/(t_p - 1)} = p`, the domain condition
  `sMin (!lower) ≤ t_p - 1`, and `t_p - 1 ≤ ξ(y/p)` for `p ≥ y^{1/ξ(y)}`;
* the splitting of `fail lower (r+1) y z` at `w ≤ z`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Finset

namespace IwaniecLinearSieve.TheoremFour

/-! ### The depth-one source term -/

/-- Telescoping: `∑_{a ≤ p < b} R(p)/p = R(a) - R(b)` for `a ≤ b`. -/
theorem sum_R_div_eq {a b : ℝ} (hab : a ≤ b) :
    ∑ p ∈ (primesLT b).filter (fun p : ℕ => a ≤ p), R p / p = R a - R b := by
  have h := sum_filter_add_sum_filter_not (primesLT b) (fun p : ℕ => a ≤ (p : ℝ))
    (fun p => R p / p)
  have hs : (primesLT b).filter (fun p : ℕ => ¬ a ≤ (p : ℝ)) = primesLT a := by
    ext p
    simp only [mem_filter, mem_primesLT, not_le]
    constructor
    · rintro ⟨⟨hp, -⟩, h⟩; exact ⟨hp, h⟩
    · rintro ⟨hp, h⟩; exact ⟨⟨hp, h.trans_le hab⟩, h⟩
  rw [hs] at h
  have ha := R_eq a
  have hb := R_eq b
  linarith

/-- The depth-one source term of `fail false`: the primes `p < z` with `p³ ≥ y` (none for the
lower sieve). -/
noncomputable def src (lower : Bool) (y z : ℝ) : ℝ :=
  if lower then 0 else ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p

theorem src_nonneg (lower : Bool) (y z : ℝ) : 0 ≤ src lower y z := by
  unfold src
  split_ifs
  · exact le_rfl
  · exact sum_nonneg fun p _ ↦ div_nonneg (R_nonneg _) p.cast_nonneg

theorem fail_succ_eq (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower (r + 1) y z =
      ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p + src lower y z := by
  cases lower
  · rw [fail_false_succ, src]; rfl
  · rw [fail_true_succ, src, rosserPrimes_true]; simp

/-- `¬ p³ < y ↔ y^{1/3} ≤ p`. -/
theorem not_cube_lt_iff {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) :
    ¬ x ^ 3 < y ↔ y ^ (1 / 3 : ℝ) ≤ x := by
  rw [not_lt, one_div, rpow_inv_le_iff_of_pos hy hx (by norm_num)]
  norm_cast

/-- The source term for `z = y^{1/s}`:
`R(y^{1/3}) - R(y^{1/s}) ≤ cR (3 - s)⁺ / L + 6 C_R pntE(w) / L` for any `w ≥ 2` below `y^{1/s}`
and `y^{1/3}` (and `0` for the lower sieve). -/
theorem src_le {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) {lower : Bool}
    {y s w : ℝ} (hy : 1 < y) (hs : 1 ≤ s) (hw : 2 ≤ w) (hwz : w ≤ y ^ (1 / s))
    (hw3 : w ≤ y ^ (1 / 3 : ℝ)) :
    src lower y (y ^ (1 / s)) ≤
      (if lower then 0 else cR * max (3 - s) 0 / log y) + 6 * CR * pntE w / log y := by
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hCR : 0 ≤ CR := by
    have h := (abs_nonneg _).trans (hR 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  have hE : 0 ≤ 6 * CR * pntE w / log y := by have := pntE_pos w; positivity
  cases lower
  · simp only [src, Bool.false_eq_true, ite_false]
    have hset : (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y) =
        (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ y ^ (1 / 3 : ℝ) ≤ p) :=
      filter_congr fun p _ ↦ not_cube_lt_iff hy0.le p.cast_nonneg
    rw [hset]
    rcases le_total 3 s with h3 | h3
    · -- no primes
      have : (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ y ^ (1 / 3 : ℝ) ≤ p) = ∅ := by
        refine eq_empty_of_forall_notMem fun p hp ↦ ?_
        rw [mem_filter, mem_primesLT] at hp
        have := rpow_one_div_le_rpow_one_div hy.le (by norm_num) h3
        linarith [hp.1.2]
      rw [this, sum_empty, max_eq_right (by linarith)]
      simpa using hE
    · rw [sum_R_div_eq (rpow_one_div_le_rpow_one_div hy.le (by linarith) h3),
        max_eq_left (by linarith)]
      have h1 := (abs_le.1 (hR _ (hw.trans hw3))).2
      have h2 := (abs_le.1 (hR _ (hw.trans hwz))).1
      rw [log_rpow_one_div hy0] at h1 h2
      have e1 : pntE (y ^ (1 / 3 : ℝ)) ≤ pntE w := pntE_le_pntE (by linarith) hw3
      have e2 : pntE (y ^ (1 / s)) ≤ pntE w := pntE_le_pntE (by linarith) hwz
      have hR1 : R (y ^ (1 / 3 : ℝ)) ≤ 3 * (cR + CR * pntE w) / log y := by
        rw [le_div_iff₀ hL]
        nlinarith
      have hR2 : s * (cR - CR * pntE w) / log y ≤ R (y ^ (1 / s)) := by
        rw [div_le_iff₀ hL]
        have : R (y ^ (1 / s)) * (log y / s) * s = R (y ^ (1 / s)) * log y := by
          field_simp
        have h2' : cR - CR * pntE w ≤ R (y ^ (1 / s)) * (log y / s) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2' (by linarith : (0 : ℝ) ≤ s)]
      have : 3 * (cR + CR * pntE w) / log y - s * (cR - CR * pntE w) / log y ≤
          cR * (3 - s) / log y + 6 * CR * pntE w / log y := by
        rw [← sub_div, ← add_div]
        apply div_le_div_of_nonneg_right _ hL.le
        have := pntE_pos w
        nlinarith [mul_nonneg (mul_nonneg hCR this.le) (by linarith : (0 : ℝ) ≤ 3 - s)]
      linarith
  · simp only [src, ite_true]
    simpa using hE

/-! ### The compensation factor `δ` -/
theorem one_le_delta {s : ℝ} (hs : 1 ≤ s) (y : ℝ) : 1 ≤ delta s y := by
  rw [delta]
  exact one_le_rpow (by linarith [lsx_nonneg (log y) hs]) (by linarith)

theorem delta_le_delta {s s' : ℝ} (hs : 1 ≤ s) (hss' : s ≤ s') (y : ℝ) :
    delta s y ≤ delta s' y := by
  have hl := log_nonneg hs
  have hll : log s ≤ log s' := log_le_log (by linarith) hss'
  have hx0 := lsx_nonneg (log y) hs
  have hx : s ^ 2 * log s ^ 5 / log y ^ 2 ≤ s' ^ 2 * log s' ^ 5 / log y ^ 2 := by gcongr
  rw [delta, delta]
  calc (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s)
      ≤ (1 + s' ^ 2 * log s' ^ 5 / log y ^ 2) ^ (5 * s) :=
        rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem delta_max_le {s a : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (y : ℝ) :
    delta (max s a) y ≤ delta a y * delta s y := by
  rcases le_total s a with h | h
  · rw [max_eq_right h]
    exact le_mul_of_one_le_right (by linarith [one_le_delta ha y]) (one_le_delta hs y)
  · rw [max_eq_left h]
    exact le_mul_of_one_le_left (by linarith [one_le_delta hs y]) (one_le_delta ha y)

/-! ### The inner level of the recursion -/

/-- `(y/p)^{1/(t_p - 1)} = p` for `1 < p < y`, `t_p = log y / log p`. -/
theorem rpow_inner_eq {y : ℝ} {p : ℕ} (hp : 1 < p) (hpy : (p : ℝ) < y) :
    (y / p) ^ (1 / (log y / log p - 1)) = p := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hy0 : 0 < y := hp0.trans hpy
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have ht : 0 < log y / log p - 1 := by
    rw [sub_pos, one_lt_div hlp]; exact log_lt_log hp0 hpy
  rw [rpow_def_of_pos (div_pos hy0 hp0), log_div_prime_eq hy0 hp, mul_one_div,
    mul_div_cancel_right₀ _ ht.ne', exp_log hp0]

/-- `p < y^{1/s} ⇒ s < t_p`. -/
theorem lt_div_log_of_lt_rpow {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : 0 < s) (hp : 1 < p)
    (hpz : (p : ℝ) < y ^ (1 / s)) : s < log y / log p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := log_lt_log (by positivity) hpz
  rw [log_rpow_one_div (by linarith)] at h
  rw [lt_div_iff₀ hlp]; rw [lt_div_iff₀ hs] at h; linarith

theorem prime_lt_of_mem_rosserPrimes {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : 1 ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) : (p : ℝ) < y := by
  have h := lt_of_mem_primesLT (rosserPrimes_subset hp)
  calc (p : ℝ) < y ^ (1 / s) := h
    _ ≤ y ^ (1 / (1 : ℝ)) := rpow_one_div_le_rpow_one_div hy.le one_pos hs
    _ = y := by simp

/-- The inner parameter `t_p - 1` lies in the domain of `!lower`. -/
theorem sMin_le_inner {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : sMin lower ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) : sMin (!lower) ≤ log y / log p - 1 := by
  have hpP := prime_of_mem_primesLT (rosserPrimes_subset hp)
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpP.one_lt)
  cases lower
  · -- `p³ < y`
    have h3 := ((mem_rosserPrimes.1 hp).2.resolve_left (by simp))
    have h := log_lt_log (by have := hpP.pos; positivity) h3
    rw [log_pow] at h
    have : 3 < log y / log p := by rw [lt_div_iff₀ hlp]; push_cast at h; linarith
    simp only [Bool.not_false, sMin]
    linarith
  · have hs2 : (2 : ℝ) ≤ s := hs
    have := lt_div_log_of_lt_rpow hy (by linarith) hpP.one_lt
      (lt_of_mem_primesLT (rosserPrimes_subset hp))
    simp only [Bool.not_true, sMin]
    linarith

theorem one_lt_log_three_mul {x : ℝ} (hx : 1 ≤ x) : 1 < log (3 * x) := by
  rw [lt_log_iff_exp_lt (by linarith)]
  have := exp_one_lt_d9
  linarith

/-- `log (y^{1/ξ(y)}) = (log log 3y)^{11/5}`. -/
theorem log_rpow_one_div_xi {y : ℝ} (hy : 1 < y) :
    log (y ^ (1 / xi y)) = log (log (3 * y)) ^ (11 / 5 : ℝ) := by
  have hL : 0 < log y := log_pos hy
  have hℓ : 0 < log (log (3 * y)) := log_pos (one_lt_log_three_mul hy.le)
  have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ _
  rw [log_rpow_one_div (by linarith), xi, div_div_cancel₀ hL.ne']

/-- For `y^{1/ξ(y)} ≤ p < y`, the inner parameter satisfies `t_p - 1 ≤ ξ(y/p)`. -/
theorem inner_le_xi {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p) (hpy : (p : ℝ) < y)
    (hw : y ^ (1 / xi y) ≤ p) : log y / log p - 1 ≤ xi (y / p) := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hy0 : 0 < y := by linarith
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hℓ : 0 < log (log (3 * y)) := log_pos (one_lt_log_three_mul hy.le)
  have hyp1 : 1 < y / p := by rw [one_lt_div hp0]; exact hpy
  have hℓ' : 0 < log (log (3 * (y / p))) := log_pos (one_lt_log_three_mul hyp1.le)
  have hℓℓ' : log (log (3 * (y / p))) ≤ log (log (3 * y)) := by
    refine log_le_log (log_pos (by linarith)) (log_le_log (by positivity) ?_)
    gcongr
    exact div_le_self hy0.le (by exact_mod_cast hp.le)
  have hP' : 0 < log (log (3 * (y / p))) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ' _
  have hPP : log (log (3 * (y / p))) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) :=
    rpow_le_rpow hℓ'.le hℓℓ' (by norm_num)
  -- `(log log 3y)^{11/5} ≤ log p`
  have hw' : log (log (3 * y)) ^ (11 / 5 : ℝ) ≤ log p := by
    rw [← log_rpow_one_div_xi hy]
    exact log_le_log (rpow_pos_of_pos hy0 _) hw
  have ht : 0 < log y / log p - 1 := by
    rw [sub_pos, one_lt_div hlp]; exact log_lt_log hp0 hpy
  rw [xi, log_div_prime_eq hy0 hp, le_div_iff₀ hP']
  calc (log y / log p - 1) * log (log (3 * (y / p))) ^ (11 / 5 : ℝ)
      ≤ (log y / log p - 1) * log p := by
        gcongr; exact hPP.trans hw'
    _ = log p * (log y / log p - 1) := mul_comm _ _

/-! ### Splitting the prime sum -/
theorem rosserPrimes_filter_lt {lower : Bool} {y z w : ℝ} (hwz : w ≤ z) :
    (rosserPrimes lower y z).filter (fun p : ℕ ↦ ¬ w ≤ p) = rosserPrimes lower y w := by
  ext p
  simp only [mem_filter, mem_rosserPrimes, mem_primesLT, not_le]
  constructor
  · rintro ⟨⟨⟨hp, -⟩, h⟩, hw⟩; exact ⟨⟨hp, hw⟩, h⟩
  · rintro ⟨⟨hp, hw⟩, h⟩; exact ⟨⟨⟨hp, hw.trans_le hwz⟩, h⟩, hw⟩

/-- `fail lower (r+1) y z ≤ fail lower (r+1) y w + ∑_{w ≤ p} (inner terms) + source`. -/
theorem fail_succ_le_split (lower : Bool) (r : ℕ) {y z w : ℝ} (hwz : w ≤ z) :
    fail lower (r + 1) y z ≤ fail lower (r + 1) y w +
      ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p),
        fail (!lower) r (y / p) p / p + src lower y z := by
  rw [fail_succ_eq, fail_succ_eq lower r y w,
    ← sum_filter_add_sum_filter_not (rosserPrimes lower y z) (fun p : ℕ ↦ w ≤ (p : ℝ)),
    rosserPrimes_filter_lt hwz]
  linarith [src_nonneg lower y w]

end IwaniecLinearSieve.TheoremFour
