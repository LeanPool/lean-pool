/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFourAux
public import LeanPool.IwaniecLinearSieve.PrimeSums.Product
import LeanPool.IwaniecLinearSieve.LinearSieve.Corollaries
import LeanPool.IwaniecLinearSieve.LinearSieve.Crude
import LeanPool.IwaniecLinearSieve.LinearSieve.Depth
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaSeven
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFourAsymp
import LeanPool.IwaniecLinearSieve.SieveMajorants.Lemmas
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# [I71, Theorem 4]

With `L = log y`, `z = y^{1/s}`, `ξ = ξ(y)`, `cR` the constant of `R_asymp`, there is `c₇` with
    fail lower r y z ≤ cR (M(s)/L + c₇ r/(r+1) δ(s, y) G(s)/L²)

for all `r`, `y > 1`, `sMin lower ≤ s ≤ ξ(y)`.

The proof is by induction on `r` (for both sieves at once), as in [I71, pp. 23–25]:

* small `y` (`y < y₀`): the crude bound `fail ≤ exp (SLT y₀)` ([I71, (4.8)]);
* `r + 2 > 2 L / log L`: the recursion has stabilised, `fail (r+1) = fail r`;
* otherwise split the prime sum at `w = y^{1/ξ}` (`fail_succ_le_split`). For `p ≥ w` the inner
  level `(y/p, t_p - 1)` is in range (`inner_le_xi`), and the induction hypothesis, Corollary 1
  and Corollary 3 give the main term and `r/(r+1)` times the error term; the primes `p < w` are
  `fail (r+1) y w`, bounded crudely. The losses are absorbed by
  `(r+1)/(r+2) - r/(r+1) ≥ (r+1)/(r+2) · (log L)²/(4L²)`, as in [I71, (4.6)].

Compared with [I71] we split at `y^{1/ξ}` instead of `y^{1/(ξ-1)}` (then `t_p - 1 ≤ ξ(y/p)`
holds exactly), use `SLT(w) ≤ log log w + C` in the crude bound, and the upper-sieve source term
`∑_{y^{1/3} ≤ p < z} R(p)/p = R(y^{1/3}) - R(z)` replaces [I71, Lemmas 14, 16].
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Finset

namespace IwaniecLinearSieve.TheoremFour

/-- Theorem 4 at depth `r` with constants `cR`, `c₇`. -/
def Bound (cR c₇ : ℝ) (r : ℕ) : Prop :=
  ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s → s ≤ xi y →
    fail lower r y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2)

theorem one_le_sMin (lower : Bool) : 1 ≤ sMin lower := by
  cases lower <;> norm_num [sMin]

/-! ### The large primes: induction hypothesis, Corollaries 1 and 3 -/

/-- The induction hypothesis at the inner level `(y/p, t_p - 1)`, divided by `p`. -/
theorem ih_term {cR c₇ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) {lower : Bool} {y s : ℝ} {p : ℕ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hp : p ∈ rosserPrimes lower y (y ^ (1 / s)))
    (hw : y ^ (1 / xi y) ≤ p) :
    fail (!lower) r (y / p) p / p ≤
      cR * (mainMaj (!lower) (log y / log p - 1) / (p * log (y / p))) +
      cR * c₇ * ((r : ℝ) / (r + 1)) * (delta (log y / log p - 1) (y / p) *
        errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2)) := by
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hpy := prime_lt_of_mem_rosserPrimes hy hs1 hp
  have hp1 := (prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  have hyp : 1 < y / p := by rw [one_lt_div hp0]; exact hpy
  have h := IH (!lower) (y / p) (log y / log p - 1) hyp (sMin_le_inner hy hs hp)
    (inner_le_xi hy hp1 hpy hw)
  rw [rpow_inner_eq hp1 hpy] at h
  refine (div_le_div_of_nonneg_right h hp0.le).trans_eq ?_
  field_simp

theorem sum_ih_le {cR c₇ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) :
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        fail (!lower) r (y / p) p / p ≤
      cR * ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) +
      cR * c₇ * ((r : ℝ) / (r + 1)) *
        ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
            (p * log (y / p) ^ 2) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun p hp => ?_
  rw [mem_filter] at hp
  exact ih_term IH hy hs hp.1 hp.2

theorem intervalIntegral_le_integral_Ioi {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioi a)) (hf0 : ∀ t ∈ Ioi a, 0 ≤ f t) :
    ∫ t in a..b, f t ≤ ∫ t in Ioi a, f t := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set hf (ae_restrict_of_forall_mem measurableSet_Ioi hf0)
    Ioc_subset_Ioi_self.eventuallyLE

/-- Corollary 1 for the large primes: the main terms of the inner levels add up to `M(s)/L`
(minus the source part `(3 - s)⁺/L` of the upper sieve), up to `O(s² G(s) pntE(w)/L)`. -/
theorem cor1_part : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
    s ≤ xi y → 3 ≤ xi y → 2 ≤ y ^ (1 / xi y) →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  obtain ⟨C, hC0, hC⟩ := cor1_le
  refine ⟨432 * C, by positivity, fun lower y s hy hs hsξ hξ3 hw2 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hpE := pntE_pos (y ^ (1 / xi y))
  cases lower
  · -- upper sieve: `α = max s 3`, `M = f`
    simp only [Bool.not_false, mainMaj_true, Bool.false_eq_true, ite_false]
    have hset : (rosserPrimes false y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p) =
        (primesLT (y ^ (1 / max s 3))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p) := by
      ext p
      simp only [mem_filter, mem_rosserPrimes, mem_primesLT, Bool.false_eq_true, false_or]
      rw [lt_rpow_one_div_max_three hy (by linarith) (Nat.cast_nonneg p)]
      tauto
    rw [hset]
    have hα : max s 3 ≤ xi y := max_le hsξ hξ3
    have h := hC fSieve y (max s 3) (xi y) hy (by linarith [le_max_right s 3]) hα hw2
      (fSieve_antitone.antitoneOn _) (fun t _ => (fSieve_pos t).le)
    refine h.trans (add_le_add ?_ ?_)
    · have hint := intervalIntegral_le_integral_Ioi hα
        (integrableOn_fSieve_shift (le_max_right s 3))
        (fun t ht => div_nonneg (fSieve_pos _).le (by linarith [ht.out, le_max_right s 3]))
      have heq := mainMaj_false_eq_integral s
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    · have h1 := mainMaj_sub_one_le true false (by linarith [le_max_right s 3] : 1 ≤ max s 3)
      rw [mainMaj_true] at h1
      have hG : errMaj false (max s 3) = errMaj false s := by
        rcases le_total s 3 with h | h
        · rw [max_eq_right h, errMaj_false_of_le_three le_rfl, errMaj_false_of_le_three h]
        · rw [max_eq_left h]
      rw [hG] at h1
      have hsq : max s 3 ^ 2 ≤ 9 * s ^ 2 := by
        rcases le_total s 3 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
      have hGs := errMaj_pos false s
      have : fSieve (max s 3 - 1) ≤ 432 * s ^ 2 * errMaj false s := by nlinarith
      apply div_le_div_of_nonneg_right _ hL.le
      calc C * fSieve (max s 3 - 1) * pntE (y ^ (1 / xi y))
          ≤ C * (432 * s ^ 2 * errMaj false s) * pntE (y ^ (1 / xi y)) := by gcongr
        _ = 432 * C * s ^ 2 * errMaj false s * pntE (y ^ (1 / xi y)) := by ring
  · -- lower sieve: `α = s`, `M = F + (3 - s)⁺`
    simp only [Bool.not_true, rosserPrimes_true, ite_true, sub_zero]
    have hs2 : (2 : ℝ) ≤ s := hs
    have h := hC (mainMaj false) y s (xi y) hy hs2 hsξ hw2
      ((mainMaj_antitone false).antitoneOn _) (fun t _ => mainMaj_nonneg false t)
    refine h.trans (add_le_add ?_ ?_)
    · have hint := intervalIntegral_le_integral_Ioi hsξ (integrableOn_mainMaj_false_shift hs2)
        (fun t ht => div_nonneg (mainMaj_nonneg _ _) (by linarith [ht.out]))
      rw [mainMaj_true, fSieve_eq_integral_mainMaj hs2]
      exact div_le_div_of_nonneg_right hint hL.le
    · have h1 := mainMaj_sub_one_le false true hs1
      have hGs := errMaj_pos true s
      apply div_le_div_of_nonneg_right _ hL.le
      calc C * mainMaj false (s - 1) * pntE (y ^ (1 / xi y))
          ≤ C * (432 * s ^ 2 * errMaj true s) * pntE (y ^ (1 / xi y)) := by
            gcongr; nlinarith
        _ = 432 * C * s ^ 2 * errMaj true s * pntE (y ^ (1 / xi y)) := by ring

/-- The source term in the form needed for the induction. -/
theorem src_le_of_le_xi {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) {lower : Bool}
    {y s : ℝ} (hy : 1 < y) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y) (hξ3 : 3 ≤ xi y)
    (hw2 : 2 ≤ y ^ (1 / xi y)) :
    src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hCR : 0 ≤ CR := by
    have h := (abs_nonneg _).trans (hR 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hE : 0 ≤ 6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
    have := errMaj_pos lower s; positivity
  cases lower
  · simp only [Bool.false_eq_true, ite_false]
    rcases le_total 3 s with h3 | h3
    · -- no source
      have : src false y (y ^ (1 / s)) = 0 := by
        rw [src, ite_eq_right_iff.2 (by simp)]
        refine sum_eq_zero fun p hp => ?_
        rw [mem_filter, mem_primesLT] at hp
        have hlt : (p : ℝ) < y ^ (1 / (3 : ℝ)) := hp.1.2.trans_le
          (rpow_one_div_le_rpow_one_div hy.le (by norm_num) h3)
        exact absurd ((not_cube_lt_iff (by linarith) p.cast_nonneg).1 hp.2) (not_le.2 hlt)
      rw [this, max_eq_right (by linarith)]
      simpa using hE
    · refine (src_le hR hy hs1 hw2 (rpow_one_div_le_rpow_one_div hy.le (by linarith) hsξ)
        (rpow_one_div_le_rpow_one_div hy.le (by norm_num) hξ3)).trans ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [errMaj_false_of_le_three h3]
      have : 6 * CR * pntE (y ^ (1 / xi y)) ≤ 6 * CR * s ^ 2 * 1 * pntE (y ^ (1 / xi y)) := by
        have : 1 ≤ s ^ 2 := by nlinarith
        have := mul_nonneg hCR hpE.le
        nlinarith
      gcongr
  · simp only [src, ite_true, zero_add]
    exact hE

/-- Corollary 1 and the source estimate together give the full main term: the source
restores the upper-sieve correction `(3 - s)⁺` subtracted from the prime sum. -/
theorem main_sum_add_src_le {cR CR C₁ : ℝ} (hcR : 0 ≤ cR) {lower : Bool} {y s : ℝ}
    (hcor1 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C₁ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hsrc : src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y) :
    cR * ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) +
      src lower y (y ^ (1 / s)) ≤ cR * mainMaj lower s / log y +
        (cR * C₁ + 6 * CR) * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  refine (add_le_add (mul_le_mul_of_nonneg_left hcor1 hcR) hsrc).trans_eq ?_
  cases lower <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

/-! ### Small `y` -/
theorem SLT_mono {a b : ℝ} (hab : a ≤ b) : SLT a ≤ SLT b := by
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
  rw [mem_primesLT] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hab⟩

theorem fail_le_exp_SLT (lower : Bool) (r : ℕ) (y z : ℝ) : fail lower r y z ≤ exp (SLT z) := by
  refine (fail_le_sum_SLT_pow lower r y z).trans ?_
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (SLT_nonneg z) (r + 1))
  refine sum_le_sum_of_subset_of_nonneg (fun l hl => ?_) fun l _ _ => ?_
  · rw [mem_filter, Finset.mem_Icc] at hl; rw [Finset.mem_range]; omega
  · have := SLT_nonneg z; positivity

theorem xi_le_of_le {y Y : ℝ} (hy : 1 < y) (hyY : y ≤ Y) :
    xi y ≤ log Y / log (log 3) ^ (11 / 5 : ℝ) := by
  have hl3 : 1 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]; have := exp_one_lt_d9; linarith
  have hll : 0 < log (log 3) := log_pos hl3
  have hL : 0 < log y := log_pos hy
  have hP : 0 < log (log 3) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hll _
  have hle : log (log 3) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) := by
    refine rpow_le_rpow hll.le (log_le_log (by linarith) (log_le_log (by norm_num) ?_))
      (by norm_num)
    linarith
  rw [xi]
  calc log y / log (log (3 * y)) ^ (11 / 5 : ℝ) ≤ log y / log (log 3) ^ (11 / 5 : ℝ) :=
        div_le_div_of_nonneg_left hL.le hP hle
    _ ≤ _ := div_le_div_of_nonneg_right (log_le_log (by linarith) hyY) hP.le

/-- [I71, (4.8)]: for `1 < y ≤ Y` the claim at depth `r + 1` holds once `c₇` is large in terms
of `Y`. -/
theorem small_y {cR c₇ Y : ℝ} (hcR : 0 < cR) (hY : 1 < Y)
    (hc₇ : 6 * exp (SLT Y) * log Y ^ 2 / (cR * bigM (log Y / log (log 3) ^ (11 / 5 : ℝ))) ≤ c₇)
    (r : ℕ) (lower : Bool) {y s : ℝ} (hy : 1 < y) (hyY : y ≤ Y) (hs : sMin lower ≤ s)
    (hsξ : s ≤ xi y) :
    fail lower (r + 1) y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s /
          log y ^ 2) := by
  set Ξ := log Y / log (log 3) ^ (11 / 5 : ℝ)
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hLY : log y ≤ log Y := log_le_log (by linarith) hyY
  have hMΞ := bigM_pos Ξ
  have hG : bigM Ξ / 3 ≤ errMaj lower s :=
    le_trans (by gcongr; exact bigM_antitone (hsξ.trans (xi_le_of_le hy hyY)))
      (errMaj_mem lower s).1
  have hδ := one_le_delta hs1 y
  have hρ : (1 : ℝ) / 2 ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith
  have hz : y ^ (1 / s) ≤ Y := by
    refine le_trans ?_ hyY
    calc y ^ (1 / s) ≤ y ^ (1 / (1 : ℝ)) := rpow_one_div_le_rpow_one_div hy.le one_pos hs1
      _ = y := by simp
  have hfail : fail lower (r + 1) y (y ^ (1 / s)) ≤ exp (SLT Y) :=
    (fail_le_exp_SLT _ _ _ _).trans (exp_le_exp.2 (SLT_mono hz))
  have hc₇0 : 0 ≤ c₇ := le_trans (by positivity) hc₇
  have hM := mainMaj_nonneg lower s
  -- the error term alone is large enough
  have key : exp (SLT Y) ≤ cR * (c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y *
      errMaj lower s / log y ^ 2) := by
    have h1 : exp (SLT Y) ≤ cR * c₇ * ((1 / 2) * (bigM Ξ / 3)) / log Y ^ 2 := by
      have hK : 6 * exp (SLT Y) * log Y ^ 2 ≤ c₇ * (cR * bigM Ξ) :=
        (div_le_iff₀ (mul_pos hcR hMΞ)).1 hc₇
      rw [le_div_iff₀ (by have := log_pos hY; positivity)]
      linarith
    have hnum : cR * c₇ * ((1 / 2) * (bigM Ξ / 3)) ≤
        cR * c₇ * ((((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcR.le hc₇0)
      have := hMΞ.le
      have := errMaj_pos lower s
      calc (1 / 2 : ℝ) * (bigM Ξ / 3) ≤ (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) *
            (delta s y * errMaj lower s) := by
            refine mul_le_mul hρ ?_ (by positivity) (by positivity)
            nlinarith
        _ = _ := by ring
    have hc0 : 0 ≤ cR * c₇ * ((((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y *
        errMaj lower s) := le_trans (by positivity) hnum
    have hLL : log y ^ 2 ≤ log Y ^ 2 := by gcongr
    refine h1.trans ((div_le_div₀ hc0 hnum (by positivity) hLL).trans_eq (by ring))
  have : 0 ≤ cR * (mainMaj lower s / log y) := by positivity
  calc fail lower (r + 1) y (y ^ (1 / s)) ≤ exp (SLT Y) := hfail
    _ ≤ _ := by rw [mul_add]; linarith

/-! ### The small primes: the crude bound against Lemma 9 -/

/-- [I71, (4.9), (4.10)]: for `y ≥ y₁` the depth sums at `w = y^{1/ξ}` are at most
`δ(s, y) G(s) / L⁴` for every `s ≤ ξ`. -/
theorem crude_le : ∃ y₁ : ℝ, ∀ y ≥ y₁, ∀ (lower : Bool) (n : ℕ) (s : ℝ), sMin lower ≤ s →
    s ≤ xi y → fail lower n y (y ^ (1 / xi y)) ≤ delta s y * errMaj lower s / log y ^ 4 := by
  obtain ⟨c, hc⟩ := majG_ge_exp
  obtain ⟨CS, hCS⟩ := SLT_le_loglog
  obtain ⟨yx, hyx⟩ := exists_xi_large
  set c' := max c 0
  set C' := |CS| + 1
  obtain ⟨y₁, hy₁⟩ := eventually_atTop.1 ((eventually_crude c' C'
    (by simp [C'])).and (eventually_ge_atTop yx))
  refine ⟨y₁, fun y hy lower n s hs hsξ => ?_⟩
  obtain ⟨⟨hX0, h2e, hA, hB⟩, hyx'⟩ := hy₁ y hy
  obtain ⟨hy1, hξ32, -, hw2⟩ := hyx y hyx'
  set ξ := xi y
  set X := log (log (y ^ (1 / ξ))) + C'
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hξ4 : 6 ≤ ξ := by linarith [add_one_le_exp (32 : ℝ)]
  have hL4 : 0 < log y ^ 4 := by have := log_pos hy1; positivity
  -- the crude bound
  have hfail : fail lower n y (y ^ (1 / ξ)) ≤
      2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) := by
    rw [one_div]
    refine fail_rpow_le_tail hy1 (by linarith) ?_ h2e
    rw [← one_div]
    have := hCS _ hw2
    have : CS ≤ C' := by simp only [C']; linarith [le_abs_self CS]
    simp only [X]
    linarith
  -- Lemma 9
  have hG : ∀ t ≥ 3, exp (-(t * log t) - t * log (log t) - c' * t) ≤ errMaj lower t := by
    intro t ht
    rw [errMaj_eq_majG_succ]
    refine le_trans (exp_le_exp.2 ?_) (hc _ t ht)
    have : c * t ≤ c' * t := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hGs := errMaj_pos lower s
  have hmain : 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * log y ^ 4 ≤ delta s y * errMaj lower s := by
    rcases le_total s (ξ / 2) with h | h
    · refine hA.trans ((hG _ (by linarith)).trans ?_)
      calc errMaj lower (ξ / 2) ≤ errMaj lower s := errMaj_antitone lower h
        _ ≤ delta s y * errMaj lower s := le_mul_of_one_le_left hGs.le (one_le_delta hs1 y)
    · refine hB.trans ?_
      have hδ := delta_le_delta (by linarith : 1 ≤ ξ / 2) h y
      have hGG : exp (-(ξ * log ξ) - ξ * log (log ξ) - c' * ξ) ≤ errMaj lower s :=
        (hG ξ (by linarith)).trans (errMaj_antitone lower hsξ)
      exact mul_le_mul hδ hGG (exp_pos _).le (by linarith [one_le_delta hs1 y])
  rw [le_div_iff₀ hL4]
  calc fail lower n y (y ^ (1 / ξ)) * log y ^ 4
      ≤ 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * log y ^ 4 := by gcongr
    _ ≤ _ := hmain

/-! ### The inductive step -/

/-- `r/(r+1) ≤ (r+1)/(r+2) · (1 - ε)` when `ε (r+1)² ≤ 1`. -/
theorem ratio_le {r : ℕ} {ε : ℝ} (hε : ε * ((r : ℝ) + 1) ^ 2 ≤ 1) :
    (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) * (1 - ε) := by
  rw [show ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) * (1 - ε) = ((r : ℝ) + 1) * (1 - ε) / (r + 2) by
    push_cast; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The depth condition supplies the relative gain `(log L)²/(4L²)` used in [I71, (4.6)].
Here `Λ` stands for `log L`; the estimate only needs `Λ > 0`. -/
theorem ratio_le_of_depth {r : ℕ} {L Λ : ℝ} (hL : 0 < L) (hΛ : 0 < Λ)
    (hdepth : (r : ℝ) + 2 ≤ 2 * L / Λ) :
    (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) *
      (1 - Λ ^ 2 / (4 * L ^ 2)) := by
  apply ratio_le
  have hr : ((r : ℝ) + 2) * Λ ≤ 2 * L := (le_div_iff₀ hΛ).1 hdepth
  have hr' : ((r : ℝ) + 1) * Λ ≤ 2 * L :=
    (mul_le_mul_of_nonneg_right (by linarith only) hΛ.le).trans hr
  have hsq : (((r : ℝ) + 1) * Λ) ^ 2 ≤ (2 * L) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hr' 2
  calc
    Λ ^ 2 / (4 * L ^ 2) * ((r : ℝ) + 1) ^ 2 =
        (((r : ℝ) + 1) * Λ) ^ 2 / (2 * L) ^ 2 := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 hsq

/-- The final bookkeeping of the inductive step ([I71, (4.6)]). -/
theorem combine {cR c₇ L D M F cr E T ρ ρ' ε : ℝ}
    (hF : F ≤ cr + (cR * M / L + E) + cR * c₇ * ρ * T) (hcr : cr ≤ D / L ^ 2)
    (hE : E ≤ D / L ^ 2) (hT : T ≤ D * (1 + ε / 2)) (hρ : ρ ≤ ρ' * (1 - ε)) (hρ0 : 0 ≤ ρ)
    (hε0 : 0 ≤ ε) (hεL : 1 / (4 * L ^ 2) ≤ ε) (hρ' : 1 / 2 ≤ ρ') (hc : 32 ≤ cR * c₇)
    (hD : 0 ≤ D) (hL : 0 < L) :
    F ≤ cR * M / L + cR * c₇ * ρ' * D := by
  have hcc : 0 ≤ cR * c₇ := by linarith
  have hD' : 0 ≤ D * (1 + ε / 2) := by positivity
  have h1 : cR * c₇ * ρ * T ≤ cR * c₇ * ρ' * D * ((1 - ε) * (1 + ε / 2)) := by
    calc cR * c₇ * ρ * T ≤ cR * c₇ * ρ * (D * (1 + ε / 2)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ cR * c₇ * (ρ' * (1 - ε)) * (D * (1 + ε / 2)) := by gcongr
      _ = _ := by ring
  have h2 : (1 - ε) * (1 + ε / 2) ≤ 1 - ε / 2 := by nlinarith
  have hρ'0 : 0 ≤ ρ' := by linarith
  have h3 : cR * c₇ * ρ' * D * ((1 - ε) * (1 + ε / 2)) ≤ cR * c₇ * ρ' * D * (1 - ε / 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hL2 : 0 < L ^ 2 := by positivity
  have h4 : 4 / L ^ 2 ≤ cR * c₇ * ρ' * ε := by
    have e1 : 32 * (1 / 2) ≤ cR * c₇ * ρ' := mul_le_mul hc hρ' (by norm_num) hcc
    calc 4 / L ^ 2 = 32 * (1 / 2) * (1 / (4 * L ^ 2)) := by field_simp; norm_num
      _ ≤ cR * c₇ * ρ' * ε := mul_le_mul e1 hεL (by positivity) (by positivity)
  have h5 : 2 * (D / L ^ 2) ≤ cR * c₇ * ρ' * D * (ε / 2) := by
    have := mul_le_mul_of_nonneg_left h4 hD
    calc 2 * (D / L ^ 2) = D * (4 / L ^ 2) / 2 := by ring
      _ ≤ D * (cR * c₇ * ρ' * ε) / 2 := by linarith
      _ = _ := by ring
  nlinarith

/-- The main case of the inductive step: `y` large and `r + 2 ≤ 2 L / log L`. All analytic
inputs are hypotheses at the given `y`, `s`. -/
theorem main_step {cR c₇ CR C₁ C₃ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) (hcR : 0 < cR)
    (hc₇ : 32 ≤ cR * c₇) (hCR : 0 ≤ CR) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y)
    (hcor1 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C₁ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hsrc : src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hcor3 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C₃ * xi y ^ 2 * pntE (y ^ (1 / xi y))))
    (hcrude : fail lower (r + 1) y (y ^ (1 / xi y)) ≤ delta s y * errMaj lower s / log y ^ 4)
    (hΛ : 1 ≤ log (log y))
    (hδ : delta (exp 32) y * (1 + C₃ * xi y ^ 2 * pntE (y ^ (1 / xi y))) ≤
      1 + log (log y) ^ 2 / (8 * log y ^ 2))
    (hK : (cR * C₁ + 6 * CR) * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y)) ≤ 1)
    (hdepth : ¬ 2 * log y / log (log y) < r + 2) :
    fail lower (r + 1) y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s /
          log y ^ 2) := by
  set L := log y
  set ξ := xi y
  set w := y ^ (1 / ξ)
  set Λ := log (log y)
  set G := errMaj lower s
  set ρ' := ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)
  set S := (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => w ≤ p)
  set M := ∑ p ∈ S, mainMaj (!lower) (L / log p - 1) / (p * log (y / p))
  set T := ∑ p ∈ S, delta (L / log p - 1) (y / p) * errMaj (!lower) (L / log p - 1) /
    (p * log (y / p) ^ 2)
  set D := delta s y * G / L ^ 2 with hD
  set ε := Λ ^ 2 / (4 * L ^ 2) with hε
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < L := log_pos hy
  have hG := errMaj_pos lower s
  have hδs := one_le_delta hs1 y
  have hpE := pntE_pos w
  have hD0 : 0 ≤ D := by positivity
  -- Corollary 1 and the source term recover the main term, with an error of size `D/L²`.
  set K := cR * C₁ + 6 * CR
  have hmain : cR * M + src lower y (y ^ (1 / s)) ≤
      cR * mainMaj lower s / L + K * s ^ 2 * G * pntE w / L :=
    main_sum_add_src_le hcR.le hcor1 hsrc
  have hE : K * s ^ 2 * G * pntE w / L ≤ D / L ^ 2 := by
    have hK0 : 0 ≤ K := by positivity
    have hsq : s ^ 2 ≤ ξ ^ 2 := by gcongr
    rw [hD, div_div, div_le_div_iff₀ hL (by positivity)]
    calc K * s ^ 2 * G * pntE w * (L ^ 2 * L ^ 2) = G * (K * s ^ 2 * L ^ 3 * pntE w) * L := by
          ring
      _ ≤ G * (K * ξ ^ 2 * L ^ 3 * pntE w) * L := by gcongr
      _ ≤ G * 1 * L := by gcongr
      _ ≤ delta s y * G * L := by
          simpa only [one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_right hδs (by positivity : 0 ≤ G * L)
  -- Corollary 3 bounds the propagated error with relative loss at most `ε/2`.
  have hT : T ≤ D * (1 + ε / 2) := by
    refine hcor3.trans ?_
    have hmax := delta_max_le hs1 (one_le_exp (by norm_num) : 1 ≤ exp 32) y
    have hb : 0 ≤ 1 + C₃ * ξ ^ 2 * pntE w := by positivity
    have hε2 : ε / 2 = Λ ^ 2 / (8 * L ^ 2) := by rw [hε]; ring
    calc delta (max s (exp 32)) y * G / L ^ 2 * (1 + C₃ * ξ ^ 2 * pntE w)
        ≤ delta (exp 32) y * delta s y * G / L ^ 2 * (1 + C₃ * ξ ^ 2 * pntE w) := by gcongr
      _ = D * (delta (exp 32) y * (1 + C₃ * ξ ^ 2 * pntE w)) := by rw [hD]; ring
      _ ≤ D * (1 + ε / 2) := by rw [hε2]; gcongr
  -- The depth increment absorbs this loss and the two errors of size `D/L²`.
  have hρ : (r : ℝ) / (r + 1) ≤ ρ' * (1 - ε) :=
    ratio_le_of_depth hL (zero_lt_one.trans_le hΛ) (not_lt.1 hdepth)
  have hεL : 1 / (4 * L ^ 2) ≤ ε := by
    rw [hε]
    exact div_le_div_of_nonneg_right (by nlinarith only [hΛ]) (by positivity)
  have hρ' : 1 / 2 ≤ ρ' := by
    simp only [ρ']
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith
  have hcr : fail lower (r + 1) y w ≤ D / L ^ 2 := by
    refine hcrude.trans_eq ?_
    rw [hD, div_div]; ring
  -- Split at `w`, apply the inner induction bounds, then combine the main sum and source.
  have hwz : w ≤ y ^ (1 / s) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hsξ
  have hF : fail lower (r + 1) y (y ^ (1 / s)) ≤ fail lower (r + 1) y w +
      (cR * mainMaj lower s / L + K * s ^ 2 * G * pntE w / L) +
      cR * c₇ * ((r : ℝ) / (r + 1)) * T := by
    calc
      _ ≤ fail lower (r + 1) y w + ∑ p ∈ S, fail (!lower) r (y / p) p / p +
          src lower y (y ^ (1 / s)) := fail_succ_le_split lower r hwz
      _ ≤ fail lower (r + 1) y w + (cR * M + cR * c₇ * ((r : ℝ) / (r + 1)) * T) +
          src lower y (y ^ (1 / s)) :=
        add_le_add (add_le_add le_rfl (sum_ih_le IH hy hs)) le_rfl
      _ = fail lower (r + 1) y w + (cR * M + src lower y (y ^ (1 / s))) +
          cR * c₇ * ((r : ℝ) / (r + 1)) * T := by ring
      _ ≤ _ := add_le_add (add_le_add le_rfl hmain) le_rfl
  calc
    _ ≤ cR * mainMaj lower s / L + cR * c₇ * ρ' * D :=
      combine hF hcr hE hT hρ (by positivity) (by positivity) hεL hρ' hc₇ hD0 hL
    _ = _ := by rw [hD]; ring

end IwaniecLinearSieve.TheoremFour

namespace IwaniecLinearSieve

open TheoremFour

/-- [I71, Theorem 4] (main terms), for `k = 1`: if `cR`, `CR` are as in `R_asymp`
(`|R(z) log z - cR| ≤ CR pntE(z)` for `z ≥ 2`), there is `c₇ ≥ 0` such that for all `r`, both
sieves, `y > 1` and `sMin lower ≤ s ≤ ξ(y)`,

`fail lower r y (y^{1/s}) ≤ cR (M(s)/L + c₇ r/(r+1) δ(s, y) G(s)/L²)`,

where `M = mainMaj lower` (`f`, resp. `F + (3 - s)⁺`), `G = errMaj lower` (`𝔣`, resp. `𝔉`),
`L = log y`. -/
theorem theorem4 {cR CR : ℝ} (hcR : 0 < cR) (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
    ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
      s ≤ xi y → fail lower r y (y ^ (1 / s)) ≤
        cR * (mainMaj lower s / log y +
          c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := cor1_part
  obtain ⟨C₃, y₃, hC₃0, hC₃⟩ := cor3_xi
  obtain ⟨yd, hyd⟩ := exists_fail_add_eq
  obtain ⟨yx, hyx⟩ := exists_xi_large
  obtain ⟨yc, hyc⟩ := crude_le
  have hCR : 0 ≤ CR :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hR 2 le_rfl)) (pntE_pos 2)
  obtain ⟨ye, hye⟩ := eventually_atTop.1 ((eventually_one_le_loglog.and
    (eventually_delta_mul_le C₃ hC₃0)).and (eventually_mul_pntE_le (cR * C₁ + 6 * CR)))
  set y₀ := max (max (max y₃ yd) (max yx yc)) (max ye 2) with hy₀
  set Ξ := log y₀ / log (log 3) ^ (11 / 5 : ℝ)
  set c₇ := max (32 / cR) (6 * exp (SLT y₀) * log y₀ ^ 2 / (cR * bigM Ξ))
  have hY : 1 < y₀ := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right ye 2) (le_max_right _ _))
  have hc₇0 : 0 ≤ c₇ := le_trans (by positivity) (le_max_left _ _)
  have hc₇ : 32 ≤ cR * c₇ := by
    have := le_max_left (32 / cR) (6 * exp (SLT y₀) * log y₀ ^ 2 / (cR * bigM Ξ))
    rw [div_le_iff₀ hcR] at this
    linarith
  refine ⟨c₇, hc₇0, fun r => ?_⟩
  change Bound cR c₇ r
  induction r with
  | zero =>
    intro lower y s hy _ _
    have := mainMaj_nonneg lower s
    have := log_pos hy
    simp only [fail_zero, Nat.cast_zero, zero_div, mul_zero, zero_mul, add_zero]
    positivity
  | succ r IH =>
    intro lower y s hy hs hsξ
    rcases le_or_gt y y₀ with hyY | hyY
    · exact small_y hcR hY (le_max_right _ _) r lower hy hyY hs hsξ
    have hle : ∀ a, a ≤ y₀ → a ≤ y := fun a ha => ha.trans hyY.le
    have hy₃ : y₃ ≤ y := hle _ (by simp [y₀])
    have hyd' : yd ≤ y := hle _ (by simp [y₀])
    have hyx' : yx ≤ y := hle _ (by simp [y₀])
    have hyc' : yc ≤ y := hle _ (by simp [y₀])
    have hye' : ye ≤ y := hle _ (by simp [y₀])
    have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
    by_cases hdeep : 2 * log y / log (log y) < r + 2
    · -- the recursion has stabilised
      rw [hyd y hyd' lower r (y ^ (1 / s)) hdeep 1]
      refine (IH lower y s hy hs hsξ).trans ?_
      have hab : (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; nlinarith
      have hL2 : 0 < log y ^ 2 := by have := log_pos hy; positivity
      refine mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hab hc₇0) (zero_le_one.trans (one_le_delta hs1 y)))
          (errMaj_pos lower s).le) hL2.le) _) hcR.le
    · obtain ⟨-, hξ32, -, hw2⟩ := hyx y hyx'
      have hξ3 : 3 ≤ xi y := by linarith [add_one_le_exp (32 : ℝ)]
      obtain ⟨⟨hΛ, hδ⟩, hK⟩ := hye y hye'
      exact main_step IH hcR hc₇ hCR hC₁0 hC₃0 hy hs hsξ (hC₁ lower y s hy hs hsξ hξ3 hw2)
        (src_le_of_le_xi hR hy hs hsξ hξ3 hw2) (hC₃ lower y s hy₃ hs)
        (hyc y hyc' lower (r + 1) s hs hsξ)
        hΛ hδ hK hdeep

end IwaniecLinearSieve
