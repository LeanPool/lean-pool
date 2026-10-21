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
import LeanPool.IwaniecLinearSieve.LinearSieve.Depth
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFiveCount
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFourAux
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finset.Slice

/-!
# [I71, Theorem 5]: the size of the support of the Rosser weights

For `y > 1`, `sMin lower ≤ s ≤ ξ(y)` and every depth `r`,
    #{d ∈ rosserSet lower y y^{1/s} | ω(d) ≤ r} ≤ c₇ · (r+1)/(r+2) · δ(s, y) · G(s) · y / log² y

(`theorem5`), where `G = errMaj lower` (`𝔣` for the lower sieve, `𝔉` for the upper sieve). This
is [I71, (4.11)] with the depth shifted by one (`A_{r,y}` there counts `r + 1` levels of the
recursion, whence `r/(r+1)` and `G_{r+1}`); with our recursion (`card_filter_rosserSet_succ`) the
count at flag `lower` is compared with `errMaj lower`. Consequence (`card_rosserSet_le`):
`#(rosserSet true y y^{1/s}) ≪ y / log² y` uniformly for `s ∈ [2, 3]`.

The proof follows [I71, pp. 26–27], by induction on `r` for both flags at once:

* `y < c₈`: the count is at most `y` (`card_rosserSet_le`), and `c₇` is chosen large;
* `y ≥ c₈` and `r + 3 > 2 log y / log log y`: the count does not change from depth `r` to `r + 1`
  (`exists_card_filter_rosserSet_add_eq`);
* otherwise Lemma 17 is split at `w = y^{1/(ξ-1)}`: the primes `p ≥ w` are handled by the
  induction hypothesis at `(y/p, t_p - 1)` and Corollary 3, the primes `p < w` give at most
  `#(rosserSet lower y w)`, which is small by the crude count (`exists_card_small`). The losses
  (Corollary 3's factor `1 + C ξ² pntE(y^{1/ξ})`, `δ(max s s₀) ≤ δ(s) δ(s₀)`, the crude part)
  are absorbed by `(r+2)/(r+3) - (r+1)/(r+2) ≥ (log log y)² / (4 log² y)`.
-/

@[expose] public section

open Real Filter Finset

namespace IwaniecLinearSieve.TheoremFive

/-- The statement of Theorem 5 at depth `r` with constant `c₇`. -/
def Bound (c₇ : ℝ) (r : ℕ) : Prop :=
  ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s → s ≤ xi y →
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2

/-! ### The inner level

Theorems 4 and 5 use the same inner-parameter estimates. These wrappers retain the
Theorem 5 statements while sharing the proofs from `TheoremFour`.
-/

/-- For `p ∈ rosserPrimes lower y y^{1/s}`: `p < y`, and the inner parameter `t_p - 1` is in the
domain of the opposite flag. -/
theorem rosserPrimes_facts {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : sMin lower ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) :
    1 < p ∧ (p : ℝ) < y ∧ sMin (!lower) ≤ log y / log p - 1 := by
  exact ⟨(prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt,
    TheoremFour.prime_lt_of_mem_rosserPrimes hy (one_le_of_sMin_le hs) hp,
    TheoremFour.sMin_le_inner hy hs hp⟩

/-- `t - 1 ≤ ξ(y/p)` for `t = t_p ≤ ξ(y)`, `1 < p < y`. -/
theorem sub_one_le_xi_div {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p) (hpy : (p : ℝ) < y)
    (ht : log y / log p ≤ xi y) : log y / log p - 1 ≤ xi (y / p) := by
  apply TheoremFour.inner_le_xi hy hp hpy
  -- Convert the logarithmic hypothesis to the prime cutoff used in Theorem 4.
  have hp0 : (0 : ℝ) < p := by positivity
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  rw [← log_le_log_iff (rpow_pos_of_pos (zero_lt_one.trans hy) _) hp0,
    log_rpow_one_div (zero_lt_one.trans hy), div_le_iff₀ (xi_pos hy)]
  simpa only [mul_comm] using (div_le_iff₀ hlp).1 ht

/-- `(y/p)^{1/(t_p - 1)} = p`. -/
theorem rpow_inv_sub_one_eq {y : ℝ} {p : ℕ} (hp : 1 < p) (hpy : (p : ℝ) < y) :
    (y / p) ^ (1 / (log y / log p - 1)) = p := by
  exact TheoremFour.rpow_inner_eq hp hpy

/-- The induction hypothesis at the inner level `(y/p, t_p - 1)`, for `t_p ≤ ξ(y)`. -/
theorem inner_le {c₇ : ℝ} {r : ℕ} (ih : Bound c₇ r) {lower : Bool} {y s : ℝ} (hy : 1 < y)
    (hs : sMin lower ≤ s) {p : ℕ} (hp : p ∈ rosserPrimes lower y (y ^ (1 / s)))
    (ht : log y / log p ≤ xi y) :
    (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * y * (delta (log y / log p - 1) (y / p) *
        errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2)) := by
  obtain ⟨hp1, hpy, hsp⟩ := rosserPrimes_facts hy hs hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp1)
  have hyp : 1 < y / p := by rw [lt_div_iff₀ hp0]; linarith
  have h := ih (!lower) (y / p) (log y / log p - 1) hyp hsp (sub_one_le_xi_div hy hp1 hpy ht)
  rw [rpow_inv_sub_one_eq hp1 hpy] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- Sum the inner induction bounds over `p ≥ y^{1/(ξ-1)}`, then enlarge the prime range
to `p ≥ y^{1/ξ}` so that Corollary 3 applies. -/
theorem sum_inner_le {c₇ : ℝ} (hc₇ : 0 ≤ c₇) {r : ℕ} (ih : Bound c₇ r)
    {lower : Bool} {y s : ℝ} (hy : 1 < y) (hs : sMin lower ≤ s) (hξ : 1 < xi y) :
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / (xi y - 1)) ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * y *
        ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
            (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
            (p * log (y / p) ^ 2) := by
  set P := rosserPrimes lower y (y ^ (1 / s))
  set w := y ^ (1 / (xi y - 1)) with hw
  set φ : ℝ := ((r : ℝ) + 1) / (r + 2)
  set term : ℕ → ℝ := fun p => delta (log y / log p - 1) (y / p) *
    errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2) with hterm
  have hφ0 : 0 ≤ φ := by positivity
  calc
    _ ≤ ∑ p ∈ P.filter (fun p : ℕ => w ≤ p), c₇ * φ * y * term p := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpP, hwp⟩ := mem_filter.1 hp
      obtain ⟨hp1, -, -⟩ := rosserPrimes_facts hy hs hpP
      have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
      have hlp : 0 < log (p : ℝ) := log_pos hp1'
      have ht : log y / log p ≤ xi y := by
        have hlog := log_le_log (by positivity) hwp
        rw [hw, log_rpow_one_div (by linarith)] at hlog
        rw [div_le_iff₀ (by linarith)] at hlog
        rw [div_le_iff₀ hlp]
        nlinarith only [hlog, hlp]
      exact inner_le ih hy hs hpP ht
    _ ≤ ∑ p ∈ P.filter (fun p : ℕ => y ^ (1 / xi y) ≤ p), c₇ * φ * y * term p := by
      refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_
      · obtain ⟨hpP, hwp⟩ := mem_filter.1 hp
        exact mem_filter.2 ⟨hpP, (rpow_one_div_le_rpow_one_div hy.le (by linarith)
          (by linarith)).trans hwp⟩
      · obtain ⟨-, -, hsp⟩ := rosserPrimes_facts hy hs (mem_filter.1 hp).1
        have := delta_pos (one_le_of_sMin_le hsp) (y / p)
        have := errMaj_pos (!lower) (log y / log p - 1)
        simp only [hterm]
        positivity
    _ = _ := (mul_sum ..).symm

/-! ### Closing the induction -/
theorem delta_max_le {s s₀ : ℝ} (hs : 1 ≤ s) (hs₀ : 1 ≤ s₀) (y : ℝ) :
    delta (max s s₀) y ≤ delta s y * delta s₀ y := by
  simpa only [mul_comm] using TheoremFour.delta_max_le hs hs₀ y

/-- The gain from depth `r` to `r + 1`: `(r+2)/(r+3) - (r+1)/(r+2) ≥ ℓ²/(4L²)` when
`r + 3 ≤ 2L/ℓ`. -/
theorem gap_le {r : ℕ} {L ℓ : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ) (h : (r : ℝ) + 3 ≤ 2 * L / ℓ) :
    2 * (ℓ ^ 2 / (8 * L ^ 2)) ≤ ((r : ℝ) + 1 + 1) / (r + 1 + 2) - (r + 1) / (r + 2) := by
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have e : ((r : ℝ) + 1 + 1) / (r + 1 + 2) - (r + 1) / (r + 2) = 1 / ((r + 2) * (r + 3)) := by
    field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hℓ] at h
  have h2 : ((r + 3) * ℓ) ^ 2 ≤ (2 * L) ^ 2 := by gcongr
  have : (r + 2) * (r + 3) * ℓ ^ 2 ≤ 4 * L ^ 2 := by nlinarith [sq_nonneg ℓ]
  rw [show 2 * (ℓ ^ 2 / (8 * L ^ 2)) * ((r + 2) * (r + 3)) =
    (r + 2) * (r + 3) * ℓ ^ 2 / (4 * L ^ 2) by field_simp; ring]
  rw [div_le_one (by positivity)]
  exact this

/-- The final algebra of the inductive step. -/
theorem close_step {c₇ φ φ' Q X ε : ℝ} (hc₇ : 1 ≤ c₇) (hQ : 0 ≤ Q) (hφ1 : φ ≤ 1)
    (hX0 : 0 ≤ X) (hX : X ≤ ε) (hgap : 2 * ε ≤ φ' - φ) :
    Q * ε + c₇ * φ * Q * (1 + X) ≤ c₇ * φ' * Q := by
  have hε : 0 ≤ ε := hX0.trans hX
  have h1 : φ * X ≤ ε := (mul_le_of_le_one_left hX0 hφ1).trans hX
  have h2 : ε ≤ φ' - φ - φ * X := by linarith
  have h3 : c₇ * ε ≤ c₇ * (φ' - φ - φ * X) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 : ε ≤ c₇ * ε := le_mul_of_one_le_left hε hc₇
  nlinarith [mul_le_mul_of_nonneg_left (h4.trans h3) hQ]

/-- The main case of the inductive step ([I71, p. 27]): `y` large and
`r + 3 ≤ 2 log y / log log y`. The hypotheses are the large-`y` facts: the crude count
(`exists_card_small`), Corollary 3 (`cor3_xi`) and the slack (`exists_slack`). -/
theorem step_main {c₇ C : ℝ} (hc₇ : 1 ≤ c₇) {r : ℕ} (ih : Bound c₇ r) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hξ32 : exp 32 ≤ xi y)
    (hsmall : 1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      delta s y * errMaj lower s * y / (8 * log y ^ 4))
    (hcor : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))))
    (hC : 0 ≤ C)
    (hslack : delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) - 1 ≤
      log (log y) ^ 2 / (8 * log y ^ 2))
    (hℓ : 1 ≤ log (log y)) (hmain : (r : ℝ) + 3 ≤ 2 * log y / log (log y)) :
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r + 1} : ℝ) ≤
      c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) * delta s y * errMaj lower s * y /
        log y ^ 2 := by
  have hL0 : 0 < log y := log_pos hy
  have hs1 := one_le_of_sMin_le hs
  have hξ1 : 1 < xi y := by linarith only [four_lt_of_exp_le hξ32]
  set L := log y
  set w := y ^ (1 / (xi y - 1))
  set φ : ℝ := ((r : ℝ) + 1) / (r + 2) with hφ
  set E := C * xi y ^ 2 * pntE (y ^ (1 / xi y))
  set Q := delta s y * errMaj lower s * y / L ^ 2 with hQ
  -- Each loss is at most `ε`; the depth increment supplies at least `2ε`.
  set ε := log (log y) ^ 2 / (8 * L ^ 2) with hε
  set X := delta (exp 32) y * (1 + E) - 1 with hX
  have hδs := delta_pos hs1 y
  have hGs := errMaj_pos lower s
  have hQ0 : 0 ≤ Q := by positivity
  have hφ0 : 0 ≤ φ := by positivity
  have hφ1 : φ ≤ 1 := by rw [hφ, div_le_one (by positivity)]; linarith
  have hE0 : 0 ≤ E := by have := pntE_pos (y ^ (1 / xi y)); positivity
  have hs₀ : (1 : ℝ) ≤ exp 32 := one_le_exp (by norm_num)
  have hδ₀ := one_le_delta hs₀ y
  have hX0 : 0 ≤ X := by
    rw [hX]
    nlinarith only [hδ₀, hE0]
  -- The crude count uses at most `Qε` of the induction gap.
  have hsmallPart : (#(rosserSet lower y w) : ℝ) ≤ Q * ε := by
    calc
      _ ≤ 1 + (#(rosserSet lower y w) : ℝ) := by linarith only
      _ ≤ delta s y * errMaj lower s * y / (8 * L ^ 4) := hsmall
      _ = Q * (1 / (8 * L ^ 2)) := by rw [hQ]; ring
      _ ≤ Q * ε := by
        rw [hε]
        have : (1 : ℝ) ≤ log (log y) ^ 2 := by nlinarith only [hℓ]
        gcongr
  -- The inner induction bounds and Corollary 3 give the main term with relative loss `X`.
  have hlargePart : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => w ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * φ * Q * (1 + X) := by
    refine (sum_inner_le (zero_le_one.trans hc₇) ih hy hs hξ1).trans ?_
    calc
      _ ≤ c₇ * φ * y *
          (delta (max s (exp 32)) y * errMaj lower s / L ^ 2 * (1 + E)) := by
        exact mul_le_mul_of_nonneg_left hcor (by positivity)
      _ = c₇ * φ * (y * errMaj lower s / L ^ 2 * (1 + E)) *
          delta (max s (exp 32)) y := by ring
      _ ≤ c₇ * φ * (y * errMaj lower s / L ^ 2 * (1 + E)) *
          (delta s y * delta (exp 32) y) := by
        exact mul_le_mul_of_nonneg_left (delta_max_le hs1 hs₀ y) (by positivity)
      _ = c₇ * φ * Q * (1 + X) := by rw [hQ, hX]; ring
  have hgap := gap_le (r := r) hL0 (zero_lt_one.trans_le hℓ) hmain
  have hgoal : c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) * delta s y *
      errMaj lower s * y / L ^ 2 = c₇ * (((r : ℝ) + 1 + 1) / (r + 1 + 2)) * Q := by
    rw [hQ]; push_cast; ring
  rw [hgoal]
  calc
    _ ≤ #(rosserSet lower y w) + ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => w ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) :=
      card_filter_succ_le r lower y (y ^ (1 / s)) w
    _ ≤ Q * ε + c₇ * φ * Q * (1 + X) := add_le_add hsmallPart hlargePart
    _ ≤ _ := close_step hc₇ hQ0 hφ1 hX0 hslack hgap

/-! ### The small-`y` case -/

/-- `ξ(y) ≤ log c₈ / (log log 3)^{11/5}` for `1 < y < c₈`. -/
theorem xi_le_of_lt {y c₈ : ℝ} (hy : 1 < y) (hyc : y < c₈) :
    xi y ≤ log c₈ / log (log 3) ^ (11 / 5 : ℝ) := by
  have h3 := one_lt_log_three
  have hll : 0 < log (log 3) := log_pos h3
  have hlam : log (log 3) ≤ lam y := by
    unfold lam
    exact log_le_log (by linarith) (log_le_log (by norm_num) (by linarith))
  rw [xi_eq_lam]
  exact div_le_div₀ (log_nonneg (by linarith)) (log_le_log (by linarith) hyc.le)
    (rpow_pos_of_pos hll _) (rpow_le_rpow hll.le hlam (by norm_num))

/-- For `1 < y < c₈` the count is at most `y`, which is at most the bound once
`c₇ ≥ 2 log² c₈ / min (𝔣(Ξ), 𝔉(Ξ))` with `Ξ = log c₈ / (log log 3)^{11/5}`. -/
theorem small_le {c₈ c₇ : ℝ}
    (hc₇ : 2 * log c₈ ^ 2 / min (errMaj true (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))
      (errMaj false (log c₈ / log (log 3) ^ (11 / 5 : ℝ))) ≤ c₇)
    (r : ℕ) (lower : Bool) {y s : ℝ} (hy : 1 < y) (hyc : y < c₈) (hs : sMin lower ≤ s)
    (hsξ : s ≤ xi y) :
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2 := by
  set Ξ := log c₈ / log (log 3) ^ (11 / 5 : ℝ) with hΞ
  set Gm := min (errMaj true Ξ) (errMaj false Ξ) with hGm
  have hGm0 : 0 < Gm := lt_min (errMaj_pos _ _) (errMaj_pos _ _)
  have hs1 := one_le_of_sMin_le hs
  have hL0 : 0 < log y := log_pos hy
  have hLc : log y ≤ log c₈ := log_le_log (by linarith) hyc.le
  have hG : Gm ≤ errMaj lower s := by
    have h1 : errMaj lower Ξ ≤ errMaj lower s :=
      errMaj_antitone lower (hsξ.trans (xi_le_of_lt hy hyc))
    cases lower
    · exact (min_le_right _ _).trans h1
    · exact (min_le_left _ _).trans h1
  have hδ := one_le_delta hs1 y
  have hφ : (1 : ℝ) / 2 ≤ ((r : ℝ) + 1) / (r + 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith [r.cast_nonneg (α := ℝ)]
  have hc₇' : 2 * log c₈ ^ 2 ≤ c₇ * Gm := by rwa [div_le_iff₀ hGm0] at hc₇
  have hcount : (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤ y :=
    (Nat.cast_le.2 (card_filter_le _ _)).trans (card_rosserSet_le hy hs1)
  refine hcount.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hc₇0 : 0 ≤ c₇ := by
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (log c₈))
    nlinarith
  have key : log y ^ 2 ≤ c₇ * (((r : ℝ) + 1) / (r + 2)) * delta s y * errMaj lower s := by
    have h1 : log y ^ 2 ≤ log c₈ ^ 2 := by gcongr
    have h2 : c₇ * Gm / 2 ≤ c₇ * (((r : ℝ) + 1) / (r + 2)) * delta s y * errMaj lower s := by
      have : c₇ * Gm / 2 = c₇ * (1 / 2) * 1 * Gm := by ring
      rw [this]
      gcongr
    linarith
  nlinarith

/-! ### Theorem 5 -/
theorem exists_bound : ∃ c₇ : ℝ, 1 ≤ c₇ ∧ ∀ r, Bound c₇ r := by
  obtain ⟨y₁, hsmall⟩ := exists_card_small
  obtain ⟨C, y₂, hC0, hcor⟩ := cor3_xi
  obtain ⟨y₃, hslack⟩ := exists_slack C hC0
  obtain ⟨y₄, hdepth⟩ := exists_card_filter_rosserSet_add_eq
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  -- Choose one threshold beyond which all five estimates apply.
  have hlarge := (eventually_ge_atTop (3 : ℝ)).and
    ((eventually_atTop.2 ⟨y₁, hsmall⟩).and
      ((eventually_atTop.2 ⟨y₂, fun y hy lower s hs ↦ hcor lower y s hy hs⟩).and
        ((eventually_atTop.2 ⟨y₃, hslack⟩).and
          ((eventually_atTop.2 ⟨y₄, hdepth⟩).and (eventually_atTop.2 ⟨y₅, hxi⟩)))))
  obtain ⟨c₈, hlarge⟩ := eventually_atTop.1 hlarge
  set c₇ := max 1 (2 * log c₈ ^ 2 / min (errMaj true (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))
    (errMaj false (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))) with hc₇
  have hc₇1 : 1 ≤ c₇ := le_max_left _ _
  refine ⟨c₇, hc₇1, fun r => ?_⟩
  induction r with
  | zero =>
    intro lower y s hy hs hsξ
    rcases lt_or_ge y c₈ with hyc | hyc
    · exact small_le (le_max_right _ _) 0 lower hy hyc hs hsξ
    obtain ⟨hy3, hsmall, -, -, -, -⟩ := hlarge y hyc
    have hL1 : 1 ≤ log y := by
      have := log_le_log (by norm_num) hy3
      linarith [one_lt_log_three]
    have h := hsmall lower s hs hsξ
    rw [card_filter_rosserSet_zero]
    have hN : (0 : ℝ) ≤ #(rosserSet lower y (y ^ (1 / (xi y - 1)))) := Nat.cast_nonneg _
    have hQ : 0 ≤ delta s y * errMaj lower s * y := by
      have := delta_pos (one_le_of_sMin_le hs) y
      have := errMaj_pos lower s
      have : 0 < y := by linarith
      positivity
    push_cast
    have : delta s y * errMaj lower s * y / (8 * log y ^ 4) ≤
        c₇ * ((0 + 1) / (0 + 2)) * delta s y * errMaj lower s * y / log y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : log y ^ 2 ≤ 4 * log y ^ 4 := by
        have h1 : 1 ≤ log y ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (log y))]
      have h5 : delta s y * errMaj lower s * y * log y ^ 2 ≤
          delta s y * errMaj lower s * y * (4 * log y ^ 4) :=
        mul_le_mul_of_nonneg_left h4 hQ
      nlinarith [mul_le_mul_of_nonneg_right hc₇1 (mul_nonneg hQ (pow_pos (by linarith :
        (0 : ℝ) < log y) 4).le)]
    linarith
  | succ r ih =>
    intro lower y s hy hs hsξ
    rcases lt_or_ge y c₈ with hyc | hyc
    · exact small_le (le_max_right _ _) (r + 1) lower hy hyc hs hsξ
    obtain ⟨-, hsmall, hcor, hslack, hdepth, hxi⟩ := hlarge y hyc
    by_cases hdeep : 2 * log y / log (log y) < ((r + 1 : ℕ) : ℝ) + 2
    · -- the depth has stabilised
      have h := hdepth lower (r + 1) (y ^ (1 / s)) hdeep 1
      simp only [Nat.add_sub_cancel] at h
      rw [h]
      refine (ih lower y s hy hs hsξ).trans ?_
      have hQ : 0 ≤ delta s y * errMaj lower s * y / log y ^ 2 := by
        have := delta_pos (one_le_of_sMin_le hs) y
        have := errMaj_pos lower s
        have : 0 < y := by linarith
        positivity
      have hφ : ((r : ℝ) + 1) / (r + 2) ≤ (((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2) := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      calc c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2
          = c₇ * ((r + 1) / (r + 2)) * (delta s y * errMaj lower s * y / log y ^ 2) := by ring
        _ ≤ c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) *
            (delta s y * errMaj lower s * y / log y ^ 2) := by gcongr
        _ = _ := by ring
    · -- the main case
      obtain ⟨-, hξ32, -, -⟩ := hxi
      obtain ⟨hsl, hℓ⟩ := hslack
      have hmain : (r : ℝ) + 3 ≤ 2 * log y / log (log y) := by
        push_cast at hdeep; linarith
      exact step_main hc₇1 ih hy hs hξ32 (hsmall lower s hs hsξ)
        (hcor lower s hs) hC0 hsl hℓ hmain

end IwaniecLinearSieve.TheoremFive

namespace IwaniecLinearSieve

open Finset TheoremFive

/-- [I71, Theorem 5] (in the indexing of our recursion): there is `c₇` such that for all depths
`r`, both sieves, `y > 1` and `sMin lower ≤ s ≤ ξ(y)`, the number of elements of
`rosserSet lower y y^{1/s}` with at most `r` prime factors is at most
`c₇ (r+1)/(r+2) δ(s, y) G(s) y / log² y`, with `G = errMaj lower` (`𝔣` or `𝔉`). -/
theorem theorem5 : ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y →
    sMin lower ≤ s → s ≤ xi y →
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / Real.log y ^ 2 := by
  obtain ⟨c₇, hc₇, h⟩ := exists_bound
  exact ⟨c₇, by linarith, fun r => h r⟩

/-- `δ(s, y) ≤ (1 + 9 log⁵ 3)^{15}` for `1 ≤ s ≤ 3` and `log y ≥ 1`. -/
theorem delta_le_of_le_three {s y : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hy : 1 ≤ Real.log y) :
    delta s y ≤ (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) := by
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hl3 : Real.log s ≤ Real.log 3 := Real.log_le_log (by linarith) hs3
  have hx : s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2 ≤ 9 * Real.log 3 ^ 5 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 ≤ 9 := by nlinarith
    have h2 : Real.log s ^ 5 ≤ Real.log 3 ^ 5 := by gcongr
    have h3 : 1 ≤ Real.log y ^ 2 := by nlinarith
    have h4 : s ^ 2 * Real.log s ^ 5 ≤ 9 * Real.log 3 ^ 5 :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h5 : 0 ≤ Real.log 3 ^ 5 := by positivity
    nlinarith
  have hx0 : 0 ≤ s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2 := by positivity
  rw [delta]
  calc (1 + s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2) ^ (5 * s)
      ≤ (1 + 9 * Real.log 3 ^ 5) ^ (5 * s) := Real.rpow_le_rpow (by linarith) (by linarith)
        (by linarith)
    _ ≤ (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- The consequence of Theorem 5 used for `LinearSieveEstimate`: the lower-bound sieve support
has `#(rosserSet true y y^{1/s}) ≪ y / log² y` uniformly for `2 ≤ s ≤ 3`. -/
theorem theorem5_card_rosserSet_le : ∃ K y₀ : ℝ, ∀ y ≥ y₀, ∀ s ∈ Set.Icc (2 : ℝ) 3,
    (#(rosserSet true y (y ^ (1 / s))) : ℝ) ≤ K * y / Real.log y ^ 2 := by
  obtain ⟨c₇, hc₇, h5⟩ := theorem5
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  set D := (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) with hD
  refine ⟨c₇ * D * 2, max y₅ 3, fun y hy s hs => ?_⟩
  obtain ⟨hy1, hξ, -, -⟩ := hxi y (le_of_max_le_left hy)
  have hy3 : 3 ≤ y := le_of_max_le_right hy
  have hL1 : 1 ≤ Real.log y := by
    have := Real.log_le_log (by norm_num) hy3
    linarith [one_lt_log_three]
  have hsξ : s ≤ xi y := hs.2.trans (by linarith [Real.add_one_le_exp (32 : ℝ)])
  set z := y ^ (1 / s)
  have hall : (rosserSet true y z).filter (fun d => #d.primeFactors ≤ #(primesLT z)) =
      rosserSet true y z :=
    filter_true_of_mem fun d hd => card_le_card (primeFactors_subset_of_mem_rosserSet hd)
  have h := h5 #(primesLT z) true y s hy1 hs.1 hsξ
  rw [hall] at h
  refine h.trans ?_
  have hδ := delta_le_of_le_three (by linarith [hs.1]) hs.2 hL1 (y := y)
  have hδ0 := delta_pos (by linarith [hs.1] : (1 : ℝ) ≤ s) y
  have hG := errMaj_le_two true s
  have hG0 := errMaj_pos true s
  have hφ : ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hφ0 : (0 : ℝ) ≤ ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) := by positivity
  have hyL : 0 ≤ y / Real.log y ^ 2 := by positivity
  calc c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s * y /
        Real.log y ^ 2
      = c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s *
          (y / Real.log y ^ 2) := by ring
    _ ≤ c₇ * 1 * D * 2 * (y / Real.log y ^ 2) := by gcongr
    _ = c₇ * D * 2 * y / Real.log y ^ 2 := by ring

end IwaniecLinearSieve
