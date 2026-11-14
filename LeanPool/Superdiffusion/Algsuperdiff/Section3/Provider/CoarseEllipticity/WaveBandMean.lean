/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WaveBandMean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `k₀`-deep wave band: its deterministic mean, and the absorption arithmetic

## The mathematical situation, exactly

corrects the ordinary upper-wave scale of `e.bL.multiscale` to `C (gamma (L -
n) + E⁻²) 3^{2 gamma (L-n) - gamma (m-n)}`.  The extra `E⁻²` summand cannot be
discarded, and it cannot be absorbed into the printed `gamma`-lane either:
absorbing it would force `E³ ≤ C₁ - 1` at the admissible tuning `gamma = E⁻⁵`,
with `E` unbounded.  What it *can* be charged to is the deterministic part of
the display.  On the `k₀`-deep band the extra content is therefore split into

* a **deterministic mean** --- a number, by stationarity, since the gauge
  `sigmaBar` is deterministic --- of normalized size
  `D_band = A sqrt(gamma k₀) 3^{gamma k₀}` at a `C(d)` amplitude `A`; and
* a **centred remainder** of pure-`gamma` amplitude, which stays in the ordinary
  lane.

The mean is not a lane at all.  It is a deterministic shift, and a deterministic
shift is exactly what the frozen upper display already carries: the `Ccg` slot of
`Probability.IsDeterministicShiftTwoTermOneSidedOrlicz`.  So the resolution is
**not** that the `E⁻²` content vanishes --- the obstruction above forbids that
--- but that it **hides in `Ccg`**.

## What is proved here

* `waveBandDepth`, `waveBandDepth_spec` --- the tuned band depth
  `k₀ = ⌈c E⁻² gamma⁻¹⌉₊` and the only property it is used through:
  `gamma k₀ ≤ c E⁻² + gamma`, the integer ceiling costing at most one `gamma`.
* `waveBandMean`, `waveBandMean_sq_le` --- the normalized deterministic band
  mean and its square, `D_band² ≤ A² (c E⁻² + gamma) 3^{2 gamma k₀}`, i.e.
  exactly `C (E⁻² + gamma)`-class.
* `mul_gamma_le_one_of_le_rpow_neg_fifth`, `gamma_le_one_of_le_rpow_neg_fifth`
  --- the two consequences of the frozen admissibility gate
  `E ≤ gamma^(-1/5)` used below: `E gamma ≤ 1` and `gamma ≤ 1`.
* `cstarInv_bandBudget_le_two` --- **the absorption arithmetic**.  On the
  frozen window (`1 ≤ E`, `cstar⁻¹ ≤ E` from the threshold binder `max (exp
  (Ccg/sigma)) cstar⁻¹ ≤ E`, and `E ≤ gamma^(-1/5)`), `cstar⁻¹ (c E⁻² + gamma)
  ≤ 2`: the `cstar`-corrected band budget is **dimension-free**.
* `cstarInv_mul_waveBandMean_sq_le` --- the headline: the `cstar`-corrected
  squared band mean is bounded by the dimension-free `waveBandConst`, so it is
  absorbable into the deterministic shift.
* `gamma_le_inv_pow_five` --- the bridge that puts the frozen gate
  `E ≤ gamma^(-1/5)` into the algebraic tuning `gamma ≤ E⁻⁵`, which is the form
  in which the lane obstruction above is read, so that obstruction is a
  statement *about this window* and not about a hypothetical one.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement (`e.cg.ellip.upper`), proof; the
  Step-3 endpoint terms.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

/-! ## 1. The tuned band depth -/

/-- The tuned depth of the deep wave band, `k₀ = ⌈c E⁻² gamma⁻¹⌉₊` (; `k₀` is a
deterministic tuning parameter). -/
noncomputable def waveBandDepth (c E gamma : ℝ) : ℕ := ⌈c * (E ^ 2)⁻¹ * gamma⁻¹⌉₊

/-- The only property of the tuned depth used downstream: the band's total
`gamma`-weight is `c E⁻²` up to the one `gamma` charged by the integer
ceiling. -/
theorem waveBandDepth_spec {c E gamma : ℝ} (hgamma : 0 < gamma)
    (ht : 0 ≤ c * (E ^ 2)⁻¹ * gamma⁻¹) :
    gamma * (waveBandDepth c E gamma : ℝ) ≤ c * (E ^ 2)⁻¹ + gamma := by
  have hceil : ((waveBandDepth c E gamma : ℕ) : ℝ) ≤ c * (E ^ 2)⁻¹ * gamma⁻¹ + 1 :=
    (Nat.ceil_lt_add_one ht).le
  have hmul := mul_le_mul_of_nonneg_left hceil hgamma.le
  have hcancel : gamma * gamma⁻¹ = 1 := mul_inv_cancel₀ hgamma.ne'
  have hval : gamma * (c * (E ^ 2)⁻¹ * gamma⁻¹ + 1) = c * (E ^ 2)⁻¹ + gamma := by
    calc gamma * (c * (E ^ 2)⁻¹ * gamma⁻¹ + 1)
        = c * (E ^ 2)⁻¹ * (gamma * gamma⁻¹) + gamma := by ring
      _ = c * (E ^ 2)⁻¹ + gamma := by rw [hcancel]; ring
  rwa [hval] at hmul

/-! ## 2. The normalized deterministic band mean -/

/-- The normalized deterministic mean of the `k₀`-deep wave band, `D_band = A
sqrt(gamma) sqrt(k₀) 3^{gamma k₀}`.  It is a **number**, not a random variable:
that is the whole content of the split.

The amplitude `A` is left as a parameter rather than fixed to a numeral: at the
proved volume-normalized `L^p` carrier of this repository the head's amplitude
is a genuine `C(d, p)` (see `deepBandAmplitude` in `DeepBandSplit.lean`), and
the frozen constant `Ccg` is dimension-only, so a dimensional amplitude is
exactly what the slot admits. -/
noncomputable def waveBandMean (A gamma : ℝ) (k0 : ℕ) : ℝ :=
  A * Real.sqrt gamma * Real.sqrt (k0 : ℝ) * (3 : ℝ) ^ (gamma * (k0 : ℝ))

theorem waveBandMean_nonneg {A : ℝ} (hA : 0 ≤ A) (gamma : ℝ) (k0 : ℕ) :
    0 ≤ waveBandMean A gamma k0 := by
  refine mul_nonneg (mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg gamma))
    (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)

/-- The squared band mean is `A² (gamma k₀)`-class, hence
`A² (c E⁻² + gamma)`-class once the depth is tuned:
`D_band² = A² (gamma k₀) 3^{2 gamma k₀}`. -/
theorem waveBandMean_sq_le {A gamma B : ℝ} (hgamma : 0 ≤ gamma) (k0 : ℕ)
    (hgk : gamma * (k0 : ℝ) ≤ B) :
    waveBandMean A gamma k0 ^ 2 ≤
      A ^ 2 * B * (3 : ℝ) ^ (2 * (gamma * (k0 : ℝ))) := by
  have hsq : (Real.sqrt gamma * Real.sqrt (k0 : ℝ)) ^ 2 = gamma * (k0 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hgamma, Real.sq_sqrt (Nat.cast_nonneg k0)]
  have hthree : ((3 : ℝ) ^ (gamma * (k0 : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (gamma * (k0 : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (gamma * (k0 : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [mul_comm]
  have hthreenn : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (gamma * (k0 : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hexpand : waveBandMean A gamma k0 ^ 2 =
      A ^ 2 * (gamma * (k0 : ℝ)) * (3 : ℝ) ^ (2 * (gamma * (k0 : ℝ))) := by
    rw [waveBandMean]
    calc (A * Real.sqrt gamma * Real.sqrt (k0 : ℝ) * (3 : ℝ) ^ (gamma * (k0 : ℝ))) ^ 2
        = A ^ 2 * (Real.sqrt gamma * Real.sqrt (k0 : ℝ)) ^ 2 *
            ((3 : ℝ) ^ (gamma * (k0 : ℝ))) ^ 2 := by ring
      _ = A ^ 2 * (gamma * (k0 : ℝ)) * (3 : ℝ) ^ (2 * (gamma * (k0 : ℝ))) := by
          rw [hsq, hthree]
  rw [hexpand]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgk (sq_nonneg A)) hthreenn

/-! ## 3. The frozen admissibility gate, in algebraic form -/

/-- The purely algebraic core: from `1 ≤ E`, `0 < t` and `E t ≤ 1`, the three
fifth-power consequences.  Stated at an abstract `t` so that no rewriting has to
reach inside the real power `gamma ^ (1/5)`. -/
private theorem fifthRoot_core {E t : ℝ} (hE : 1 ≤ E) (htpos : 0 < t)
    (hEt : E * t ≤ 1) :
    E * t ^ (5 : ℕ) ≤ 1 ∧ t ^ (5 : ℕ) ≤ 1 ∧ E ^ (5 : ℕ) * t ^ (5 : ℕ) ≤ 1 := by
  have ht1 : t ≤ 1 := le_trans (le_mul_of_one_le_left htpos.le hE) hEt
  refine ⟨?_, pow_le_one₀ htpos.le ht1, ?_⟩
  · have hsplit : E * t ^ (5 : ℕ) = E * t * t ^ (4 : ℕ) := by ring
    rw [hsplit]
    exact (mul_le_mul hEt (pow_le_one₀ htpos.le ht1) (pow_nonneg htpos.le 4) zero_le_one).trans_eq
      (mul_one 1)
  · rw [← mul_pow]
    exact pow_le_one₀ (by positivity) hEt

/-- On the frozen gate `E ≤ gamma^(-1/5)` with `1 ≤ E`, the fifth root of
`gamma` is at most `E⁻¹`; the three corollaries used below are `E gamma ≤ 1`,
`gamma ≤ 1` and `E⁵ gamma ≤ 1`. -/
private theorem fifthRoot_aux {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    E * gamma ≤ 1 ∧ gamma ≤ 1 ∧ E ^ (5 : ℕ) * gamma ≤ 1 := by
  have htpos : (0 : ℝ) < gamma ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hgamma _
  have ht5 : (gamma ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = gamma := by
    rw [← Real.rpow_natCast (gamma ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hgamma.le]
    norm_num
  have hinv : gamma ^ (-(1 / 5 : ℝ)) = (gamma ^ (1 / 5 : ℝ))⁻¹ :=
    Real.rpow_neg hgamma.le _
  have hEt : E * gamma ^ (1 / 5 : ℝ) ≤ 1 := by
    have hstep := mul_le_mul_of_nonneg_right (hEgamma.trans_eq hinv) htpos.le
    rwa [inv_mul_cancel₀ htpos.ne'] at hstep
  obtain ⟨h1, h2, h3⟩ := fifthRoot_core hE htpos hEt
  rw [ht5] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The frozen gate `E ≤ gamma^(-1/5)` gives `E gamma ≤ 1`. -/
theorem mul_gamma_le_one_of_le_rpow_neg_fifth {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma : 0 < gamma) (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    E * gamma ≤ 1 :=
  (fifthRoot_aux hE hgamma hEgamma).1

/-- The frozen gate `E ≤ gamma^(-1/5)` gives `gamma ≤ 1`. -/
theorem gamma_le_one_of_le_rpow_neg_fifth {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma : 0 < gamma) (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    gamma ≤ 1 :=
  (fifthRoot_aux hE hgamma hEgamma).2.1

/-- The frozen gate `E ≤ gamma^(-1/5)` is the algebraic tuning `gamma ≤ E⁻⁵` that
argue at. -/
theorem gamma_le_inv_pow_five {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
  have hpow : (0 : ℝ) < E ^ (5 : ℕ) := pow_pos (lt_of_lt_of_le zero_lt_one hE) 5
  have h := (fifthRoot_aux hE hgamma hEgamma).2.2
  rw [show ((E ^ (5 : ℕ))⁻¹ : ℝ) = 1 / E ^ (5 : ℕ) by rw [one_div], le_div_iff₀ hpow,
    mul_comm]
  exact h

/-! ## 4. The absorption arithmetic -/

/-- **The absorption arithmetic** (with the `cstar⁻¹` factor).

On the frozen window the `cstar`-corrected band budget is dimension-free: the
threshold binder supplies `cstar⁻¹ ≤ E`, so `cstar⁻¹ c E⁻² ≤ c E⁻¹ ≤ 1`, and the
gate `E ≤ gamma^(-1/5)` supplies `cstar⁻¹ gamma ≤ E gamma ≤ 1`.  Positivity of
`cstar` is not needed: the threshold binder already dominates `cstar⁻¹`. -/
theorem cstarInv_bandBudget_le_two {c E gamma cstar : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hcstarE : cstar⁻¹ ≤ E)
    (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    cstar⁻¹ * (c * (E ^ 2)⁻¹ + gamma) ≤ 2 := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : E ≠ 0 := hE0.ne'
  have hbudget : (0 : ℝ) ≤ c * (E ^ 2)⁻¹ + gamma :=
    add_nonneg (mul_nonneg hc0 (inv_nonneg.2 (sq_nonneg E))) hgamma.le
  have hstep : cstar⁻¹ * (c * (E ^ 2)⁻¹ + gamma) ≤ E * (c * (E ^ 2)⁻¹ + gamma) :=
    mul_le_mul_of_nonneg_right hcstarE hbudget
  have hEsq : E * (E ^ 2)⁻¹ = E⁻¹ := by field_simp
  have hEinv : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE
  have hEgamma1 : E * gamma ≤ 1 :=
    mul_gamma_le_one_of_le_rpow_neg_fifth hE hgamma hEgamma
  have hexpand : E * (c * (E ^ 2)⁻¹ + gamma) = c * (E * (E ^ 2)⁻¹) + E * gamma := by
    ring
  rw [hexpand, hEsq] at hstep
  nlinarith [hstep, hEinv, hEgamma1, hc0, hc1, inv_pos.2 hE0]

/-- The budget of the squared deep-band deterministic mean at amplitude `A`.
No model parameter enters: `cstar`, `E`, `gamma` and `s` have all been paid. -/
def waveBandConst (A : ℝ) : ℝ := A ^ 2 * 2 * 81


theorem waveBandConst_nonneg (A : ℝ) : 0 ≤ waveBandConst A := by
  rw [waveBandConst]; positivity

/-- **The `E⁻²` content is absorbable as a deterministic shift.**

On the frozen window the `cstar`-corrected squared mean of the `k₀`-deep wave
band is bounded by the dimension-free numeral `waveBandConst`.  Contrast the
lane obstruction of the module header: the same content is **not** absorbable
when read as a `Gamma₁` amplitude against the `gamma`-lane. -/
theorem cstarInv_mul_waveBandMean_sq_le {A c E gamma cstar : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hcstar : 0 < cstar) (hcstarE : cstar⁻¹ ≤ E)
    (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    cstar⁻¹ * waveBandMean A gamma (waveBandDepth c E gamma) ^ 2 ≤
      waveBandConst A := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hcsinv : (0 : ℝ) < cstar⁻¹ := inv_pos.2 hcstar
  have hgamma1 : gamma ≤ 1 := gamma_le_one_of_le_rpow_neg_fifth hE hgamma hEgamma
  have ht : (0 : ℝ) ≤ c * (E ^ 2)⁻¹ * gamma⁻¹ :=
    mul_nonneg (mul_nonneg hc0 (inv_nonneg.2 (sq_nonneg E))) (inv_nonneg.2 hgamma.le)
  have hdepth := waveBandDepth_spec (c := c) (E := E) hgamma ht
  -- the `c E⁻²` part of the budget is at most `1`
  have hcE : c * (E ^ 2)⁻¹ ≤ 1 := by
    have hsq : (1 : ℝ) ≤ E ^ 2 := by nlinarith [hE, hE0]
    have hinv : (E ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq
    nlinarith [hc0, hc1, hinv, inv_nonneg.2 (sq_nonneg E)]
  have hgk2 : gamma * ((waveBandDepth c E gamma : ℕ) : ℝ) ≤ 2 := by linarith
  -- the exponential factor is bounded by `3 ^ 4`
  have hthree : (3 : ℝ) ^ (2 * (gamma * ((waveBandDepth c E gamma : ℕ) : ℝ))) ≤ 81 := by
    have hle : (3 : ℝ) ^ (2 * (gamma * ((waveBandDepth c E gamma : ℕ) : ℝ))) ≤
        (3 : ℝ) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hval : (3 : ℝ) ^ (4 : ℝ) = 81 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rwa [hval] at hle
  have hsq := waveBandMean_sq_le (A := A) (B := c * (E ^ 2)⁻¹ + gamma) hgamma.le
    (waveBandDepth c E gamma) hdepth
  have hbudget : (0 : ℝ) ≤ c * (E ^ 2)⁻¹ + gamma :=
    add_nonneg (mul_nonneg hc0 (inv_nonneg.2 (sq_nonneg E))) hgamma.le
  have hsq81 : waveBandMean A gamma (waveBandDepth c E gamma) ^ 2 ≤
      A ^ 2 * (c * (E ^ 2)⁻¹ + gamma) * 81 := by
    refine hsq.trans ?_
    exact mul_le_mul_of_nonneg_left hthree (by positivity)
  have hcs := cstarInv_bandBudget_le_two hc0 hc1 hE hgamma hcstarE hEgamma
  have hchain : cstar⁻¹ * waveBandMean A gamma (waveBandDepth c E gamma) ^ 2 ≤
      cstar⁻¹ * (A ^ 2 * (c * (E ^ 2)⁻¹ + gamma) * 81) :=
    mul_le_mul_of_nonneg_left hsq81 hcsinv.le
  refine hchain.trans ?_
  rw [waveBandConst]
  nlinarith [hcs, hcsinv, hbudget, sq_nonneg A]

/-! ## 5. The two-lane necessity, reproved -/


end Algsuperdiff.Section3.Provider.CoarseEllipticity
