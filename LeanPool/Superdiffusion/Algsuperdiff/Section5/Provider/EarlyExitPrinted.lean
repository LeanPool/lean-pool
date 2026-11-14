/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OneStepLaplaceComposer
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LengthTimeScale

/-!
# EarlyExitPrinted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The printed early-exit exponent

This file prices the integer subtraction and division in the canonical chain
length, and combines that discrete estimate with the auxiliary-scale comparison
into the printed bound on the early-exit exponent.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open HCPolySupport MarkovProcess MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The explicit size threshold which absorbs both endpoint losses and the
integer division by the overlap multiplicity. -/
def earlyExitBaseScale (d : ℕ) : ℕ := 64 * (d + 1 + 3 ^ d)

/-- The explicit coefficient left after the two factor-two losses and the
factor three in the auxiliary-scale comparison. -/
def earlyExitDecayConstant (d : ℕ) (gamma delta kappa : ℝ) : ℝ :=
  kappa * delta ^ (1 - gamma)⁻¹ / (192 * (3 : ℝ) ^ d)

/-- Before taking real casts, the canonical chain contains the quotient by
`16 * 3^d`; the constant `64` in `earlyExitBaseScale` pays for the endpoint
subtractions. -/
theorem div_sixteen_pow_le_earlyExitChainLength (d k : ℕ)
    (hlarge : 64 * (d + 1) ≤ 3 ^ k) :
    3 ^ k / (16 * 3 ^ d) ≤ earlyExitChainLength d k := by
  have hq : 0 < 3 ^ d := by positivity
  have hp16 : (3 ^ k / (16 * 3 ^ d)) * 3 ^ d ≤ 3 ^ k / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 16)]
    calc
      (3 ^ k / (16 * 3 ^ d)) * 3 ^ d * 16 =
          (3 ^ k / (16 * 3 ^ d)) * (16 * 3 ^ d) := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 3 ^ k := Nat.div_mul_le_self _ _
  rw [earlyExitChainLength, Nat.le_div_iff_mul_le hq]
  apply hp16.trans
  unfold earlyExitTraceCount
  have hfloor := Nat.lt_mul_div_succ (3 * 3 ^ k) (by norm_num : 0 < 4)
  have hdiv := Nat.div_mul_le_self (3 ^ k) 16
  omega

/-- In real form, after one further factor two for the final quotient remainder,
the canonical chain has length at least `3^k / (32 * 3^d)`. -/
theorem earlyExitChainLength_lower (d k : ℕ)
    (hlarge : earlyExitBaseScale d ≤ 3 ^ k) :
    (3 : ℝ) ^ k / (32 * (3 : ℝ) ^ d) ≤ (earlyExitChainLength d k : ℝ) := by
  have hlarge' : 64 * (d + 1) ≤ 3 ^ k :=
    (Nat.mul_le_mul_left 64 (Nat.le_add_right (d + 1) (3 ^ d))).trans hlarge
  have hchain := div_sixteen_pow_le_earlyExitChainLength d k hlarge'
  have hden : 16 * 3 ^ d ≤ 3 ^ k := by
    calc
      16 * 3 ^ d ≤ 64 * (d + 1 + 3 ^ d) := by omega
      _ ≤ 3 ^ k := hlarge
  have hquot : 1 ≤ 3 ^ k / (16 * 3 ^ d) :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 16 * 3 ^ d)).2 (by simpa using hden)
  have hlt := Nat.lt_mul_div_succ (3 ^ k) (by positivity : 0 < 16 * 3 ^ d)
  have hnat : 3 ^ k ≤ 32 * 3 ^ d * earlyExitChainLength d k := by
    calc
      3 ^ k ≤ 16 * 3 ^ d * (3 ^ k / (16 * 3 ^ d) + 1) := hlt.le
      _ ≤ 16 * 3 ^ d * (2 * (3 ^ k / (16 * 3 ^ d))) := by gcongr; omega
      _ = (32 * 3 ^ d) * (3 ^ k / (16 * 3 ^ d)) := by ring
      _ ≤ (32 * 3 ^ d) * earlyExitChainLength d k :=
        Nat.mul_le_mul_left _ hchain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (3 : ℝ) ^ d)]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, mul_comm] using
    (show ((3 ^ k : ℕ) : ℝ) ≤ ((32 * 3 ^ d * earlyExitChainLength d k : ℕ) : ℝ) by
      exact_mod_cast hnat)

/-- The lower half of the auxiliary-scale straddle bounds the printed minimum
by the next displacement scale.  The factor three is the single successor
scale loss. -/
theorem displacementMinScale_lt_three_mul_displacementScale
    {nu cstar gamma delta t : ℝ} {m n : ℤ}
    (hnu : 0 < nu) (ht : 0 < t) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hnm : n ≤ m)
    (hn : (3 : ℝ) ^ n ≤ auxiliaryScaleBound nu cstar gamma delta t m) :
    displacementMinScale nu cstar gamma t m <
      3 * displacementScale delta gamma (m - n).toNat := by
  let k : ℕ := (m - n).toNat
  have hkcast : (k : ℤ) = m - n := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hnm)
  have hnot : ¬ displacementScale delta gamma (k + 1) ≤
      displacementMinScale nu cstar gamma t m := by
    intro hle
    have hsep := auxiliaryScale_le_sub_of_displacementScale_le hnu ht hdelta hdelta1
      hcstar hgamma hgamma1 hn hle
    rw [Nat.cast_add, Nat.cast_one, hkcast] at hsep
    omega
  have hlt := lt_of_not_ge hnot
  calc
    displacementMinScale nu cstar gamma t m < displacementScale delta gamma (k + 1) := hlt
    _ = 3 * displacementScale delta gamma k := by
      simp only [displacementScale, pow_succ]
      ring

/-- The explicit cost of comparing the two terms of the effective diffusivity
with the two terms in `auxiliaryScaleBound`. -/
def earlyExitProfileCost (cstar gamma : ℝ) : ℝ :=
  3 + 3 * (Real.sqrt (cstar * gamma⁻¹)) ^ gamma

private theorem effectiveDiffusivity_le_add {nu cstar gamma s : ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hs : 0 < s) :
    effectiveDiffusivity nu cstar gamma s ≤
      nu + Real.sqrt (cstar * gamma⁻¹) * s ^ gamma := by
  have hcg : 0 ≤ cstar * gamma⁻¹ := by positivity
  have hs2g : 0 ≤ s ^ (2 * gamma) := Real.rpow_nonneg hs.le _
  rw [effectiveDiffusivity]
  refine (HCPolySupport.sqrt_add_le_add_sqrt_of_nonneg (sq_nonneg nu)
    (mul_nonneg hcg hs2g)).trans_eq ?_
  have hnuSq : Real.sqrt (nu ^ (2 : ℕ)) = nu := Real.sqrt_sq_eq_abs nu ▸ abs_of_pos hnu
  have hprod : Real.sqrt (cstar * gamma⁻¹ * s ^ (2 * gamma)) =
      Real.sqrt (cstar * gamma⁻¹) * s ^ gamma := by
    rw [Real.sqrt_mul hcg]
    congr 1
    have hsroot : s ^ (2 * gamma) = (s ^ gamma) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [hsroot, Real.sqrt_sq_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs gamma)]
  rw [hnuSq, hprod]

private theorem auxiliary_anomalous_time_le {B gamma delta t R s p : ℝ}
    (hB : 0 < B) (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hdelta : 0 < delta) (ht : 0 < t) (hR : 0 < R) (hs : 0 < s)
    (hp : 0 < p) (hRp : R = s * p)
    (h : B * (t / (delta * R)) ^ (1 - gamma)⁻¹ < 3 * s) :
    t * (B * s ^ gamma) / s ^ (2 : ℕ) ≤
      delta * (3 * B ^ gamma) * p := by
  have h1g : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hx : 0 < t / (delta * R) := by positivity
  have hleft :
      (B * (t / (delta * R)) ^ (1 - gamma)⁻¹) ^ (1 - gamma) =
        B ^ (1 - gamma) * (t / (delta * R)) := by
    rw [Real.mul_rpow hB.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
      inv_mul_cancel₀ h1g.ne', Real.rpow_one]
  have hright : (3 * s) ^ (1 - gamma) = 3 ^ (1 - gamma) * s ^ (1 - gamma) :=
    Real.mul_rpow (by norm_num) hs.le
  have hpow := Real.rpow_le_rpow (mul_nonneg hB.le (Real.rpow_nonneg hx.le _)) h.le h1g.le
  rw [hleft, hright] at hpow
  have hthree : (3 : ℝ) ^ (1 - gamma) ≤ 3 := by
    exact Real.rpow_le_self_of_one_le (by norm_num) (by linarith only [hgamma])
  have hBpow : B ^ gamma * B ^ (1 - gamma) = B := by
    rw [← Real.rpow_add hB, add_sub_cancel, Real.rpow_one]
  have hspow : s ^ (1 - gamma) * s ^ gamma = s := by
    rw [← Real.rpow_add hs, sub_add_cancel, Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Real.rpow_nonneg hB.le gamma) (Real.rpow_nonneg hs.le gamma))
  have hcore : B * t / (delta * R) * s ^ gamma ≤ 3 * B ^ gamma * s := by
    calc
      B * t / (delta * R) * s ^ gamma =
          (B ^ gamma * B ^ (1 - gamma)) * s ^ gamma *
            (t / (delta * R)) := by rw [hBpow]; ring
      _ = (B ^ gamma * s ^ gamma) *
            (B ^ (1 - gamma) * (t / (delta * R))) := by ring
      _ ≤ (B ^ gamma * s ^ gamma) *
          (3 ^ (1 - gamma) * s ^ (1 - gamma)) := hscaled
      _ = B ^ gamma * 3 ^ (1 - gamma) *
          (s ^ (1 - gamma) * s ^ gamma) := by ring
      _ = B ^ gamma * 3 ^ (1 - gamma) * s := by rw [hspow]
      _ ≤ B ^ gamma * 3 * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hthree (Real.rpow_nonneg hB.le _)) hs.le
      _ = 3 * B ^ gamma * s := by ring
  calc
    t * (B * s ^ gamma) / s ^ (2 : ℕ) =
        delta * p / s * (B * t / (delta * R) * s ^ gamma) := by
          rw [hRp]
          field_simp
    _ ≤ delta * p / s * (3 * B ^ gamma * s) :=
      mul_le_mul_of_nonneg_left hcore (div_nonneg (mul_nonneg hdelta.le hp.le) hs.le)
    _ = delta * (3 * B ^ gamma) * p := by field_simp

/-- The upper half of the auxiliary-scale straddle controls the positive
Laplace cost at the profile time scale. -/
theorem time_div_lengthTimeScale_le_of_auxiliaryScale_lt {nu cstar gamma delta t : ℝ}
    {m n : ℤ} (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma1 : gamma < 1) (hdelta : 0 < delta) (ht : 0 < t) (hnm : n ≤ m)
    (hn : auxiliaryScaleBound nu cstar gamma delta t m < (3 : ℝ) ^ (n + 1)) :
    t / lengthTimeScale nu cstar gamma ((3 : ℝ) ^ n) ≤
      delta * earlyExitProfileCost cstar gamma * (3 : ℝ) ^ (m - n).toNat := by
  let k : ℕ := (m - n).toNat
  let R : ℝ := (3 : ℝ) ^ m
  let s : ℝ := (3 : ℝ) ^ n
  let p : ℝ := (3 : ℝ) ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hkcast : (k : ℤ) = m - n := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hnm)
  have hRp : R = s * p := by
    dsimp [R, s, p]
    rw [← zpow_natCast (3 : ℝ) k, hkcast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hupper : auxiliaryScaleBound nu cstar gamma delta t m < 3 * s := by
    simpa only [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), s, mul_comm] using hn
  rw [auxiliaryScaleBound] at hupper
  rw [← Real.sqrt_eq_rpow] at hupper
  change max (nu * t / (delta * R))
    (Real.sqrt (cstar * gamma⁻¹) * (t / (delta * R)) ^ (1 - gamma)⁻¹) <
      3 * s at hupper
  have hfirst : nu * t / (delta * R) < 3 * s := by
    exact (le_max_left _ _).trans_lt hupper
  have hsecond : Real.sqrt (cstar * gamma⁻¹) *
      (t / (delta * R)) ^ (1 - gamma)⁻¹ < 3 * s := by
    exact (le_max_right _ _).trans_lt hupper
  have hnuPart : t * nu / s ^ (2 : ℕ) ≤ delta * 3 * p := by
    calc
      t * nu / s ^ (2 : ℕ) = delta * p / s * (nu * t / (delta * R)) := by
        rw [hRp]
        field_simp
      _ ≤ delta * p / s * (3 * s) :=
        mul_le_mul_of_nonneg_left hfirst.le
          (div_nonneg (mul_nonneg hdelta.le hp.le) hs.le)
      _ = delta * 3 * p := by field_simp
  have hB : 0 < Real.sqrt (cstar * gamma⁻¹) := Real.sqrt_pos.2 (by positivity)
  have hBPart := auxiliary_anomalous_time_le hB hgamma hgamma1 hdelta ht hR hs hp hRp hsecond
  have hprofile := effectiveDiffusivity_le_add hnu hcstar hgamma hs
  change t / (s ^ (2 : ℕ) / effectiveDiffusivity nu cstar gamma s) ≤
    delta * earlyExitProfileCost cstar gamma * p
  rw [div_div_eq_mul_div]
  calc
    t * effectiveDiffusivity nu cstar gamma s / s ^ (2 : ℕ) ≤
        t * (nu + Real.sqrt (cstar * gamma⁻¹) * s ^ gamma) / s ^ (2 : ℕ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprofile ht.le) (pow_nonneg hs.le 2)
    _ = t * nu / s ^ (2 : ℕ) +
        t * (Real.sqrt (cstar * gamma⁻¹) * s ^ gamma) / s ^ (2 : ℕ) := by ring
    _ ≤ delta * 3 * p +
        delta * (3 * Real.sqrt (cstar * gamma⁻¹) ^ gamma) * p :=
          add_le_add hnuPart hBPart
    _ = delta * earlyExitProfileCost cstar gamma * p := by
      unfold earlyExitProfileCost
      ring

/-- The scale straddle and the comparison between the profile time and the
running exit-time scale put the positive Laplace term below half of the
retained chain exponent. -/
theorem laplaceCost_le_of_auxiliaryScale_lt {d : ℕ} (M : ABKModel d)
    {cstar C delta t kappa : ℝ} {m n : ℤ}
    (hcstar : 0 < cstar) (hC : 0 < C) (hdelta : 0 < delta) (ht : 0 < t)
    (hnm : n ≤ m)
    (hn : auxiliaryScaleBound M.nu cstar M.gamma delta t m < (3 : ℝ) ^ (n + 1))
    (hscale : lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) ≤
      2 * exitTimeScale M n)
    (hdeltaSmall : 128 * (3 : ℝ) ^ d * delta * earlyExitProfileCost cstar M.gamma ≤
      C * kappa) :
    (C * exitTimeScale M n)⁻¹ * t ≤
      kappa * (3 : ℝ) ^ (m - n).toNat / (64 * (3 : ℝ) ^ d) := by
  have hgamma1 : M.gamma < 1 :=
    lt_of_le_of_lt M.shellPrefix.gamma_le_quarter (by norm_num)
  have hT := time_div_lengthTimeScale_le_of_auxiliaryScale_lt M.nu_pos hcstar
    M.shellPrefix.gamma_pos hgamma1 hdelta ht hnm hn
  have hprofilePos : 0 < lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) := by
    unfold lengthTimeScale effectiveDiffusivity
    have hnuSq : 0 < M.nu ^ (2 : ℕ) := sq_pos_of_pos M.nu_pos
    have hcg : 0 ≤ cstar * M.gamma⁻¹ :=
      mul_nonneg hcstar.le (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
    have hrpow : 0 ≤ ((3 : ℝ) ^ n) ^ (2 * M.gamma) :=
      Real.rpow_nonneg (zpow_nonneg (by norm_num) n) _
    have hsecond : 0 ≤ cstar * M.gamma⁻¹ *
        ((3 : ℝ) ^ n) ^ (2 * M.gamma) := mul_nonneg hcg hrpow
    have hbase : 0 < M.nu ^ (2 : ℕ) + cstar * M.gamma⁻¹ *
        ((3 : ℝ) ^ n) ^ (2 * M.gamma) := add_pos_of_pos_of_nonneg hnuSq hsecond
    have hsqrt : 0 < Real.sqrt (M.nu ^ (2 : ℕ) + cstar * M.gamma⁻¹ *
        ((3 : ℝ) ^ n) ^ (2 * M.gamma)) := Real.sqrt_pos.2 hbase
    positivity
  have hhalf : lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) / 2 ≤
      exitTimeScale M n := by linarith only [hscale]
  have hinv : (exitTimeScale M n)⁻¹ ≤
      2 * (lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n))⁻¹ := by
    have hi := inv_anti₀ (by positivity : 0 <
      lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) / 2) hhalf
    rwa [inv_div, div_eq_mul_inv] at hi
  have hcost : (C * exitTimeScale M n)⁻¹ * t ≤
      2 / C * (t / lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n)) := by
    calc
      (C * exitTimeScale M n)⁻¹ * t = C⁻¹ * (exitTimeScale M n)⁻¹ * t := by
        rw [mul_inv_rev]
        ring
      _ ≤ C⁻¹ * (2 * (lengthTimeScale M.nu cstar M.gamma
          ((3 : ℝ) ^ n))⁻¹) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv (inv_nonneg.2 hC.le)) ht.le
      _ = 2 / C * (t / lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n)) := by
        ring
  have hscaled : (C * exitTimeScale M n)⁻¹ * t ≤
      2 / C * (delta * earlyExitProfileCost cstar M.gamma *
        (3 : ℝ) ^ (m - n).toNat) :=
    hcost.trans (mul_le_mul_of_nonneg_left hT (by positivity))
  calc
    (C * exitTimeScale M n)⁻¹ * t ≤
        2 / C * (delta * earlyExitProfileCost cstar M.gamma *
          (3 : ℝ) ^ (m - n).toNat) := hscaled
    _ ≤ kappa * (3 : ℝ) ^ (m - n).toNat / (64 * (3 : ℝ) ^ d) := by
      have hden : 0 < 64 * (3 : ℝ) ^ d := by positivity
      have hfac : 2 / C * (delta * earlyExitProfileCost cstar M.gamma) ≤
          kappa / (64 * (3 : ℝ) ^ d) := by
        calc
          2 / C * (delta * earlyExitProfileCost cstar M.gamma) =
              (2 * (delta * earlyExitProfileCost cstar M.gamma)) / C := by ring
          _ ≤ kappa / (64 * (3 : ℝ) ^ d) := by
            rw [div_le_div_iff₀ hC hden]
            have hrearrange : (2 * (delta * earlyExitProfileCost cstar M.gamma)) *
                (64 * (3 : ℝ) ^ d) =
                  128 * (3 : ℝ) ^ d * delta * earlyExitProfileCost cstar M.gamma := by ring
            rw [hrearrange, mul_comm kappa C]
            exact hdeltaSmall
      have hp : 0 ≤ (3 : ℝ) ^ (m - n).toNat := by positivity
      calc
        2 / C * (delta * earlyExitProfileCost cstar M.gamma *
            (3 : ℝ) ^ (m - n).toNat) =
            (2 / C * (delta * earlyExitProfileCost cstar M.gamma)) *
              (3 : ℝ) ^ (m - n).toNat := by ring
        _ ≤ (kappa / (64 * (3 : ℝ) ^ d)) * (3 : ℝ) ^ (m - n).toNat :=
          mul_le_mul_of_nonneg_right hfac hp
        _ = kappa * (3 : ℝ) ^ (m - n).toNat / (64 * (3 : ℝ) ^ d) := by ring

/-- **Deterministic B8 exponent lemma.**  The natural-number endpoint and
division losses are included in `earlyExitChainLength_lower`; the successor
loss in the auxiliary scale is included in
`displacementMinScale_lt_three_mul_displacementScale`.  Once the positive
Laplace cost uses at most half of the retained chain exponent, the printed
minimum remains with the explicit positive coefficient
`earlyExitDecayConstant`. -/
theorem earlyExit_exponent_le {d : ℕ} {nu cstar gamma delta t lam kappa : ℝ}
    {m n : ℤ}
    (hnu : 0 < nu) (ht : 0 < t) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hkappa : 0 < kappa) (hnm : n ≤ m)
    (hn : (3 : ℝ) ^ n ≤ auxiliaryScaleBound nu cstar gamma delta t m)
    (hlarge : earlyExitBaseScale d ≤ 3 ^ (m - n).toNat)
    (htime : lam * t ≤
      kappa * (3 : ℝ) ^ (m - n).toNat / (64 * (3 : ℝ) ^ d)) :
    0 < earlyExitDecayConstant d gamma delta kappa ∧
      lam * t - kappa * (earlyExitChainLength d (m - n).toNat : ℝ) ≤
        -earlyExitDecayConstant d gamma delta kappa *
          displacementMinScale nu cstar gamma t m := by
  let k : ℕ := (m - n).toNat
  have hq : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have h1g : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hdp : 0 < delta ^ (1 - gamma)⁻¹ := Real.rpow_pos_of_pos hdelta _
  have hcpos : 0 < earlyExitDecayConstant d gamma delta kappa := by
    unfold earlyExitDecayConstant
    positivity
  refine ⟨hcpos, ?_⟩
  have hchain := earlyExitChainLength_lower d k hlarge
  have hkchain : kappa * (3 : ℝ) ^ k / (32 * (3 : ℝ) ^ d) ≤
      kappa * (earlyExitChainLength d k : ℝ) := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hchain hkappa.le
  have hmin := displacementMinScale_lt_three_mul_displacementScale hnu ht hdelta
    hdelta1 hcstar hgamma hgamma1 hnm hn
  change displacementMinScale nu cstar gamma t m <
    3 * displacementScale delta gamma k at hmin
  change lam * t ≤ kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) at htime
  have hcancel : delta ^ (1 - gamma)⁻¹ * delta ^ (-(1 - gamma)⁻¹) = 1 := by
    rw [← Real.rpow_add hdelta, add_neg_cancel, Real.rpow_zero]
  have hcmin : earlyExitDecayConstant d gamma delta kappa *
      displacementMinScale nu cstar gamma t m <
        kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) := by
    refine (mul_lt_mul_of_pos_left hmin hcpos).trans_eq ?_
    unfold earlyExitDecayConstant displacementScale
    calc
      kappa * delta ^ (1 - gamma)⁻¹ / (192 * (3 : ℝ) ^ d) *
          (3 * (delta ^ (-(1 - gamma)⁻¹) * (3 : ℝ) ^ k)) =
          kappa / (64 * (3 : ℝ) ^ d) *
            (delta ^ (1 - gamma)⁻¹ * delta ^ (-(1 - gamma)⁻¹)) * (3 : ℝ) ^ k := by
              ring
      _ = kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) := by rw [hcancel]; ring
  have hretained : lam * t +
      kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) ≤
        kappa * (earlyExitChainLength d k : ℝ) := by
    have hdouble : kappa * (3 : ℝ) ^ k / (32 * (3 : ℝ) ^ d) =
        kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) +
          kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) := by ring
    calc
      lam * t + kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) ≤
          kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) +
            kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d) :=
              by simpa only [add_comm] using
                add_le_add_right htime (kappa * (3 : ℝ) ^ k / (64 * (3 : ℝ) ^ d))
      _ = kappa * (3 : ℝ) ^ k / (32 * (3 : ℝ) ^ d) := hdouble.symm
      _ ≤ kappa * (earlyExitChainLength d k : ℝ) := hkchain
  change lam * t - kappa * (earlyExitChainLength d k : ℝ) ≤
    -earlyExitDecayConstant d gamma delta kappa *
      displacementMinScale nu cstar gamma t m
  linarith only [hcmin.le, hretained]

/-- The positive exponent extracted from the strict one-step Laplace
contraction. -/
def earlyExitKappa (Cup clow : ℝ≥0) : ℝ :=
  1 - (oneStepLaplaceContraction Cup clow).toReal

/-- The exponent extracted from the one-step contraction is strictly positive. -/
theorem earlyExitKappa_pos {Cup clow : ℝ≥0} (hCup : 0 < Cup) (hclow : 0 < clow) :
    0 < earlyExitKappa Cup clow := by
  have hlt := oneStepLaplaceContraction_lt_one hCup hclow
  have hreal : (oneStepLaplaceContraction Cup clow).toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (oneStepLaplaceContraction_ne_top Cup clow)
        ENNReal.one_ne_top).2 hlt
  unfold earlyExitKappa
  linarith only [hreal]

/-- The strict one-step contraction is bounded by the real exponential of its
extracted positive exponent. -/
theorem oneStepLaplaceContraction_le_exp_neg_earlyExitKappa (Cup clow : ℝ≥0) :
    oneStepLaplaceContraction Cup clow ≤
      ENNReal.ofReal (Real.exp (-earlyExitKappa Cup clow)) := by
  let rho := oneStepLaplaceContraction Cup clow
  have hrho : rho = ENNReal.ofReal rho.toReal :=
    (ENNReal.ofReal_toReal (oneStepLaplaceContraction_ne_top Cup clow)).symm
  have hreal : rho.toReal ≤ Real.exp (-earlyExitKappa Cup clow) := by
    calc
      rho.toReal = 1 + (rho.toReal - 1) := by ring
      _ ≤ Real.exp (rho.toReal - 1) := by
        simpa only [add_comm] using Real.add_one_le_exp (rho.toReal - 1)
      _ = Real.exp (-earlyExitKappa Cup clow) := by
        unfold earlyExitKappa rho
        congr 1
        ring
  change rho ≤ ENNReal.ofReal (Real.exp (-earlyExitKappa Cup clow))
  rw [hrho]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Deterministic B8 scale optimization.**  If `n` straddles the auxiliary
scale, the profile time is comparable to the running exit-time scale, the
accuracy is below the displayed explicit threshold, and the residual triadic
gap is above `earlyExitBaseScale`, then the Chernoff exponent is a negative
multiple of the exact minimum printed in the paper. -/
theorem earlyExit_exponent_le_of_auxiliaryScale_straddle {d : ℕ} (M : ABKModel d)
    {C delta t kappa : ℝ} {m n : ℤ}
    (hC : 0 < C) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (ht : 0 < t)
    (hkappa : 0 < kappa) (hnm : n ≤ m)
    (hnLower : (3 : ℝ) ^ n ≤ auxiliaryScaleBound M.nu (Disorder.cstar M)
      M.gamma delta t m)
    (hnUpper : auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta t m <
      (3 : ℝ) ^ (n + 1))
    (hscale : lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
      2 * exitTimeScale M n)
    (hdeltaSmall : 128 * (3 : ℝ) ^ d * delta *
        earlyExitProfileCost (Disorder.cstar M) M.gamma ≤ C * kappa)
    (hlarge : earlyExitBaseScale d ≤ 3 ^ (m - n).toNat) :
    0 < earlyExitDecayConstant d M.gamma delta kappa ∧
      (C * exitTimeScale M n)⁻¹ * t -
          kappa * (earlyExitChainLength d (m - n).toNat : ℝ) ≤
        -earlyExitDecayConstant d M.gamma delta kappa *
          displacementMinScale M.nu (Disorder.cstar M) M.gamma t m := by
  apply earlyExit_exponent_le M.nu_pos ht hdelta hdelta1
    (Provider.Orlicz.cstar_pos M) M.shellPrefix.gamma_pos
    (lt_of_le_of_lt M.shellPrefix.gamma_le_quarter (by norm_num)) hkappa hnm hnLower hlarge
  exact laplaceCost_le_of_auxiliaryScale_lt M (Provider.Orlicz.cstar_pos M) hC hdelta ht hnm
    hnUpper hscale hdeltaSmall

end

end Algsuperdiff.Section5.Provider
