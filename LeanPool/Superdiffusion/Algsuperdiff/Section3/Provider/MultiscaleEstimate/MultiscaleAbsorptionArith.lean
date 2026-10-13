/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorptionCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.DeepLegSummability

/-!
# MultiscaleAbsorptionArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the scalar absorption arithmetic of `p.multiscale.estimate`

## Why this file exists

It is a statement-preserving motion and nothing else: sections 4, 5 and 6 of that module -- the
three scale bridges of the non-lane terms, the bad lane's two amplitudes, and
the deterministic remainder -- were moved here with their section headers,
their docstrings, their statements and their proof text unchanged.  The
original section numbers 4, 5, 6 are kept precisely so that every
cross-reference in either module's header still points where it did.

Exactly two mechanical changes were forced by the motion, at no mathematical
cost:

1. each moved declaration is `protected theorem` here where it was
   `private theorem` there (12 declarations); and
2. the ten call sites *inside* this file that consume a sibling of this file
   carry the `MultiscaleAbsorptionArith.` qualifier, because a `protected`
   name is not in scope under its own short form.

No statement was altered, no lemma was dropped, no lemma was added, and no
proof was re-golfed.

## What is here

Twelve real-scalar inequalities, all model-free: they mention no `ABKModel`, no
measure and no random variable, only real parameters
(`eps`, `Cms`, `E`, `cgamma`, `s`, `cstar^{-1}`, and the amplitude constants).

* **Section 4** -- `polyTerm_le_ordinaryScale`, `expTerm_le_ordinaryScale`,
  `expTerm_le_rareScale`: the three scale bridges carrying a display term into
  the ordinary scale `s^{-2} eps^2 E^2 cgamma` or the rare scale
  `s^{-4} eps^2 exp(-2 E^{-3} cgamma^{-1})`, on top of the Core module's
  `absorb_window_poly`, `absorb_window_exp` and `absorb_window_exp_rare`.
* **Section 5** -- `badProfile_le`, `badRemainder_le`, `badOrdinarySum_le`,
  `badOrdinaryAmplitude_le`, `badRareAmplitude_le`: the bad lane's `Gamma_1`
  and `Gamma_{2/7}` amplitudes, absorbed.
* **Section 6** -- `remainderGap_le`, `remainderScale_le`, `remainderLog_le`,
  `remainderTerm_le`: the three summands of the deterministic remainder and
  their sum, absorbed into the ordinary normal form.

Four of the twelve are consumed by the parent module (inside the proof of
`exists_absorbed_envelope`): `polyTerm_le_ordinaryScale`,
`badOrdinaryAmplitude_le`, `badRareAmplitude_le` and `remainderTerm_le`.  The
other eight are consumed only here.

## Scope

`protected` implementation support for one sibling module, NOT source-facing.
Every declaration is a proved local helper over real scalars.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorptionArith

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Localization

noncomputable section

/-! ## 4. The three scale bridges of the non-lane terms -/

/-- A polynomial term of the display, in the ordinary normal form. -/
protected theorem polyTerm_le_ordinaryScale {cstarInv eps Cms E gam s Q p K : ℝ}
    (hQ : 0 ≤ Q) (hcs : 0 ≤ cstarInv) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hCms : 2 + p ≤ Cms) (hQE : Q ≤ K * E)
    (hwin : cstarInv * eps ^ (-Cms) ≤ E) (hgam : 0 ≤ gam) (hs : 0 < s) :
    Q * cstarInv * eps ^ (-p) * gam * (s⁻¹) ^ 2 ≤
      K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have habs := absorb_window_poly hQ hcs heps0 heps1 hCms hQE hwin
  have hpos : (0 : ℝ) ≤ gam * (s⁻¹) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right habs hpos
  calc Q * cstarInv * eps ^ (-p) * gam * (s⁻¹) ^ 2
      = Q * cstarInv * eps ^ (-p) * (gam * (s⁻¹) ^ 2) := by ring
    _ ≤ K * (eps ^ 2 * E ^ 2) * (gam * (s⁻¹) ^ 2) := h1
    _ = K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by ring

/-- An exponentially small term of the display, in the ordinary normal form. -/
protected theorem expTerm_le_ordinaryScale {eps Cms E gam s a Q K : ℝ}
    (hQ : 0 ≤ Q) (ha : 0 < a) (hE : 0 < E) (hgam : 0 < gam) (heps0 : 0 < eps)
    (heps1 : eps ≤ 1) (hgammaE : gam ≤ (E⁻¹) ^ 10) (hCms : (2 : ℝ) ≤ 8 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E)
    (hK : 2 * Q * (a⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 8 ≤ K) (hs : 0 < s) :
    Q * Real.exp (-(a * (E⁻¹) ^ 2 * gam⁻¹)) * (s⁻¹) ^ 2 ≤
      K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have habs := absorb_window_exp hQ ha hE hgam heps0 heps1 hgammaE hCms hfloor hK
  have hpos : (0 : ℝ) ≤ (s⁻¹) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right habs hpos
  calc Q * Real.exp (-(a * (E⁻¹) ^ 2 * gam⁻¹)) * (s⁻¹) ^ 2
      ≤ K * (eps ^ 2 * E ^ 2 * gam) * (s⁻¹) ^ 2 := h1
    _ = K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by ring

/-- An exponentially small term of the display, in the rare normal form. -/
protected theorem expTerm_le_rareScale {eps Cms E gam s a Q K X : ℝ}
    (hQ : 0 ≤ Q) (ha : 0 < a) (hE : 0 < E) (hgam : 0 < gam) (heps0 : 0 < eps)
    (heps1 : eps ≤ 1) (hgammaE : gam ≤ (E⁻¹) ^ 10) (hEa : 4 / a ≤ E)
    (hCms : (2 : ℝ) ≤ 16 * Cms) (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E)
    (hK : 8 * Q * (a⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 16 ≤ K) (hs : 0 < s) (hs1 : s ≤ 1)
    (hX : X = 2 * (E⁻¹) ^ 3 * gam⁻¹) (hK0 : 0 ≤ K) :
    Q * Real.exp (-(a * (E⁻¹) ^ 2 * gam⁻¹)) ≤
      K * ((s⁻¹) ^ 4 * (eps ^ 2 * Real.exp (-X))) := by
  subst hX
  have habs := absorb_window_exp_rare hQ ha hE hgam heps0 heps1 hgammaE hEa hCms
    hfloor hK
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have hpow : (1 : ℝ) ≤ (s⁻¹) ^ 4 := one_le_pow₀ hsinv1
  have hbase : (0 : ℝ) ≤ eps ^ 2 * Real.exp (-(2 * (E⁻¹) ^ 3 * gam⁻¹)) := by positivity
  have hstep : eps ^ 2 * Real.exp (-(2 * (E⁻¹) ^ 3 * gam⁻¹)) ≤
      (s⁻¹) ^ 4 * (eps ^ 2 * Real.exp (-(2 * (E⁻¹) ^ 3 * gam⁻¹))) := by
    nlinarith [hpow, hbase]
  exact habs.trans (mul_le_mul_of_nonneg_left hstep hK0)

/-! ## 5. The bad lane's two amplitudes -/

/-- The printed lower-ellipticity profile is `2/3 . Ccg` on the window
`8 cgamma <= s`, so the crude bound's deterministic shift is `<= 24 Ccg`. -/
protected theorem badProfile_le {Ccg0 gam s : ℝ} (hCcg0 : 0 < Ccg0) (hgam0 : 0 < gam)
    (hgam1 : gam ≤ 1) (hs8 : 8 * gam ≤ s) :
    0 ≤ 8 * Ccg0 + 8 * (3 : ℝ) ^ gam *
        lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo ∧
      8 * Ccg0 + 8 * (3 : ℝ) ^ gam *
        lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo ≤
        24 * Ccg0 := by
  have hs : (0 : ℝ) < s := by linarith
  have hden : (0 : ℝ) < 2 * (s / 4) - gam := by linarith
  have hprof : lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo =
      Ccg0 * (s / 4) * (2 * (s / 4) - gam)⁻¹ :=
    Provider.Tail.lowerEllipticityProfile_exponentTwo Ccg0 gam (s / 4)
  have hinvle : (2 * (s / 4) - gam)⁻¹ ≤ 8 / (3 * s) := by
    have hpos : (0 : ℝ) < 8 / (3 * s) := by positivity
    rw [inv_le_comm₀ hden hpos]
    have hrw : (8 / (3 * s))⁻¹ = 3 * s / 8 := by field_simp
    rw [hrw]
    linarith
  have hprof0 : (0 : ℝ) ≤ lowerEllipticityProfile Ccg0 gam (s / 4)
      Provider.Tail.exponentTwo := by
    rw [hprof]; positivity
  have hprofle : lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo ≤
      2 / 3 * Ccg0 := by
    rw [hprof]
    have h1 : Ccg0 * (s / 4) * (2 * (s / 4) - gam)⁻¹ ≤ Ccg0 * (s / 4) * (8 / (3 * s)) :=
      mul_le_mul_of_nonneg_left hinvle (by positivity)
    have h2 : Ccg0 * (s / 4) * (8 / (3 * s)) = 2 / 3 * Ccg0 := by field_simp; ring
    linarith [h1, h2.le, h2.ge]
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ gam := Real.rpow_pos_of_pos (by norm_num) _
  have hthree : (3 : ℝ) ^ gam ≤ 3 := by
    calc (3 : ℝ) ^ gam ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hgam1
      _ = 3 := Real.rpow_one 3
  refine ⟨by positivity, ?_⟩
  have hmul : 8 * (3 : ℝ) ^ gam *
      lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo ≤
      8 * 3 * (2 / 3 * Ccg0) := by
    have hA : 8 * (3 : ℝ) ^ gam ≤ 8 * 3 := by linarith
    have hA0 : (0 : ℝ) ≤ 8 * (3 : ℝ) ^ gam := by positivity
    calc 8 * (3 : ℝ) ^ gam *
          lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo
        ≤ 8 * (3 : ℝ) ^ gam * (2 / 3 * Ccg0) := mul_le_mul_of_nonneg_left hprofle hA0
      _ ≤ 8 * 3 * (2 / 3 * Ccg0) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
  linarith [hmul]

/-- The remainder summand of the crude bound's ordinary amplitude, at the
window's own cube bound `(8/(3s))^3`. -/
protected theorem badRemainder_le {Ccg0 cstarInv gam s : ℝ} (hCcg0 : 0 < Ccg0)
    (hcs : 0 ≤ cstarInv) (hgam0 : 0 < gam) (hs8 : 8 * gam ≤ s) :
    8 * (Ccg0 * cstarInv * (s / 4) * gam * (2 * (s / 4) - gam)⁻¹ ^ 3) ≤
      38 * Ccg0 * cstarInv * gam * (s⁻¹) ^ 2 := by
  have hs : (0 : ℝ) < s := by linarith
  have hden : (0 : ℝ) < 2 * (s / 4) - gam := by linarith
  have hinvle : (2 * (s / 4) - gam)⁻¹ ≤ 8 / (3 * s) := by
    have hpos : (0 : ℝ) < 8 / (3 * s) := by positivity
    rw [inv_le_comm₀ hden hpos]
    have hrw : (8 / (3 * s))⁻¹ = 3 * s / 8 := by field_simp
    rw [hrw]
    linarith
  have hcube : (2 * (s / 4) - gam)⁻¹ ^ 3 ≤ (8 / (3 * s)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hinvle 3
  have hbase : (0 : ℝ) ≤ 8 * (Ccg0 * cstarInv * (s / 4) * gam) := by positivity
  have hb : (0 : ℝ) ≤ Ccg0 * cstarInv * gam * (s⁻¹) ^ 2 := by positivity
  have h2 : 8 * (Ccg0 * cstarInv * (s / 4) * gam) * (8 / (3 * s)) ^ 3 =
      (1024 / 27 : ℝ) * (Ccg0 * cstarInv * gam * (s⁻¹) ^ 2) := by
    field_simp
    ring
  calc 8 * (Ccg0 * cstarInv * (s / 4) * gam * (2 * (s / 4) - gam)⁻¹ ^ 3)
      = 8 * (Ccg0 * cstarInv * (s / 4) * gam) * (2 * (s / 4) - gam)⁻¹ ^ 3 := by ring
    _ ≤ 8 * (Ccg0 * cstarInv * (s / 4) * gam) * (8 / (3 * s)) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube hbase
    _ = (1024 / 27 : ℝ) * (Ccg0 * cstarInv * gam * (s⁻¹) ^ 2) := h2
    _ ≤ 38 * (Ccg0 * cstarInv * gam * (s⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hb
    _ = 38 * Ccg0 * cstarInv * gam * (s⁻¹) ^ 2 := by ring

/-- The crude bound's ordinary amplitude, reduced to its three absorbable
summands.  Only the `[0,1]` profile bound, the remainder's cube bound and the
merge constant `1 + log 2 <= 2` are used. -/
protected theorem badOrdinarySum_le {cstarInv gam s Ccg0 cc T dR E Q4a Q4b Q4c : ℝ}
    (hCcg0 : 0 < Ccg0) (hcc : 0 < cc) (hcs : 0 ≤ cstarInv) (hdR : 0 ≤ dR)
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hs8 : 8 * gam ≤ s) (hT0 : 0 ≤ T)
    (hQ4a : Q4a = 122880 * Ccg0 * gammaTriangleConst 1 * dR * cc⁻¹)
    (hQ4b : Q4b = 122880 * Ccg0 * gammaTriangleConst 1 * dR)
    (hQ4c : Q4c = 608 * Ccg0) :
    8 * ((1 + Real.log 2) ^ (1 : ℝ)⁻¹ *
        ((8 * Ccg0 + 8 * (3 : ℝ) ^ gam *
            lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo) *
            (gammaTriangleConst 1 *
              (20 * s⁻¹ * (16 * dR * s⁻¹ *
                (cc⁻¹ * cstarInv * T * gam +
                  Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹)))))) +
          8 * (Ccg0 * cstarInv * (s / 4) * gam * (2 * (s / 4) - gam)⁻¹ ^ 3))) ≤
      Q4a * cstarInv * T * gam * (s⁻¹) ^ 2 +
        Q4b * Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹)) * (s⁻¹) ^ 2 +
        Q4c * cstarInv * gam * (s⁻¹) ^ 2 := by
  have hs : (0 : ℝ) < s := by linarith
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
  have hg1 : (0 : ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
  have hden : (0 : ℝ) < 2 * (s / 4) - gam := by linarith
  obtain ⟨hPfac0, hPfac⟩ := MultiscaleAbsorptionArith.badProfile_le hCcg0 hgam0 hgam1 hs8
  have hRemle := MultiscaleAbsorptionArith.badRemainder_le (cstarInv := cstarInv) hCcg0 hcs hgam0 hs8
  have hMid0 : (0 : ℝ) ≤ gammaTriangleConst 1 *
      (20 * s⁻¹ * (16 * dR * s⁻¹ * (cc⁻¹ * cstarInv * T * gam +
        Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹))))) := by positivity
  have hRem0 : (0 : ℝ) ≤ 8 * (Ccg0 * cstarInv * (s / 4) * gam *
      (2 * (s / 4) - gam)⁻¹ ^ 3) := by positivity
  set Out : ℝ := (1 + Real.log 2) ^ (1 : ℝ)⁻¹ with hOdef
  set Pfac : ℝ := 8 * Ccg0 + 8 * (3 : ℝ) ^ gam *
    lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo with hPdef
  set Mid : ℝ := gammaTriangleConst 1 *
    (20 * s⁻¹ * (16 * dR * s⁻¹ * (cc⁻¹ * cstarInv * T * gam +
      Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹))))) with hMdef
  set Rem : ℝ := 8 * (Ccg0 * cstarInv * (s / 4) * gam *
    (2 * (s / 4) - gam)⁻¹ ^ 3) with hRdef
  have houter : Out ≤ 2 := by
    rw [hOdef, inv_one, Real.rpow_one]
    have := Real.log_two_lt_d9
    linarith
  have hnn : (0 : ℝ) ≤ Pfac * Mid + Rem :=
    add_nonneg (mul_nonneg hPfac0 hMid0) hRem0
  have h16 : 8 * (Out * (Pfac * Mid + Rem)) ≤ 16 * (Pfac * Mid + Rem) := by
    nlinarith [mul_nonneg (sub_nonneg.2 houter) hnn]
  have hPM : Pfac * Mid ≤ 24 * Ccg0 * Mid := mul_le_mul_of_nonneg_right hPfac hMid0
  have hinner : 16 * (24 * Ccg0 * Mid) =
      Q4a * cstarInv * T * gam * (s⁻¹) ^ 2 +
        Q4b * Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹)) * (s⁻¹) ^ 2 := by
    rw [hQ4a, hQ4b, hMdef]; ring
  have hrem16 : 16 * (38 * Ccg0 * cstarInv * gam * (s⁻¹) ^ 2) =
      Q4c * cstarInv * gam * (s⁻¹) ^ 2 := by rw [hQ4c]; ring
  linarith [h16, hPM, hRemle, hinner.le, hinner.ge, hrem16.le, hrem16.ge]

/-- **The bad lane's `Gamma_1` amplitude, absorbed** into the ordinary normal
form: the `3^{5h} cgamma` head (polynomial in `eps^{-1}`, absorbed by the window
at `2 + p <= Cms`), the exponentially small tail (absorbed by `x^2 e^{-x} <= 2`),
and the profile remainder. -/
protected theorem badOrdinaryAmplitude_le {cstarInv eps Cms E gam s Ccg0 cc T p dR K
    Q4a Q4b Q4c : ℝ}
    (hCcg0 : 0 < Ccg0) (hcc : 0 < cc) (hcs : 0 ≤ cstarInv) (hdR : 0 ≤ dR)
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hs8 : 8 * gam ≤ s)
    (hT0 : 0 ≤ T) (hT : T ≤ eps ^ (-p)) (hp0 : 0 ≤ p)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hE : 0 < E)
    (hgammaE : gam ≤ (E⁻¹) ^ 10)
    (hwin : cstarInv * eps ^ (-Cms) ≤ E)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E)
    (hQ4a : Q4a = 122880 * Ccg0 * gammaTriangleConst 1 * dR * cc⁻¹)
    (hQ4b : Q4b = 122880 * Ccg0 * gammaTriangleConst 1 * dR)
    (hQ4c : Q4c = 608 * Ccg0)
    (hCmsp : 2 + p ≤ Cms) (hQ4aE : Q4a ≤ E) (hQ4cE : Q4c ≤ E)
    (hK : 2 * Q4b * (cc⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 8 + 2 ≤ K) :
    8 * ((1 + Real.log 2) ^ (1 : ℝ)⁻¹ *
        ((8 * Ccg0 + 8 * (3 : ℝ) ^ gam *
            lowerEllipticityProfile Ccg0 gam (s / 4) Provider.Tail.exponentTwo) *
            (gammaTriangleConst 1 *
              (20 * s⁻¹ * (16 * dR * s⁻¹ *
                (cc⁻¹ * cstarInv * T * gam +
                  Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹)))))) +
          8 * (Ccg0 * cstarInv * (s / 4) * gam * (2 * (s / 4) - gam)⁻¹ ^ 3))) ≤
      K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have hs : (0 : ℝ) < s := by linarith
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
  have hg1 : (0 : ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
  have hCms8 : (2 : ℝ) ≤ 8 * Cms := by linarith
  have hQ4a0 : (0 : ℝ) ≤ Q4a := by rw [hQ4a]; positivity
  have hQ4b0 : (0 : ℝ) ≤ Q4b := by rw [hQ4b]; positivity
  have hQ4c0 : (0 : ℝ) ≤ Q4c := by rw [hQ4c]; positivity
  have hsum := MultiscaleAbsorptionArith.badOrdinarySum_le (E := E) hCcg0 hcc hcs hdR hgam0 hgam1 hs8 hT0
    hQ4a hQ4b hQ4c
  set S : ℝ := (s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam) with hSdef
  set K4b : ℝ := 2 * Q4b * (cc⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 8 with hK4bdef
  have hbase : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have hp1 : Q4a * cstarInv * T * gam * (s⁻¹) ^ 2 ≤ 1 * S := by
    have hcoef : (0 : ℝ) ≤ Q4a * cstarInv := mul_nonneg hQ4a0 hcs
    have hrest : (0 : ℝ) ≤ gam * (s⁻¹) ^ 2 := by positivity
    have hmono : Q4a * cstarInv * T * gam * (s⁻¹) ^ 2 ≤
        Q4a * cstarInv * eps ^ (-p) * gam * (s⁻¹) ^ 2 := by
      calc Q4a * cstarInv * T * gam * (s⁻¹) ^ 2
          = (Q4a * cstarInv) * T * (gam * (s⁻¹) ^ 2) := by ring
        _ ≤ (Q4a * cstarInv) * eps ^ (-p) * (gam * (s⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hcoef) hrest
        _ = Q4a * cstarInv * eps ^ (-p) * gam * (s⁻¹) ^ 2 := by ring
    rw [hSdef]
    exact hmono.trans (MultiscaleAbsorptionArith.polyTerm_le_ordinaryScale hQ4a0 hcs heps0 heps1 hCmsp
      (by linarith : Q4a ≤ 1 * E) hwin hgam0.le hs)
  have hp2 : Q4b * Real.exp (-(cc * (E⁻¹) ^ 2 * gam⁻¹)) * (s⁻¹) ^ 2 ≤ K4b * S := by
    rw [hSdef, hK4bdef]
    exact MultiscaleAbsorptionArith.expTerm_le_ordinaryScale hQ4b0 hcc hE hgam0 heps0 heps1 hgammaE hCms8 hfloor
      le_rfl hs
  have hp3 : Q4c * cstarInv * gam * (s⁻¹) ^ 2 ≤ 1 * S := by
    have hz : eps ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    have hh := MultiscaleAbsorptionArith.polyTerm_le_ordinaryScale (p := (0 : ℝ)) (K := (1 : ℝ)) hQ4c0 hcs heps0
      heps1 (by linarith : (2 : ℝ) + 0 ≤ Cms) (by linarith : Q4c ≤ 1 * E) hwin
      hgam0.le hs
    rw [hz] at hh
    rw [hSdef]
    calc Q4c * cstarInv * gam * (s⁻¹) ^ 2
        = Q4c * cstarInv * 1 * gam * (s⁻¹) ^ 2 := by ring
      _ ≤ 1 * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := hh
  have hcollect : 1 * S + K4b * S + 1 * S = (K4b + 2) * S := by ring
  have hlast : (K4b + 2) * S ≤ K * S :=
    mul_le_mul_of_nonneg_right (by rw [hK4bdef]; linarith [hK]) hbase
  linarith [hsum, hp1, hp2, hp3, hcollect.le, hcollect.ge, hlast]

/-- **The bad lane's `Gamma_{2/7}` amplitude, absorbed** into the rare normal
form.  The printed rate `exp(-(Ccg^{-1} E^{-2} cgamma^{-1}))` clears the frozen
root's own `exp(-(2 E^{-3} cgamma^{-1}))` on the window `8 Ccg <= E`. -/
protected theorem badRareAmplitude_le {eps Cms E gam s Ccg0 K : ℝ}
    (hCcg0 : 0 < Ccg0) (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hE : 0 < E) (hgammaE : gam ≤ (E⁻¹) ^ 10)
    (hEa : 8 * Ccg0 ≤ E) (hCms : (2 : ℝ) ≤ 16 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E)
    (hK : 8 * 4096 * Ccg0 ^ 2 * (3 / 2 : ℝ) ^ 16 ≤ K) (hK0 : 0 ≤ K) :
    8 * ((1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ *
        (8 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) +
          8 * (3 : ℝ) ^ gam * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)))) ≤
      K * ((s⁻¹) ^ 4 * (eps ^ 2 * Real.exp (-(2 * (E⁻¹) ^ 3 * gam⁻¹)))) := by
  have hexp0 : (0 : ℝ) < Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) := Real.exp_pos _
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ gam := Real.rpow_pos_of_pos (by norm_num) _
  have hthree : (3 : ℝ) ^ gam ≤ 3 := by
    calc (3 : ℝ) ^ gam ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hgam1
      _ = 3 := Real.rpow_one 3
  have hlog2 : (1 : ℝ) + Real.log 2 ≤ 2 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog0 : (0 : ℝ) ≤ 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have houter : (1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ ≤ 16 := by
    calc (1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ ≤ (2 : ℝ) ^ ((2 : ℝ) / 7)⁻¹ :=
          Real.rpow_le_rpow hlog0 hlog2 (by norm_num)
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 16 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have houter0 : (0 : ℝ) ≤ (1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ :=
    Real.rpow_nonneg hlog0 _
  have hinner : 8 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) +
      8 * (3 : ℝ) ^ gam * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) ≤
      32 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) := by
    nlinarith [hthree, hexp0]
  have hinner0 : (0 : ℝ) ≤ 8 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) +
      8 * (3 : ℝ) ^ gam * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) := by positivity
  have hstep : 8 * ((1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ *
      (8 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) +
        8 * (3 : ℝ) ^ gam * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)))) ≤
      4096 * Real.exp (-(Ccg0⁻¹ * (E⁻¹) ^ 2 * gam⁻¹)) := by
    nlinarith [houter, houter0, hinner, hinner0, hexp0]
  have hane : (0 : ℝ) < Ccg0⁻¹ := inv_pos.2 hCcg0
  have hdiv : (4 : ℝ) / Ccg0⁻¹ = 4 * Ccg0 := by field_simp
  have hKrw : 8 * 4096 * ((Ccg0⁻¹)⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 16 ≤ K := by
    rwa [inv_inv]
  have habs := MultiscaleAbsorptionArith.expTerm_le_rareScale (Q := 4096) (a := Ccg0⁻¹) (K := K)
    (X := 2 * (E⁻¹) ^ 3 * gam⁻¹) (by norm_num) hane hE hgam0 heps0 heps1 hgammaE
    (by rw [hdiv]; linarith) hCms hfloor hKrw hs hs1 rfl hK0
  linarith [hstep, habs]

/-! ## 6. The deterministic remainder -/

/-- The `cgamma^2 h^2` summand of the deterministic remainder. -/
protected theorem remainderGap_le {eps Cms E gam s hgapR Q5 : ℝ} (hQ5 : 0 ≤ Q5)
    (hgam0 : 0 < gam) (hs : 0 < s) (hs1 : s ≤ 1) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hE1 : 1 ≤ E) (hgammaE : gam ≤ (E⁻¹) ^ 10) (hhgap0 : 0 ≤ hgapR)
    (hhgap : hgapR ≤ 2 * E) (hCms10 : (2 : ℝ) ≤ 10 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E) :
    Q5 * gam ^ 2 * hgapR ^ 2 ≤
      (4 * Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have hE : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have hsq : (1 : ℝ) ≤ (s⁻¹) ^ 2 := one_le_pow₀ hsinv1
  have hgeps := gamma_le_epsSq heps0 heps1 hE hfloor hCms10 hgammaE
  have hbase0 : (0 : ℝ) ≤ eps ^ 2 * E ^ 2 * gam := by positivity
  have hSge : eps ^ 2 * E ^ 2 * gam ≤ (s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam) := by
    nlinarith [hsq, hbase0]
  have hg2 : gam ^ 2 ≤ (3 / 2 : ℝ) ^ 10 * eps ^ 2 * gam := by
    nlinarith [hgeps, hgam0.le]
  have hh2 : hgapR ^ 2 ≤ 4 * E ^ 2 := by nlinarith [hhgap, hhgap0]
  calc Q5 * gam ^ 2 * hgapR ^ 2 ≤ Q5 * gam ^ 2 * (4 * E ^ 2) :=
        mul_le_mul_of_nonneg_left hh2 (by positivity)
    _ = (4 * E ^ 2 * Q5) * gam ^ 2 := by ring
    _ ≤ (4 * E ^ 2 * Q5) * ((3 / 2 : ℝ) ^ 10 * eps ^ 2 * gam) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
    _ = (4 * Q5 * (3 / 2 : ℝ) ^ 10) * (eps ^ 2 * E ^ 2 * gam) := by ring
    _ ≤ (4 * Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) :=
        mul_le_mul_of_nonneg_left hSge (by positivity)

/-- The `cgamma^2 s^{-2}` summand of the deterministic remainder. -/
protected theorem remainderScale_le {eps Cms E gam s Q5 : ℝ} (hQ5 : 0 ≤ Q5)
    (hgam0 : 0 < gam) (hs : 0 < s) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hE1 : 1 ≤ E) (hgammaE : gam ≤ (E⁻¹) ^ 10) (hCms10 : (2 : ℝ) ≤ 10 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E) :
    Q5 * gam ^ 2 * (s ^ 2)⁻¹ ≤
      (Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have hE : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hgeps := gamma_le_epsSq heps0 heps1 hE hfloor hCms10 hgammaE
  have hg2 : gam ^ 2 ≤ (3 / 2 : ℝ) ^ 10 * eps ^ 2 * gam := by
    nlinarith [hgeps, hgam0.le]
  have hEsq : (1 : ℝ) ≤ E ^ 2 := one_le_pow₀ hE1
  have hinv : (s ^ 2)⁻¹ = (s⁻¹) ^ 2 := by rw [inv_pow]
  have hmid : eps ^ 2 * gam ≤ eps ^ 2 * E ^ 2 * gam := by nlinarith [hEsq, hgam0.le]
  calc Q5 * gam ^ 2 * (s ^ 2)⁻¹ = (Q5 * (s⁻¹) ^ 2) * gam ^ 2 := by rw [hinv]; ring
    _ ≤ (Q5 * (s⁻¹) ^ 2) * ((3 / 2 : ℝ) ^ 10 * eps ^ 2 * gam) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
    _ = (Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * gam)) := by ring
    _ ≤ (Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hmid (by positivity)

/-- The `cgamma^2 E^4 |log cgamma|^4` summand of the deterministic remainder. -/
protected theorem remainderLog_le {eps Cms E gam s Q5 : ℝ} (hQ5 : 0 ≤ Q5)
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hE1 : 1 ≤ E)
    (hgammaE : gam ≤ (E⁻¹) ^ 10) (hCms3 : (2 : ℝ) ≤ 3 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E) :
    Q5 * gam ^ 2 * (E ^ 4 * |Real.log gam| ^ 4) ≤
      (384 * Q5 * (3 / 2 : ℝ) ^ 3) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have hE : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have hsq : (1 : ℝ) ≤ (s⁻¹) ^ 2 := one_le_pow₀ hsinv1
  have hroot : Real.sqrt gam * Real.sqrt gam = gam := Real.mul_self_sqrt hgam0.le
  have hlogb := sqrt_mul_abs_log_pow_four_le hgam0 hgam1
  have hsqrt := sqrt_gamma_mul_sq_le heps0 heps1 hE hfloor hCms3 hgammaE
  have hroot0 : (0 : ℝ) ≤ Real.sqrt gam := Real.sqrt_nonneg gam
  -- `gam^2 |log gam|^4 <= 384 gam sqrt gam`
  have hstep1 : gam ^ 2 * |Real.log gam| ^ 4 ≤ 384 * (gam * Real.sqrt gam) := by
    have hrw : gam ^ 2 * |Real.log gam| ^ 4 =
        gam * Real.sqrt gam * (Real.sqrt gam * |Real.log gam| ^ 4) := by
      rw [mul_assoc, ← mul_assoc (Real.sqrt gam), hroot]
      ring
    rw [hrw]
    calc gam * Real.sqrt gam * (Real.sqrt gam * |Real.log gam| ^ 4)
        ≤ gam * Real.sqrt gam * 384 :=
          mul_le_mul_of_nonneg_left hlogb (by positivity)
      _ = 384 * (gam * Real.sqrt gam) := by ring
  have hbase0 : (0 : ℝ) ≤ eps ^ 2 * E ^ 2 * gam := by positivity
  have hSge : eps ^ 2 * E ^ 2 * gam ≤ (s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam) := by
    nlinarith [hsq, hbase0]
  calc Q5 * gam ^ 2 * (E ^ 4 * |Real.log gam| ^ 4)
      = (Q5 * E ^ 4) * (gam ^ 2 * |Real.log gam| ^ 4) := by ring
    _ ≤ (Q5 * E ^ 4) * (384 * (gam * Real.sqrt gam)) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
    _ = (384 * Q5 * gam * E ^ 2) * (Real.sqrt gam * E ^ 2) := by ring
    _ ≤ (384 * Q5 * gam * E ^ 2) * ((3 / 2 : ℝ) ^ 3 * eps ^ 2) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (384 * Q5 * (3 / 2 : ℝ) ^ 3) * (eps ^ 2 * E ^ 2 * gam) := by ring
    _ ≤ (384 * Q5 * (3 / 2 : ℝ) ^ 3) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) :=
        mul_le_mul_of_nonneg_left hSge (by positivity)

/-- **The deterministic remainder, absorbed** into the ordinary normal form. -/
protected theorem remainderTerm_le {eps Cms E gam s hgapR Q5 K : ℝ} (hQ5 : 0 ≤ Q5)
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hE1 : 1 ≤ E)
    (hgammaE : gam ≤ (E⁻¹) ^ 10) (hhgap0 : 0 ≤ hgapR) (hhgap : hgapR ≤ 2 * E)
    (hCms3 : (2 : ℝ) ≤ 3 * Cms) (hCms10 : (2 : ℝ) ≤ 10 * Cms)
    (hfloor : (2 / 3 : ℝ) * eps ^ (-Cms) ≤ E)
    (hK : 4 * Q5 * (3 / 2 : ℝ) ^ 10 + Q5 * (3 / 2 : ℝ) ^ 10 +
      384 * Q5 * (3 / 2 : ℝ) ^ 3 ≤ K) :
    Q5 * gam ^ 2 * (hgapR ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) ≤
      K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by
  have hE : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have h1 := MultiscaleAbsorptionArith.remainderGap_le (Cms := Cms) hQ5 hgam0 hs hs1 heps0 heps1 hE1 hgammaE
    hhgap0 hhgap hCms10 hfloor
  have h2 := MultiscaleAbsorptionArith.remainderScale_le (Cms := Cms) hQ5 hgam0 hs heps0 heps1 hE1 hgammaE
    hCms10 hfloor
  have h3 := MultiscaleAbsorptionArith.remainderLog_le (Cms := Cms) hQ5 hgam0 hgam1 hs hs1 heps0 heps1 hE1
    hgammaE hCms3 hfloor
  have hbase : (0 : ℝ) ≤ (s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam) := by positivity
  have hsplit : Q5 * gam ^ 2 * (hgapR ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) =
      Q5 * gam ^ 2 * hgapR ^ 2 + Q5 * gam ^ 2 * (s ^ 2)⁻¹ +
        Q5 * gam ^ 2 * (E ^ 4 * |Real.log gam| ^ 4) := by ring
  have hcollect : (4 * Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) +
      (Q5 * (3 / 2 : ℝ) ^ 10) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) +
      (384 * Q5 * (3 / 2 : ℝ) ^ 3) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) =
      (4 * Q5 * (3 / 2 : ℝ) ^ 10 + Q5 * (3 / 2 : ℝ) ^ 10 +
        384 * Q5 * (3 / 2 : ℝ) ^ 3) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) := by ring
  have hlast : (4 * Q5 * (3 / 2 : ℝ) ^ 10 + Q5 * (3 / 2 : ℝ) ^ 10 +
      384 * Q5 * (3 / 2 : ℝ) ^ 3) * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) ≤
      K * ((s⁻¹) ^ 2 * (eps ^ 2 * E ^ 2 * gam)) :=
    mul_le_mul_of_nonneg_right hK hbase
  linarith [h1, h2, h3, hsplit.le, hsplit.ge, hcollect.le, hcollect.ge, hlast]

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorptionArith
