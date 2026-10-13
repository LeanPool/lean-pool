/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineEnergySlot
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepTwoEnergy

/-!
# HomSpineTopScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `htop`: the printed Step-2 top-scale datum

## What this file supplies

`HomSpineEnergySlot.energySlot_of_regularityDisplay` carries exactly one
content-bearing hypothesis, `htop`:

```text
  3^{(1-α)X} · T.toReal  ≤  recutEnergyFactor M Y m ω · energyBracket σ_m 3^{m/2} K_g K_h^∞ K_h
```

where `T` is the Theorem-C bracket.  That bracket is (verbatim from
`anomalous_regularity`) the sum of THREE terms: the top-scale energy
`√ν‖∇u‖_{L²(□_m)}` and the two printed data terms `√(σ_m⁻¹)3^{m/2}K_g`,
`√σ_m 3^{m/2}K_h`.  This file

1. identifies the FIRST term with the left-hand side of the print's
   the energy-from-data display (`ofReal_sqrtNu_mul_gradAverage` — an identity: the
   `ℝ≥0∞` `eLpNorm` carrier of the root against the REAL
   `normalizedSetAverage` carrier of `HomStepTwoEnergy`, via the
   `volumeAverage_eq_toReal_lintegral` and the `H¹` integrability of `|∇u|²`);
2. absorbs the two data terms into `energyBracket` — the printed bracket's own
   summands, at no cost, since `√σ_m K_h^∞ ≥ 0`
   (`regularityDataBracket_toReal_le`);
3. produces `htop` from the printed top-scale energy bound
   (`htop_of_topScaleEnergy`), with the `3^{(1-α)X}` factor and the constant
   parked in the FREE slot `Y` of `recutEnergyFactor`, which is where the
   printed `EthmB(m)` carries `3^{(1-α)X_m(α)}`;
4. EXECUTES the print's own derivation of the top-scale energy bound
   (`topScaleEnergy_of_stepTwoA`) from the LANDED
   `HomStepTwoEnergy.exists_sqrt_nu_mul_gradL2_le` (= the coarse-graining right-hand side +
   the display bounding the `Λ`'s by the `𝓔`'s) and TWO named bridges;
5. closes the INDEX bridge unconditionally in the enlarged-`Y` reading
   (`htop_of_stepTwoA_enlargedY`): the two honest error indices of the
   two-index display are carried by `Y` itself.

## The two named bridges (nothing else is assumed)

* `StepTwoDataBridge` — the already-named component
  input: `CoarseGraining`'s note-normalized Besov data quantities at the index `t` are below
  the printed `3^{m/2}`-normalized Hölder data, at the constant
  `(1 - 3^{2t-1})^{-1/2}` recorded in that correction.  It needs `t < 1/2`
  STRICTLY; at `t = 1/2` the `C^{0,1/2}` data leg is infinite.
* `StepTwoIndexBridge` — the honest
  composition of the print's own inputs carries TWO error indices, `t/2` and
  `t`, where the printed display quotes the single `1/4`.  Collapsing them onto
  `1/4` needs an order monotonicity of `𝓔_{·,∞,2}` in the UNAVAILABLE direction
  (the `HomSeamRepin.parentTruncatedTwo_le_of_order_le` bounds the
  HIGHER order by the LOWER one, and `t/2 < 1/4` for every admissible `t`).
  `htop_of_stepTwoA_enlargedY` therefore does NOT use this bridge: it enlarges
  `Y` by `(1 + 𝓔sup_{t/2})(1 + 𝓔sup_t)`, which is exactly the print's Step-1
  Hölder budget applied to two more factors.  The bridge is kept as a named
  `Prop` so the narrow reading (the printed single index) remains statable.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The top-scale carrier identity -/

/-- The gradient square of an `H¹(□_m)` function is integrable on the cube. -/
theorem integrableOn_vecNormSq_grad_originCube {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) (openCubeSet (originCube d m)) volume := by
  simpa [vecNormSq] using
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 u.grad_memVectorL2

/-- **THE TOP-SCALE CARRIER IDENTITY.**

The Theorem-C bracket's first term — an `ℝ≥0∞` `eLpNorm` against the
normalized volume measure — IS the real quantity
`√ν · ‖∇u‖_{L²(□_m)}` that the energy-from-data display of `HomStepTwoEnergy` bounds.
No estimate is spent: the only steps are the real/`ℝ≥0∞` average bridge and
the `H¹` integrability of `|∇u|²`. -/
theorem ofReal_sqrtNu_mul_gradAverage (M : ABKModel d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) :
    ENNReal.ofReal (Real.sqrt (M.nu : ℝ)) *
        eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) =
      ENNReal.ofReal
        (Real.sqrt (M.nu : ℝ) *
          Real.sqrt
            (normalizedSetAverage (openCubeSet (originCube d m))
              (fun y => vecNormSq (u.grad y)))) := by
  have havg : (0 : ℝ) ≤
      volumeAverage (openCubeSet (originCube d m)) (fun y => vecNormSq (u.grad y)) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet _)
      (fun x _ => vecNormSq_nonneg _)
  have hpow : ENNReal.ofReal
        (volumeAverage (openCubeSet (originCube d m)) (fun y => vecNormSq (u.grad y))) ^
        (1 / 2 : ℝ) =
      ENNReal.ofReal
        (Real.sqrt
          (volumeAverage (openCubeSet (originCube d m))
            (fun y => vecNormSq (u.grad y)))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg havg (by norm_num), ← Real.sqrt_eq_rpow]
  rw [eLpNorm_two_sqrt_vecNormSq _ _ (aestronglyMeasurable_sqrt_vecNormSq_grad u subset_rfl),
    normalizedVolumeMeasureOn_openCubeSet,
    volumeAverage_eq_toReal_lintegral (originCube d m) (fun x => vecNormSq_nonneg _)
      (integrableOn_vecNormSq_grad_originCube u),
    hpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-! ## 2. The bracket, and its two data terms against `energyBracket` -/

/-- **The Theorem-C bracket**, transcribed verbatim from
`anomalous_regularity`: the top-scale energy plus the two printed data
terms. -/
def regularityDataBracket (M : ABKModel d) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d m))) (sigmaBarM Kg Kh : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (M.nu : ℝ)) *
      eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
        (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) +
    ENNReal.ofReal (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg) +
    ENNReal.ofReal (Real.sqrt sigmaBarM * Real.rpow 3 ((m : ℝ) / 2) * Kh)

/-- The printed introduction's energy display bracket is nonnegative on the printed data
signs. -/
theorem energyBracket_nonneg {sigma pow Kg KhInf Kh : ℝ} (hpow : 0 ≤ pow)
    (hKg : 0 ≤ Kg) (hKhInf : 0 ≤ KhInf) (hKh : 0 ≤ Kh) :
    0 ≤ energyBracket sigma pow Kg KhInf Kh := by
  have h1 : (0 : ℝ) ≤ Real.sqrt sigma⁻¹ * pow * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpow) hKg
  have h2 : (0 : ℝ) ≤ Real.sqrt sigma * (KhInf + pow * Kh) :=
    mul_nonneg (Real.sqrt_nonneg _) (by nlinarith only [hKhInf, hpow, hKh])
  rw [energyBracket]
  linarith only [h1, h2]

/-- The bracket is a single `ENNReal.ofReal` of the printed real sum. -/
theorem regularityDataBracket_eq_ofReal (M : ABKModel d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) {sigmaBarM Kg Kh : ℝ}
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) :
    regularityDataBracket M m u sigmaBarM Kg Kh =
      ENNReal.ofReal
        (Real.sqrt (M.nu : ℝ) *
            Real.sqrt
              (normalizedSetAverage (openCubeSet (originCube d m))
                (fun y => vecNormSq (u.grad y))) +
          Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
          Real.sqrt sigmaBarM * Real.rpow 3 ((m : ℝ) / 2) * Kh) := by
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have he : (0 : ℝ) ≤
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt
          (normalizedSetAverage (openCubeSet (originCube d m))
            (fun y => vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb : (0 : ℝ) ≤ Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpow) hKg
  rw [regularityDataBracket, ofReal_sqrtNu_mul_gradAverage M u,
    ← ENNReal.ofReal_add he hb, ← ENNReal.ofReal_add (by linarith only [he, hb])
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpow) hKh)]

/-- **The two data terms are inside `energyBracket`.**

The bracket's real value is the top-scale energy plus a quantity below the
printed introduction's energy display bracket; the only slack is the `√σ_m
K_h^∞` summand, which the printed bracket carries and the Theorem-C one does
not. -/
theorem regularityDataBracket_toReal_le (M : ABKModel d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) {sigmaBarM Kg Kh KhInf : ℝ}
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf) :
    (regularityDataBracket M m u sigmaBarM Kg Kh).toReal ≤
      Real.sqrt (M.nu : ℝ) *
          Real.sqrt
            (normalizedSetAverage (openCubeSet (originCube d m))
              (fun y => vecNormSq (u.grad y))) +
        energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have he : (0 : ℝ) ≤
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt
          (normalizedSetAverage (openCubeSet (originCube d m))
            (fun y => vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb : (0 : ℝ) ≤ Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpow) hKg
  have hc : (0 : ℝ) ≤ Real.sqrt sigmaBarM * (Real.rpow 3 ((m : ℝ) / 2) * Kh) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hpow hKh)
  have hslack : (0 : ℝ) ≤ Real.sqrt sigmaBarM * KhInf :=
    mul_nonneg (Real.sqrt_nonneg _) hKhInf
  have hsplit : energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh =
      Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
        (Real.sqrt sigmaBarM * KhInf +
          Real.sqrt sigmaBarM * (Real.rpow 3 ((m : ℝ) / 2) * Kh)) := by
    rw [energyBracket]; ring
  rw [regularityDataBracket_eq_ofReal M u hKg hKh,
    ENNReal.toReal_ofReal (by linarith only [he, hb, hc]), hsplit]
  linarith only [hslack, hc]

/-! ## 3. `htop`, produced -/

/-- **`htop`, PRODUCED.**

The binder `energySlot_of_regularityDisplay` consumes, at the Theorem-C
bracket, from the printed top-scale energy bound.  The `3^{(1-α)X}` factor and
the Step-2 constant are parked in the FREE slot `Y` of `recutEnergyFactor` —
the slot the printed `EthmB(m)` uses for exactly that factor — together with
any extra random factor `Y₀` the honest Step-2 display needs; `Y₀ = 1` is the
printed reading. -/
theorem htop_of_topScaleEnergy (M : ABKModel d) {m : ℤ} {X : ℕ} {alpha : ℝ}
    (u : H1Function (openCubeSet (originCube d m))) {sigmaBarM Kg Kh KhInf Ctop : ℝ}
    (omega : Cutoff.CutoffSample d) (Y0 : Cutoff.CutoffSample d → ℝ≥0∞)
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf) (hCtop : 0 ≤ Ctop)
    (hY1 : 1 ≤ Y0 omega) (hYtop : Y0 omega ≠ ⊤)
    (hfinE : fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤)
    (hEnergy :
      Real.sqrt (M.nu : ℝ) *
          Real.sqrt
            (normalizedSetAverage (openCubeSet (originCube d m))
              (fun y => vecNormSq (u.grad y))) ≤
        Ctop *
            (Y0 omega *
              (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal *
          energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :
    (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
        (regularityDataBracket M m u sigmaBarM Kg Kh).toReal ≤
      recutEnergyFactor M
          (fun w => ENNReal.ofReal ((Ctop + 1) * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ))) * Y0 w) m
          omega *
        energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hB : (0 : ℝ) ≤ energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    energyBracket_nonneg hpow hKg hKhInf hKh
  have hX : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  set V : ℝ :=
    (Y0 omega *
      (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal with hVdef
  have hV1 : (1 : ℝ) ≤ V := by
    have hone : (1 : ℝ≥0∞) ≤
        Y0 omega *
          (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega) := by
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ Y0 omega *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega) :=
          mul_le_mul' hY1 le_self_add
    have hne : Y0 omega *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega) ≠ ⊤ :=
      ENNReal.mul_ne_top hYtop (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hfinE⟩)
    rw [hVdef]
    simpa using ENNReal.toReal_mono hne hone
  /- the bracket, cut and absorb -/
  have hcut := regularityDataBracket_toReal_le (M := M) (m := m) u
    (sigmaBarM := sigmaBarM) (KhInf := KhInf) hKg hKh hKhInf
  have hstep : (regularityDataBracket M m u sigmaBarM Kg Kh).toReal ≤
      (Ctop + 1) * V * energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    have hone : energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ≤
        V * energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
      nlinarith only [hV1, hB]
    have hfin : Ctop * V *
        energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh +
        V * energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh =
        (Ctop + 1) * V *
          energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by ring
    linarith only [hcut, hEnergy, hone, hfin]
  /- the random factor, comput -/
  have hfactor : recutEnergyFactor M
        (fun w => ENNReal.ofReal ((Ctop + 1) * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ))) * Y0 w) m
        omega =
      (Ctop + 1) * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) * V := by
    rw [recutEnergyFactor, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (by linarith only [hCtop]) hX)]
    rw [hVdef, ENNReal.toReal_mul]
    ring
  rw [hfactor]
  have hmul := mul_le_mul_of_nonneg_left hstep hX
  calc (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
        (regularityDataBracket M m u sigmaBarM Kg Kh).toReal
      ≤ (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
          ((Ctop + 1) * V *
            energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := hmul
    _ = (Ctop + 1) * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) * V *
          energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by ring

/-! ## 4. The two named bridges of the print's Step-2 chain -/

/-- **THE DATA-LEG BRIDGE** (the already-named component
input).  `CoarseGraining`'s note-normalized Besov data quantities at the index `t` are below
the printed `3^{m/2}`-normalized Hölder data of the manuscript.  The correction records
the constant `(1 - 3^{2t-1})^{-1/2}` and the STRICT requirement `t < 1/2`.

THIS IS AN INPUT.  It is never proved in this repository. -/
def StepTwoDataBridge (m : ℤ) (t : ℝ) (g gradh : Vec d → Vec d)
    (Cdata Kg KhInf Kh : ℝ) : Prop :=
  scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) t (fun x => -g x) ≤
      Cdata * (Real.rpow 3 ((m : ℝ) / 2) * Kg) ∧
    scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) t gradh ≤
      Cdata * (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)

/-- **THE INDEX BRIDGE**.

The honest composition of the print's own Step-2 inputs carries TWO error
indices, `t/2` on the `g` leg and `t` on the `∇h` leg; the printed display
quotes the single `1/4`.  This `Prop` is the collapse onto a common factor `W`.

At `W:= (1 + 𝓔sup_{1/4})` the collapse is exactly what the print asserts and is
NOT available (see the module docstring); `htop_of_stepTwoA_enlargedY` avoids it
by carrying `W = (1 + 𝓔sup_{t/2})(1 + 𝓔sup_t)(1 + 𝓔sup_{1/4})` instead, at
`Kidx = 1`. -/
def StepTwoIndexBridge [NeZero d] (M : ABKModel d) (L m : ℤ) (t Kidx W : ℝ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  1 + fluxCorrectedError M L m (t / 2) omega ≤ Kidx * W ∧
    1 + fluxCorrectedError M L m t omega ≤ Kidx * W

/-! ## 5. The print's Step-2 chain, executed -/

/-- One leg of the Step-2 display, with its error factor and its data leg
replaced. -/
private theorem stepTwoLeg {c e w K B Cd P : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hw : 0 ≤ w) (hB : 0 ≤ B) (heW : e ≤ K * w) (hBP : B ≤ Cd * P) :
    c * e * B ≤ c * K * Cd * w * P := by
  have h1 : c * e * B ≤ c * (K * w) * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heW hc) hB
  have hcw : (0 : ℝ) ≤ c * (K * w) := mul_nonneg hc (mul_nonneg hK hw)
  calc c * e * B ≤ c * (K * w) * B := h1
    _ ≤ c * (K * w) * (Cd * P) := mul_le_mul_of_nonneg_left hBP hcw
    _ = c * K * Cd * w * P := by ring

/-- The two legs, added: the exact shape `exists_sqrt_nu_mul_gradL2_le` produces
against the exact shape `energyBracket` splits into. -/
private theorem stepTwoCombineAbstract
    {C a1 a2 r e1 e2 Bg Bh sg sh Kidx W Cdata p1 p2 : ℝ}
    (hC : 0 ≤ C) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hr : 0 ≤ r) (hBg : 0 ≤ Bg)
    (hBh : 0 ≤ Bh) (hsg : 0 ≤ sg) (hsh : 0 ≤ sh) (hK : 0 ≤ Kidx) (hW : 0 ≤ W)
    (hCd : 0 ≤ Cdata) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hi1 : e1 ≤ Kidx * W) (hi2 : e2 ≤ Kidx * W)
    (hg : sg * Bg ≤ Cdata * p1) (hh : sh * Bh ≤ Cdata * p2) :
    C * a1 * (sg * (r * e1)) * Bg + C * a2 * (sh * (r * e2)) * Bh ≤
      C * (a1 + a2) * r * Kidx * Cdata * W * (p1 + p2) := by
  have hc1 : (0 : ℝ) ≤ C * a1 * r := mul_nonneg (mul_nonneg hC ha1) hr
  have hc2 : (0 : ℝ) ≤ C * a2 * r := mul_nonneg (mul_nonneg hC ha2) hr
  have h1 : C * a1 * (sg * (r * e1)) * Bg ≤ C * a1 * r * Kidx * Cdata * W * p1 := by
    have := stepTwoLeg (c := C * a1 * r) (e := e1) (w := W) (K := Kidx)
      (B := sg * Bg) (Cd := Cdata) (P := p1) hc1 hK hW (mul_nonneg hsg hBg) hi1 hg
    calc C * a1 * (sg * (r * e1)) * Bg = C * a1 * r * e1 * (sg * Bg) := by ring
      _ ≤ C * a1 * r * Kidx * Cdata * W * p1 := this
  have h2 : C * a2 * (sh * (r * e2)) * Bh ≤ C * a2 * r * Kidx * Cdata * W * p2 := by
    have := stepTwoLeg (c := C * a2 * r) (e := e2) (w := W) (K := Kidx)
      (B := sh * Bh) (Cd := Cdata) (P := p2) hc2 hK hW (mul_nonneg hsh hBh) hi2 hh
    calc C * a2 * (sh * (r * e2)) * Bh = C * a2 * r * e2 * (sh * Bh) := by ring
      _ ≤ C * a2 * r * Kidx * Cdata * W * p2 := this
  have hx1 : (0 : ℝ) ≤ C * a1 * r * Kidx * Cdata * W * p2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc1 hK) hCd) hW) hp2
  have hx2 : (0 : ℝ) ≤ C * a2 * r * Kidx * Cdata * W * p1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc2 hK) hCd) hW) hp1
  have hexp : C * (a1 + a2) * r * Kidx * Cdata * W * (p1 + p2) =
      C * a1 * r * Kidx * Cdata * W * p1 + C * a2 * r * Kidx * Cdata * W * p2 +
        (C * a1 * r * Kidx * Cdata * W * p2 + C * a2 * r * Kidx * Cdata * W * p1) := by
    ring
  linarith only [h1, h2, hx1, hx2, hexp]

/-- The printed data bracket, split into the two legs the Step-2 display pairs
against. -/
private theorem energyBracket_split (sigma pow Kg KhInf Kh : ℝ) :
    energyBracket sigma pow Kg KhInf Kh =
      Real.sqrt sigma⁻¹ * (pow * Kg) + Real.sqrt sigma * (KhInf + pow * Kh) := by
  rw [energyBracket]; ring

/-- **STEP 2, EXECUTED**.

The print's own derivation, on the carriers: the LANDED
`exists_sqrt_nu_mul_gradL2_le` (= the coarse-graining right-hand side + the
display bounding the `Λ`'s by the `𝓔`'s), the data-leg bridge and the index
bridge compose into the printed top-scale energy bound at the explicit constant

```text
  C_step (t^{-3/2} + t^{-1/2}) √(2d) · K_idx · C_data.
```

Nothing else is used; the `t`-powers and the `√(2d)` are `CoarseGraining`'s own
and stay displayed . -/
theorem topScaleEnergy_of_stepTwoA (d : ℕ) [NeZero d] :
    ∃ Cstep : ℝ, 0 < Cstep ∧
      ∀ (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
        {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
        {t Kidx W Cdata Kg Kh KhInf : ℝ},
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u hdat g →
        0 < t → t < 1 →
        ForceBesovRegularity (originCube d m) t (fun x => -g x) →
        ForceBesovRegularity (originCube d m) t hdat.grad →
        StepTwoDataBridge m t g hdat.grad Cdata Kg KhInf Kh →
        StepTwoIndexBridge M L m t Kidx W omega →
        0 ≤ Kidx → 0 ≤ W → 0 ≤ Cdata → 0 ≤ Kg → 0 ≤ Kh → 0 ≤ KhInf →
          Real.sqrt (M.nu : ℝ) *
              Real.sqrt
                (normalizedSetAverage (openCubeSet (originCube d m))
                  (fun y => vecNormSq (u.grad y))) ≤
            Cstep * (Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ))) *
                Real.sqrt (2 * (d : ℝ)) * Kidx * Cdata * W *
              energyBracket (Annealed.sigmaBar M m : ℝ) (Real.rpow 3 ((m : ℝ) / 2)) Kg
                KhInf Kh := by
  obtain ⟨C, hCpos, hmain⟩ := exists_sqrt_nu_mul_gradL2_le d
  refine ⟨C, hCpos, ?_⟩
  intro M L m omega u hdat g t Kidx W Cdata Kg Kh KhInf hsol ht0 ht1 hgB hhB hdata
    hindex hK hW hCd hKg hKh hKhInf
  obtain ⟨hdatag, hdatah⟩ := hdata
  obtain ⟨hind1, hind2⟩ := hindex
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hBg : (0 : ℝ) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) t (fun x => -g x) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hgB
  have hBh : (0 : ℝ) ≤
      scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) t hdat.grad := by
    have hsem :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hhB
    have hmean : (0 : ℝ) ≤
        Real.sqrt (vecNormSq (cubeAverageVec (originCube d m) hdat.grad)) :=
      Real.sqrt_nonneg _
    rw [scaleNormalizedPositiveBesovVectorNormTwo]
    linarith only [hsem, hmean]
  have hstep := hmain M L m omega hsol ht0 ht1 hgB hhB
  rw [homogenizationErrorOnCube_scalarMatrix_eq_fluxCorrectedError M L m (t / 2) omega,
    homogenizationErrorOnCube_scalarMatrix_eq_fluxCorrectedError M L m t omega] at hstep
  refine hstep.trans ?_
  rw [energyBracket_split]
  refine stepTwoCombineAbstract (C := C) (a1 := Real.rpow t (-(3 / 2 : ℝ)))
    (a2 := Real.rpow t (-(1 / 2 : ℝ))) (r := Real.sqrt (2 * (d : ℝ)))
    (e1 := 1 + fluxCorrectedError M L m (t / 2) omega)
    (e2 := 1 + fluxCorrectedError M L m t omega) hCpos.le
    (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _) (Real.sqrt_nonneg _) hBg hBh
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hK hW hCd
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hpow hKg))
    (mul_nonneg (Real.sqrt_nonneg _) (by
      have : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) * Kh := mul_nonneg hpow hKh
      linarith only [hKhInf, this])) hind1 hind2 ?_ ?_
  · calc Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) t (fun x => -g x)
        ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
            (Cdata * (Real.rpow 3 ((m : ℝ) / 2) * Kg)) :=
          mul_le_mul_of_nonneg_left hdatag (Real.sqrt_nonneg _)
      _ = Cdata *
            (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Real.rpow 3 ((m : ℝ) / 2) * Kg)) := by
          ring
  · calc Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
        scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) t hdat.grad
        ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
            (Cdata * (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) :=
          mul_le_mul_of_nonneg_left hdatah (Real.sqrt_nonneg _)
      _ = Cdata *
            (Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
              (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) := by ring

/-! ## 6. The index bridge, CLOSED at the enlarged `Y` -/

/-- **The enlargement of the printed `Y` slot.**

`EthmB(m)`'s `Y` slot carries `3^{(1-α)X_m(α)}`; the honest two-index Step-2
display asks it to carry, in addition, the two `sup_{L ≥ m}` error factors at
the display's OWN indices `t/2` and `t`.  That is exactly two more factors for
the print's Step-1 Hölder budget, and no new object: the factors are the
public observable at two more orders. -/
def stepTwoEnlargedY (M : ABKModel d) (m : ℤ) {t : ℝ} (ht : 0 < t) :
    Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega =>
    (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega) *
      (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega)

/-- One factor of the enlarged `Y`, as a real. -/
private theorem one_add_error_le_toReal [NeZero d] (M : ABKModel d) {L m : ℤ}
    (hL : m ≤ L) {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d)
    (hrep : fluxCorrectedError M L m s omega =
      fluxCorrectedErrorRepresentative M L m ⟨s, hs⟩ omega)
    (hfin : fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega ≠ ⊤) :
    1 + fluxCorrectedError M L m s omega ≤
      (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega).toReal := by
  have hle : ENNReal.ofReal (fluxCorrectedError M L m s omega) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega := by
    rw [hrep]
    exact le_fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega hL
  have hreal : fluxCorrectedError M L m s omega ≤
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
  have hadd : (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega).toReal =
      1 + (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨s, hs⟩ omega).toReal := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top hfin, ENNReal.toReal_one]
  rw [hadd]
  linarith only [hreal]

/-- A product of three factors above `1` dominates its first factor. -/
private theorem le_mul_three {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b * c := by
  have ha0 : (0 : ℝ) ≤ a := by linarith only [ha]
  have hb0 : (0 : ℝ) ≤ b := by linarith only [hb]
  have h1 : a ≤ a * b := le_mul_of_one_le_right ha0 hb
  have h2 : a * b ≤ a * b * c := le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
  linarith only [h1, h2]

/-- Every factor of the enlarged `Y` is at least `1`. -/
private theorem one_le_toReal_one_add {E : ℝ≥0∞} (hfin : E ≠ ⊤) :
    (1 : ℝ) ≤ (1 + E).toReal := by
  have hne : (1 : ℝ≥0∞) + E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hfin⟩
  simpa using ENNReal.toReal_mono hne (le_self_add : (1 : ℝ≥0∞) ≤ 1 + E)

/-- **THE INDEX BRIDGE, CLOSED** — at the enlarged `Y` and at `K_idx = 1`.

No order monotonicity of `𝓔_{·,∞,2}` is used: each honest index is carried by
its OWN factor of `stepTwoEnlargedY`, and `le_fluxCorrectedTwoScaleError
ObservableSup` supplies the `sup_{L ≥ m}` step.  The two `hrep` hypotheses are
the standard a.e. carrier identification
(`Support.fluxCorrectedError_ae_eq_representative`), not new content. -/
theorem stepTwoIndexBridge_of_representative [NeZero d] (M : ABKModel d) {L m : ℤ}
    (hL : m ≤ L) {t : ℝ} (ht : 0 < t) (omega : Cutoff.CutoffSample d)
    (hrep1 : fluxCorrectedError M L m (t / 2) omega =
      fluxCorrectedErrorRepresentative M L m ⟨t / 2, half_pos ht⟩ omega)
    (hrep2 : fluxCorrectedError M L m t omega =
      fluxCorrectedErrorRepresentative M L m ⟨t, ht⟩ omega)
    (hfin1 : fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega ≠ ⊤)
    (hfin2 : fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega ≠ ⊤)
    (hfinE : fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤) :
    StepTwoIndexBridge M L m t 1
      ((stepTwoEnlargedY M m ht omega *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal)
      omega := by
  have h1 := one_le_toReal_one_add hfin1
  have h2 := one_le_toReal_one_add hfin2
  have h3 := one_le_toReal_one_add hfinE
  have hW : (stepTwoEnlargedY M m ht omega *
      (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal =
      (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega).toReal *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega).toReal *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega).toReal := by
    rw [stepTwoEnlargedY, ENNReal.toReal_mul, ENNReal.toReal_mul]
  refine ⟨?_, ?_⟩
  · have hstep := one_add_error_le_toReal M hL (half_pos ht) omega hrep1 hfin1
    rw [hW, one_mul]
    exact hstep.trans (le_mul_three h1 h2 h3)
  · have hstep := one_add_error_le_toReal M hL ht omega hrep2 hfin2
    rw [hW, one_mul]
    refine hstep.trans ?_
    calc (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega).toReal
        ≤ (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega).toReal *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩
              omega).toReal *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega).toReal :=
          le_mul_three h2 h1 h3
      _ = (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩
              omega).toReal *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega).toReal *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega).toReal := by
          ring

/-! ## 7. `htop`, with the index bridge discharged -/

/-- **`htop`, PRODUCED FROM THE PRINT'S OWN STEP-2 CHAIN.**

Sections 5 and 6 composed into section 3: the binder
`energySlot_of_regularityDisplay` consumes, at the Theorem-C bracket, from

* the LANDED the coarse-graining right-hand side + the display bounding the `Λ`'s by the `𝓔`'s
composition
  (`exists_sqrt_nu_mul_gradL2_le`),
* the ONE named data-leg input `StepTwoDataBridge`,
* the standard a.e. carrier identification `hrep1`/`hrep2`, and
* three a.e. finiteness cuts.

NO order monotonicity of `𝓔_{·,∞,2}` is used: the printed `Y` slot is enlarged
by `stepTwoEnlargedY`, which is the two honest indices of the two-index display
carried where the print carries `3^{(1-α)X_m(α)}`. -/
theorem htop_of_stepTwoA_enlargedY (d : ℕ) [NeZero d] :
    ∃ Cstep : ℝ, 0 < Cstep ∧
      ∀ (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
        {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
        {t : ℝ} (ht : 0 < t) {Cdata Kg Kh KhInf alpha : ℝ} {X : ℕ},
        m ≤ L → t < 1 →
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u hdat g →
        ForceBesovRegularity (originCube d m) t (fun x => -g x) →
        ForceBesovRegularity (originCube d m) t hdat.grad →
        StepTwoDataBridge m t g hdat.grad Cdata Kg KhInf Kh →
        fluxCorrectedError M L m (t / 2) omega =
          fluxCorrectedErrorRepresentative M L m ⟨t / 2, half_pos ht⟩ omega →
        fluxCorrectedError M L m t omega =
          fluxCorrectedErrorRepresentative M L m ⟨t, ht⟩ omega →
        fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega ≠ ⊤ →
        fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega ≠ ⊤ →
        fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤ →
        0 ≤ Cdata → 0 ≤ Kg → 0 ≤ Kh → 0 ≤ KhInf →
          (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
              (regularityDataBracket M m u (Annealed.sigmaBar M m : ℝ) Kg Kh).toReal ≤
            recutEnergyFactor M
                (fun w =>
                  ENNReal.ofReal
                      ((Cstep * (Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ))) *
                            Real.sqrt (2 * (d : ℝ)) * Cdata + 1) *
                        (3 : ℝ) ^ ((1 - alpha) * (X : ℝ))) *
                    stepTwoEnlargedY M m ht w)
                m omega *
              energyBracket (Annealed.sigmaBar M m : ℝ) (Real.rpow 3 ((m : ℝ) / 2)) Kg
                KhInf Kh := by
  obtain ⟨Cstep, hCstep, hstep⟩ := topScaleEnergy_of_stepTwoA d
  refine ⟨Cstep, hCstep, ?_⟩
  intro M L m omega u hdat g t ht Cdata Kg Kh KhInf alpha X hL ht1 hsol hgB hhB hdata
    hrep1 hrep2 hfin1 hfin2 hfinE hCd hKg hKh hKhInf
  set Y0 : Cutoff.CutoffSample d → ℝ≥0∞ := stepTwoEnlargedY M m ht with hY0def
  set W : ℝ :=
    (Y0 omega * (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal
    with hWdef
  have hindex : StepTwoIndexBridge M L m t 1 W omega := by
    rw [hWdef, hY0def]
    exact stepTwoIndexBridge_of_representative M hL ht omega hrep1 hrep2 hfin1 hfin2 hfinE
  have hY1 : (1 : ℝ≥0∞) ≤ Y0 omega := by
    rw [hY0def, stepTwoEnlargedY]
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega) *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega) :=
        mul_le_mul' le_self_add le_self_add
  have hYtop : Y0 omega ≠ ⊤ := by
    rw [hY0def, stepTwoEnlargedY]
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hfin1⟩)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hfin2⟩)
  have hW0 : (0 : ℝ) ≤ W := ENNReal.toReal_nonneg
  have hE := hstep M L m omega hsol ht ht1 hgB hhB hdata hindex zero_le_one hW0 hCd hKg
    hKh hKhInf
  rw [show Cstep * (Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ))) *
        Real.sqrt (2 * (d : ℝ)) * 1 * Cdata * W *
        energyBracket (Annealed.sigmaBar M m : ℝ) (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh =
      Cstep * (Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ))) *
        Real.sqrt (2 * (d : ℝ)) * Cdata * W *
        energyBracket (Annealed.sigmaBar M m : ℝ) (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh
      from by ring] at hE
  have hCtop : (0 : ℝ) ≤ Cstep * (Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ))) *
      Real.sqrt (2 * (d : ℝ)) * Cdata := by
    have h1 : (0 : ℝ) ≤ Real.rpow t (-(3 / 2 : ℝ)) + Real.rpow t (-(1 / 2 : ℝ)) := by
      have ha : (0 : ℝ) ≤ Real.rpow t (-(3 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
      have hb : (0 : ℝ) ≤ Real.rpow t (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
      linarith only [ha, hb]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCstep.le h1) (Real.sqrt_nonneg _)) hCd
  exact htop_of_topScaleEnergy M u omega Y0 hKg hKh hKhInf hCtop hY1 hYtop hfinE hE

end

end Algsuperdiff.Section4.Provider.Homogenization
