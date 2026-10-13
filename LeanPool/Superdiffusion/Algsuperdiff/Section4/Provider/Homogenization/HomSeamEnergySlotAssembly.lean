/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomProviderBAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfBundle
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGaugeCongruence
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDataBridge

/-!
# HomSeamEnergySlotAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The energy conjuncts of the seam residue, assembled at the enlarged `Y`

## What this file supplies

The seam residue's energy supply asks, per `ω` and per
printed elliptic pair, for `{0 ≤ S, the partial-sum slot, hSbound}` plus the
multiscale clause.  This file produces the FIRST THREE from the Theorem-C
display, by supplying the step no file supplies:

```text
  HomProviderBAssembly.RegularityDisplayAt   ⟶   HomSpineEnergyDensity.RegularityEnergyDisplay
```

(`regularityEnergyDisplay_of_regularityDisplayAt`), and then composing
`HomSpineTopScale.htop_of_stepTwoA_enlargedY` with
`HomSpineEnergySlot.energySlot_of_regularityDisplay` at the seam's own `Y`
slot.

## The two binder mismatches the slice resolves (both DISPLAYED, neither assumed
away)

1. **The `K_h^∞` gate.**  The display's own sup binder is
   `‖∇h‖ ≤ 3^{m/2}K_h`, while the seam's per-`ω` datum carries the root's
   `‖∇h‖ ≤ K_h^∞` with a FREE `K_h`.  The slice runs the display at the
   shifted constant `seamShiftedKh m K_h K_h^∞ = 3^{-m/2}K_h^∞ + K_h`, at which
   `3^{m/2}·K_h' = K_h^∞ + 3^{m/2}K_h` — so the bracket's third term is
   EXACTLY the printed `energyBracket`'s second summand.  Nothing is lost:
   running `htop` at `(K_h:= K_h', K_h^∞:= 0)` returns the printed bracket on
   the nose (`energyBracket_zero_seamShiftedKh`).

2. **`HasGradientOn`.**  The `anomalous_regularity` display carries
   the classical-gradient binder `HasGradientOn □_m h.toFun h.grad` (the V3
   amendment).  The frozen ROOT carries it too, but the spine drops it
   (the §4.5 provider introduces it and discards it), so the per-`ω` residues
   do NOT bind it.
   Every theorem below therefore takes it as an EXPLICIT hypothesis: the energy
   slot is available exactly for the pairs the theorem speaks about.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The shifted Hölder constant of the sup binder -/

/-- **The display's Hölder constant at the root's own sup binder.**

The display gates its data by `‖∇h‖_{L^∞} ≤ 3^{m/2}K_h`; the root binds
`‖∇h‖_{L^∞} ≤ K_h^∞` with an independent `K_h`.  Running the display at
`3^{-m/2}K_h^∞ + K_h` meets the gate and reproduces the printed bracket. -/
def seamShiftedKh (m : ℤ) (Kh KhInf : ℝ) : ℝ :=
  Real.rpow 3 (-((m : ℝ) / 2)) * KhInf + Kh

theorem seamShiftedKh_nonneg {m : ℤ} {Kh KhInf : ℝ} (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf) :
    0 ≤ seamShiftedKh m Kh KhInf := by
  have h : (0 : ℝ) ≤ Real.rpow 3 (-((m : ℝ) / 2)) * KhInf :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKhInf
  rw [seamShiftedKh]
  linarith only [h, hKh]

theorem le_seamShiftedKh {m : ℤ} {Kh KhInf : ℝ} (hKhInf : 0 ≤ KhInf) :
    Kh ≤ seamShiftedKh m Kh KhInf := by
  have h : (0 : ℝ) ≤ Real.rpow 3 (-((m : ℝ) / 2)) * KhInf :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKhInf
  rw [seamShiftedKh]
  linarith only [h]

/-- **The shift is exact**: the weight `3^{m/2}` applied to the shifted
constant is the printed sum `K_h^∞ + 3^{m/2}K_h`. -/
theorem three_rpow_mul_seamShiftedKh (m : ℤ) (Kh KhInf : ℝ) :
    Real.rpow 3 ((m : ℝ) / 2) * seamShiftedKh m Kh KhInf =
      KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh := by
  have hcancel : Real.rpow 3 ((m : ℝ) / 2) * Real.rpow 3 (-((m : ℝ) / 2)) = 1 := by
    show (3 : ℝ) ^ ((m : ℝ) / 2) * (3 : ℝ) ^ (-((m : ℝ) / 2)) = 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  rw [seamShiftedKh, mul_add, ← mul_assoc, hcancel, one_mul]

/-- The printed bracket at `K_h^∞ = 0` and the shifted constant IS the printed
bracket at the root's own pair.  This is the identity that makes the `K_h^∞`
gate free. -/
theorem energyBracket_zero_seamShiftedKh (sigma : ℝ) (m : ℤ) (Kg Kh KhInf : ℝ) :
    energyBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg 0 (seamShiftedKh m Kh KhInf) =
      energyBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  rw [energyBracket, energyBracket, three_rpow_mul_seamShiftedKh]
  ring

/-! ## 2. The bracket is finite -/

/-- The Theorem-C bracket is never `⊤` on the printed data signs. -/
theorem regularityDataBracket_ne_top (M : ABKModel d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) {sigmaBarM Kg Kh : ℝ}
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) :
    regularityDataBracket M m u sigmaBarM Kg Kh ≠ ⊤ := by
  rw [regularityDataBracket_eq_ofReal M u hKg hKh]
  exact ENNReal.ofReal_ne_top

/-! ## 3. THE SLICE: the display, cut at one finite minimal scale -/

/-- **THE MISSING LINK.**

`HomProviderBAssembly.RegularityDisplayAt` — the byte transcription of
`anomalous_regularity`'s per-`ω` body — sliced into
`HomSpineEnergyDensity.RegularityEnergyDisplay` at one sample, one admissible
`L`, one elliptic pair and one FINITE value `k` of the minimal scale.

Both binder mismatches of the module docstring are resolved in the statement:
the sup gate is met at `seamShiftedKh`, and `hgrad` is the theorem's own
classical-gradient binder. -/
theorem regularityEnergyDisplay_of_regularityDisplayAt [NeZero d] (M : ABKModel d)
    {Creg alpha : ℝ} {m : ℤ} {X : Cutoff.CutoffSample d → ℕ∞}
    {omega : Cutoff.CutoffSample d}
    (hdisp : RegularityDisplayAt M Creg alpha m X omega) {k : ℕ}
    (hXk : X omega = ((k : ℕ) : ℕ∞)) {L : ℤ} (hL : m ≤ L)
    {u h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    {Kg Kh KhInf : ℝ} (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf)
    (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (originCube d m) u h g)
    (hKgB : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhB : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad)
    (hsup : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf)
    (hgrad : HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad) :
    RegularityEnergyDisplay M m k u Creg alpha
      (regularityDataBracket M m u ((Annealed.sigmaBar M m : ℝ)) Kg
        (seamShiftedKh m Kh KhInf)) := by
  have hKhB' : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
      (seamShiftedKh m Kh KhInf) h.grad :=
    hKhB.mono_const (le_seamShiftedKh hKhInf)
  have hsup' : ∀ y ∈ openCubeSet (originCube d m),
      ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * seamShiftedKh m Kh KhInf := by
    intro y hy
    have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) * Kh :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh
    rw [three_rpow_mul_seamShiftedKh]
    exact le_trans (hsup y hy) (by linarith only [hpow])
  intro x hx n hn hgate
  have hn0 : (0 : ℤ) ≤ m - n := by omega
  have hcast : ((k : ℤ)) ≤ (((m - n).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hn0]; exact hgate
  have hnat : k ≤ (m - n).toNat := by exact_mod_cast hcast
  have henat : X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) := by
    rw [hXk]; exact_mod_cast hnat
  exact (hdisp L hL u h g Kg (seamShiftedKh m Kh KhInf) hsol hKgB hKhB' hsup' hgrad x hx
    n hn henat).1

/-! ## 4. The pinned top-scale constant -/

private theorem quarter_rpow (c : ℝ) : Real.rpow (1 / 4 : ℝ) c = Real.rpow 2 (-2 * c) := by
  show ((1 : ℝ) / 4) ^ c = (2 : ℝ) ^ (-2 * c)
  have hb4 : (2 : ℝ) ^ (((2 : ℕ) : ℝ)) = 4 := by rw [Real.rpow_natCast]; norm_num
  have h4 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-(((2 : ℕ) : ℝ))) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hb4]
    norm_num
  rw [h4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1

private theorem quarter_rpow_sum :
    Real.rpow (1 / 4 : ℝ) (-(3 / 2 : ℝ)) + Real.rpow (1 / 4 : ℝ) (-(1 / 2 : ℝ)) = 10 := by
  have hb8 : (2 : ℝ) ^ (((3 : ℕ) : ℝ)) = 8 := by rw [Real.rpow_natCast]; norm_num
  have h1 : Real.rpow (1 / 4 : ℝ) (-(3 / 2 : ℝ)) = 8 := by
    rw [quarter_rpow]
    show (2 : ℝ) ^ (-2 * -(3 / 2 : ℝ)) = 8
    rw [show -2 * -(3 / 2 : ℝ) = (((3 : ℕ) : ℝ)) by push_cast; norm_num, hb8]
  have h2 : Real.rpow (1 / 4 : ℝ) (-(1 / 2 : ℝ)) = 2 := by
    rw [quarter_rpow]
    show (2 : ℝ) ^ (-2 * -(1 / 2 : ℝ)) = 2
    rw [show -2 * -(1 / 2 : ℝ) = (1 : ℝ) by norm_num, Real.rpow_one]
  rw [h1, h2]; norm_num

/-- **THE PINNED `C_top` OF THE SEAM.**

`HomSpineTopScale.htop_of_stepTwoA_enlargedY`'s own constant at the consumer pin
`t = 1/4` and at the discharged data-bridge constant
`HomSpineDataBridge.stepTwoDataConstPinned`.  Model-free: `d`, the Step-2
constant, and nothing else. -/
def seamTopScaleConst (d : ℕ) (Cstep : ℝ) : ℝ :=
  10 * Cstep * Real.sqrt (2 * (d : ℝ)) * stepTwoDataConstPinned d + 1

theorem seamTopScaleConst_nonneg (d : ℕ) {Cstep : ℝ} (hCstep : 0 ≤ Cstep) :
    0 ≤ seamTopScaleConst d Cstep := by
  have h : (0 : ℝ) ≤ 10 * Cstep * Real.sqrt (2 * (d : ℝ)) * stepTwoDataConstPinned d :=
    mul_nonneg (mul_nonneg (by linarith only [hCstep]) (Real.sqrt_nonneg _))
      (stepTwoDataConstPinned_nonneg d)
  rw [seamTopScaleConst]; linarith only [h]

/-- The symbolic constant of `htop_of_stepTwoA_enlargedY` at `t = 1/4` and the
pinned data constant IS `seamTopScaleConst`. -/
theorem seamTopScaleConst_eq (d : ℕ) (Cstep : ℝ) :
    Cstep * (Real.rpow (1 / 4 : ℝ) (-(3 / 2 : ℝ)) + Real.rpow (1 / 4 : ℝ) (-(1 / 2 : ℝ))) *
        Real.sqrt (2 * (d : ℝ)) * stepTwoDataConstPinned d + 1 =
      seamTopScaleConst d Cstep := by
  rw [seamTopScaleConst, quarter_rpow_sum]; ring

/-! ## 5. The `Y`-slot identification -/

/-- **THE SEAM's `Y` SLOT IS `htop`'s `Y` SLOT**, at every sample where the
minimal scale is finite.  The `ℕ∞` cut is the only content: off it
`homMinimalScaleFactor` is `⊤` and the printed factor carries no information. -/
theorem seamEnlargedY_apply_of_eq_coe (M : ABKModel d) (m : ℤ) {Ctop alpha : ℝ}
    (hCtop : 0 ≤ Ctop) {X : Cutoff.CutoffSample d → ℕ∞}
    (omega : Cutoff.CutoffSample d) {k : ℕ} (hXk : X omega = ((k : ℕ) : ℕ∞)) :
    seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - alpha) X) omega =
      ENNReal.ofReal (Ctop * (3 : ℝ) ^ ((1 - alpha) * (k : ℝ))) *
        stepTwoEnlargedY M m (show (0 : ℝ) < 1 / 4 by norm_num) omega := by
  have hY : homMinimalScaleFactor (1 - alpha) X omega =
      ENNReal.ofReal ((3 : ℝ) ^ ((1 - alpha) * (k : ℝ))) := by
    rw [homMinimalScaleFactor, hXk, enatThreeRpow_coe]
  rw [seamEnlargedY, hY, ← mul_assoc, ← ENNReal.ofReal_mul hCtop]

/-! ## 6. `htop` at the seam's own `Y` -/

theorem seamQuarterPos : (0 : ℝ) < 1 / 4 := by norm_num

/-- **`htop`, AT THE SEAM's OWN `Y` SLOT.**

`HomSpineTopScale.htop_of_stepTwoA_enlargedY` instantiated at the consumer pin
`t = 1/4`, at the DISCHARGED data bridge
(`HomSpineDataBridge.stepTwoDataBridge_of_holder_pinned`, so is not an input
here), at the shifted Hölder constant and at `K_h^∞ = 0` — the last choice is
what makes the right-hand bracket the PRINTED `energyBracket σ_m 3^{m/2} K_g
K_h^∞ K_h` with no slack at all. -/
theorem htop_seamEnlargedY (d : ℕ) [NeZero d] (hd1 : 1 ≤ d) :
    ∃ Cstep : ℝ, 0 < Cstep ∧
      ∀ (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
        {u h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
        {Kg Kh KhInf alpha : ℝ} {X : Cutoff.CutoffSample d → ℕ∞} {k : ℕ},
        m ≤ L → X omega = ((k : ℕ) : ℕ∞) →
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        fluxCorrectedError M L m (1 / 4 / 2) omega =
          fluxCorrectedErrorRepresentative M L m ⟨1 / 4 / 2, half_pos seamQuarterPos⟩
            omega →
        fluxCorrectedError M L m (1 / 4) omega =
          fluxCorrectedErrorRepresentative M L m ⟨1 / 4, seamQuarterPos⟩ omega →
        fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4 / 2, half_pos seamQuarterPos⟩
            omega ≠ ⊤ →
        fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4, seamQuarterPos⟩ omega ≠ ⊤ →
        fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤ →
        0 ≤ Kg → 0 ≤ Kh → 0 ≤ KhInf →
          (3 : ℝ) ^ ((1 - alpha) * (k : ℝ)) *
              (regularityDataBracket M m u ((Annealed.sigmaBar M m : ℝ)) Kg
                (seamShiftedKh m Kh KhInf)).toReal ≤
            recutEnergyFactor M
                (seamEnlargedY M m (seamTopScaleConst d Cstep)
                  (homMinimalScaleFactor (1 - alpha) X)) m omega *
              energyBracket ((Annealed.sigmaBar M m : ℝ)) (Real.rpow 3 ((m : ℝ) / 2)) Kg
                KhInf Kh := by
  obtain ⟨Cstep, hCstep, hmain⟩ := htop_of_stepTwoA_enlargedY d
  refine ⟨Cstep, hCstep, ?_⟩
  intro M L m omega u h g Kg Kh KhInf alpha X k hL hXk hsol hKgB hKhB hsupB hrep1 hrep2
    hfin1 hfin2 hfinE hKg0 hKh0 hKhInf0
  have hKh'0 : (0 : ℝ) ≤ seamShiftedKh m Kh KhInf := seamShiftedKh_nonneg hKh0 hKhInf0
  have hbridge : StepTwoDataBridge m (1 / 4) g h.grad (stepTwoDataConstPinned d) Kg 0
      (seamShiftedKh m Kh KhInf) := by
    obtain ⟨hb1, hb2⟩ := stepTwoDataBridge_of_holder_pinned (t := 1 / 4) seamQuarterPos
      le_rfl hKg0 hKh0 hKhInf0 hKgB hKhB hsupB
    refine ⟨hb1, ?_⟩
    rw [show (0 : ℝ) + Real.rpow 3 ((m : ℝ) / 2) * seamShiftedKh m Kh KhInf =
        KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh from by
      rw [zero_add, three_rpow_mul_seamShiftedKh]]
    exact hb2
  have hgB : ForceBesovRegularity (originCube d m) (1 / 4) (fun x => -g x) :=
    forceBesovRegularity_neg_of_holderHalf hd1 seamQuarterPos (by norm_num) hKg0 hKgB
  have hhB : ForceBesovRegularity (originCube d m) (1 / 4) h.grad :=
    forceBesovRegularity_of_holderHalf hd1 seamQuarterPos (by norm_num) hKh0 hKhB
  have hkey := hmain M L m omega (u := u) (hdat := h) (g := g) seamQuarterPos
    (Cdata := stepTwoDataConstPinned d) (Kg := Kg) (Kh := seamShiftedKh m Kh KhInf)
    (KhInf := 0) (alpha := alpha) (X := k) hL (by norm_num) hsol hgB hhB hbridge hrep1
    hrep2 hfin1 hfin2 hfinE (stepTwoDataConstPinned_nonneg d) hKg0 hKh'0 le_rfl
  rw [energyBracket_zero_seamShiftedKh] at hkey
  have hYval : seamEnlargedY M m (seamTopScaleConst d Cstep)
        (homMinimalScaleFactor (1 - alpha) X) omega =
      ENNReal.ofReal
          ((Cstep * (Real.rpow (1 / 4 : ℝ) (-(3 / 2 : ℝ)) +
                Real.rpow (1 / 4 : ℝ) (-(1 / 2 : ℝ))) *
              Real.sqrt (2 * (d : ℝ)) * stepTwoDataConstPinned d + 1) *
            (3 : ℝ) ^ ((1 - alpha) * (k : ℝ))) *
        stepTwoEnlargedY M m seamQuarterPos omega := by
    rw [seamEnlargedY_apply_of_eq_coe M m (seamTopScaleConst_nonneg d hCstep.le) omega hXk,
      seamTopScaleConst_eq]
  simp only [recutEnergyFactor] at hkey ⊢
  rw [hYval]
  exact hkey

/-! ## 7. THE THREE ENERGY CONJUNCTS, PRODUCED -/

/-- **`{0 ≤ S, the partial-sum slot, hSbound}` OF THE SEAM RESIDUE, PRODUCED.**

The first three conjuncts of the seam's energy residue at its own
enlarged `Y`, from the Theorem-C display alone.  The partial-sum slot is
delivered at the PRINTED coefficient `ã_{L,m}`: by
`HomSeamFluxCoefficient.printedLocalEnergy_fluxCorrected` the energy functional
is the SAME function of cubes at `ã_{L,m}` and at `a_L`, so no estimate is
spent on the swap.

Two hypotheses are visible here that the residue statement does NOT bind
(module docstring, mismatches (1) and (2)): the classical-gradient binder
`hgrad` of the theorem, and the finiteness `X ω = k` of the minimal scale.  The
`C_en⁰` slot produced is `recutEnergySlotConst Creg (homAlpha M) (4d) (homS M)
(homK M)` — it names `Creg` and the model, and its `coarseGrainingGeomFactor
(4d) (homS M / 4)` factor is's D3. -/
theorem seamEnergySlot_of_regularityDisplayAt (d : ℕ) [NeZero d] (hd1 : 1 ≤ d) :
    ∃ Cstep : ℝ, 0 < Cstep ∧
      ∀ (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
        {X : Cutoff.CutoffSample d → ℕ∞} {k : ℕ} {Creg : ℝ},
        0 < Creg → 4 ≤ |Real.log M.gamma| → X omega = ((k : ℕ) : ℕ∞) →
        RegularityDisplayAt M Creg (homAlpha M) m X omega →
        ∀ (L : ℤ), m ≤ L →
          ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
            (Kg Kh KhInf : ℝ),
            IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) u h g →
            HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
            HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
            (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
            HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
            fluxCorrectedError M L m (1 / 4 / 2) omega =
              fluxCorrectedErrorRepresentative M L m ⟨1 / 4 / 2, half_pos seamQuarterPos⟩
                omega →
            fluxCorrectedError M L m (1 / 4) omega =
              fluxCorrectedErrorRepresentative M L m ⟨1 / 4, seamQuarterPos⟩ omega →
            fluxCorrectedTwoScaleErrorObservableSup M m m
                ⟨1 / 4 / 2, half_pos seamQuarterPos⟩ omega ≠ ⊤ →
            fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4, seamQuarterPos⟩ omega ≠
              ⊤ →
            fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤ →
            ∃ S : ℝ,
              0 ≤ S ∧
              (∀ N : ℕ,
                coarseGrainingEnergyPartial (originCube d m)
                    (recutExponent d hd1).exponent.toReal (homS M - homS M / 4) (homK M) N
                    (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega)
                      u) ≤
                  S) ∧
              S ≤ recutEnergySlotConst Creg (homAlpha M)
                    (recutExponent d hd1).exponent.toReal (homS M) (homK M) *
                  recutEnergyFactor M
                    (seamEnlargedY M m (seamTopScaleConst d Cstep)
                      (homMinimalScaleFactor (1 - homAlpha M) X)) m omega *
                  energyBracket ((Annealed.sigmaBar M m : ℝ)) (Real.rpow 3 ((m : ℝ) / 2))
                    Kg KhInf Kh := by
  obtain ⟨Cstep, hCstep, htop⟩ := htop_seamEnlargedY d hd1
  refine ⟨Cstep, hCstep, ?_⟩
  intro M m omega X k Creg hCreg hlog hXk hdisp L hL u h g Kg Kh KhInf hsol hKgB hKhB
    hsupB hgrad hrep1 hrep2 hfin1 hfin2 hfinE
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : (0 : ℝ) ≤ Kg := hKgB.nonneg hx0 hy0 hne
  have hKh0 : (0 : ℝ) ≤ Kh := hKhB.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hsupB (cubeCenter (originCube d m)) hcen)
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]
    linarith only [hdR]
  have halpha1 : homAlpha M ≤ 1 := by rw [homAlpha]; linarith only [hs]
  have halpha : 1 - homAlpha M = homS M / 2 := by rw [homAlpha]; ring
  have hdispE := regularityEnergyDisplay_of_regularityDisplayAt M hdisp hXk hL hKh0
    hKhInf0 hsol hKgB hKhB hsupB hgrad
  have hT : regularityDataBracket M m u ((Annealed.sigmaBar M m : ℝ)) Kg
      (seamShiftedKh m Kh KhInf) ≠ ⊤ :=
    regularityDataBracket_ne_top M u hKg0 (seamShiftedKh_nonneg hKh0 hKhInf0)
  have hhtop := htop M L m omega (alpha := homAlpha M) hL hXk hsol hKgB hKhB hsupB hrep1
    hrep2 hfin1 hfin2 hfinE hKg0 hKh0 hKhInf0
  obtain ⟨S, hS0, hSpart, hSb⟩ :=
    energySlot_of_regularityDisplay hdispE hT halpha1 hCreg.le halpha hp hs L omega
      (homK M) hhtop
  refine ⟨S, hS0, ?_, hSb⟩
  intro N
  rw [show (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) =
      printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u from
    funext fun R => printedLocalEnergy_fluxCorrected M L m omega u R]
  exact hSpart N

end

end Algsuperdiff.Section4.Provider.Homogenization
