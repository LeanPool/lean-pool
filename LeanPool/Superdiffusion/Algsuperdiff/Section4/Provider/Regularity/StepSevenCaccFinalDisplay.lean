/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccGradient

/-!
# StepSevenCaccFinalDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The two derived scalars, named -/

/-- **The Caccioppoli's output constant at the §4.4 pin**, `Ccacc = √P`. -/
def stepSevenCaccConst (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d) : ℝ :=
  Real.sqrt (caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT)

theorem stepSevenCaccConst_nonneg (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d) :
    0 ≤ stepSevenCaccConst C Q a := Real.sqrt_nonneg _

/-- **The Caccioppoli's own data leg at the §4.4 pin**, `dataM`. -/
def stepSevenCaccDataM [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (g : Vec d → Vec d) : ℝ :=
  Real.sqrt (stepSevenCaccForcingFactor * (Ch02.lambdaS Q stepSevenCaccT a)⁻¹) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q stepOneS g

theorem stepSevenCaccDataM_nonneg [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (hg : ForceBesovRegularity Q stepOneS g) :
    0 ≤ stepSevenCaccDataM Q a g :=
  mul_nonneg (Real.sqrt_nonneg _)
    (cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q stepOneS g
      hg.partialSeminorms_bddAbove)

/-! ## 2. `e.gradient.with.shom` with `hvol` and `hcacc` discharged -/

/-- **`e.gradient.with.shom` on the interior branch, with `hvol` and `hcacc`
discharged.**

```text
  ν^{1/2}‖∇u‖_{L²(U_{n+1})}
    ≤ (3^{3d+1/4}·Ccacc·(Cosc√Clam+1)) · √σ · 3^{(3/4)(1-α)(m-n)} · oscHi
      + (3^{3d+1/4}·Ccacc·(Cosc√Clam+1)) · 3^{(3/4)(1-α)(m-n)}
          · ( √σ · dataOsc + dataM ) ,
```

at the carriers of the module docstring.  The surviving analytic inputs are
`hlambda` (row 2 of the derived-slot table, discharged in the `_of_caps` sibling
below) and `hosc`
(`e.oscillation.Holder.bound`). -/
theorem exists_stepSevenGradientWithShom_interior (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} {C1 alpha delta : ℝ} {B : ℕ}
        {Cosc Clam oscHi dataOsc shomNp : ℝ},
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        z ∈ openCubeSet (originCube d (m - 1)) → n' ≤ m - 1 → n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ Clam → 0 ≤ oscHi → 0 ≤ dataOsc →
        Ch02.lambdaS (originCube d n') stepSevenCaccT
            (Support.fluxCorrectedCoeffFamily M L mf Qf
              (Cutoff.translateCutoffSample z omega)) ≤ Clam * shomNp →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => u.toFun x -
                volumeAverage (truncatedWindow z m n') u.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * dataOsc) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt Clam + 1)) * Real.sqrt shomNp *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscHi +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt Clam + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt shomNp * dataOsc +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCaccHcacc_interior d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n n' Qf z omega u v g C1 alpha delta B Cosc Clam oscHi dataOsc shomNp
    hval hgrad hz hn' hcore heq hforce hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    hCosc hClam hoscHi hdataOsc hlambda hosc
  have hzm : z ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega) hz
  have hvol := stepSevenNuGradNorm_le_volumeRatio d (nu := (M.nu : ℝ)) (n' := n')
    (le_of_lt M.nu_pos) hzm hnm hcore u
  have hcacc := hC M L mf m n' Qf omega u v
    (volumeAverage (truncatedWindow z m n') u.toFun) hval hgrad hz hn' heq hforce
  have hmain := stepSevenGradientWithShom (d := d) (C1 := C1) (alpha := alpha)
    (delta := delta) (B := B) (n := n) (m := m) (n' := n')
    (Ccacc := stepSevenCaccConst C (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)))
    (Cosc := Cosc) (Clam := Clam)
    (gradLoc := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad)
    (gradCore := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n' - 2)) u.grad)
    (oscLo := (3 : ℝ) ^ (-n') *
      normalizedL2On (truncatedWindow z m n')
        (fun x => u.toFun x - volumeAverage (truncatedWindow z m n') u.toFun))
    (oscHi := oscHi) (dataOsc := dataOsc)
    (dataM := stepSevenCaccDataM (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)) g)
    (lamLo := Ch02.lambdaS (originCube d n') stepSevenCaccT
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)))
    (shomNp := shomNp)
    hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    (stepSevenCaccConst_nonneg _ _ _) hCosc hClam
    (stepSevenNuGradNorm_nonneg _ _ _)
    (mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (normalizedL2On_nonneg _ _))
    hoscHi hdataOsc (stepSevenCaccDataM_nonneg _ _ hforce) hvol hcacc hlambda hosc
  exact hmain

/-- **`e.gradient.with.shom` on the interior branch, with `hvol`, `hcacc` AND
`hlambda` discharged.**

`hlambda` is row 2 of the derived-slot table
(`StepSevenLambdaSlots.stepSevenLambdaS_lower_le_of_caps`) at the parent cube
`□_{n'+1}`: from the clause-(B) record there, `λ_{1/8,1}(□_{n'}) ≤
(256/63)··σ`.  The only surviving analytic input is `hosc`. -/
theorem exists_stepSevenGradientWithShom_interior_of_caps (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} {C1 alpha delta : ℝ} {B : ℕ}
        {Cosc CB sigma oscHi dataOsc : ℝ},
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        z ∈ openCubeSet (originCube d (m - 1)) → n' ≤ m - 1 → n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CB → 0 ≤ oscHi → 0 ≤ dataOsc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigma CB →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => u.toFun x -
                volumeAverage (truncatedWindow z m n') u.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * dataOsc) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) u.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt (256 / 63 * CB) + 1)) * Real.sqrt sigma *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscHi +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                stepSevenCaccConst C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega)) *
                (Cosc * Real.sqrt (256 / 63 * CB) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt sigma * dataOsc +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenGradientWithShom_interior d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n n' Qf z omega u v g C1 alpha delta B Cosc CB sigma oscHi dataOsc
    hval hgrad hz hn' hcore heq hforce hC1 halpha0 halpha1 hnm hdelta hgap hbudget
    hCosc hCB hoscHi hdataOsc hcaps hosc
  have hrow2 := stepSevenLambdaS_lower_le_of_caps (k := n' + 1) _ hcaps
  rw [show n' + 1 - 1 = n' by ring] at hrow2
  have hClam : (0 : ℝ) ≤ 256 / 63 * CB := by linarith only [hCB]
  exact hC M L mf m n n' Qf omega u v hval hgrad hz hn' hcore heq hforce hC1 halpha0
    halpha1 hnm hdelta hgap hbudget hCosc hClam hoscHi hdataOsc hrow2 hosc

end

end Algsuperdiff.Section4.Provider.Regularity
