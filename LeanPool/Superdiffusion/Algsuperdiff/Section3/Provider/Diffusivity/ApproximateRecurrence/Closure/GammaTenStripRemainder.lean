/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripLambdaGrowth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorCellInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureInteriorSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureTerminalStrip
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorHosc
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripPathwise
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripCellSquare

/-!
# GammaTenStripRemainder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary-strip residual of the interior route, assembled

ABK26, Step 2 of `l.approximate.recurrence.formula`, target
`e.lower.bound.localization.terms`.

## What this module is

`Closure.ClosureInteriorSplit.ClosureStripRemainder d` is the second of the two
conditional A obligations of the interior route.  Written out, it asks: at
**every** model, window, gap and pair of directions --- with no regime, no
direction normalization and no gap positivity --- for all large localization
cubes there is a bound `Cstrip` on the full-mesh average of the *squared* cell
expectations of the Step-2 integrand, which the signed Cauchy--Schwarz gate
`sqrt(d 3^{g-p}) sqrt(Cstrip) <= cgamma^{10}/2` absorbs.

This module assembles it from two pathwise inputs and the polynomial rate of
`Closure.GammaTenStripLambdaGrowth`.  The assembly is where the two competing
rates are compared: the strip constant grows **polynomially** in the
localization scale `K` (degree eight, through the ellipticity moment), while the
mesh depth `p = closureMeshDepth M n h K` grows **linearly**, so the gate's
`3^{g-p}` decays geometrically.  `eventually_poly_le_geometric` closes it.

## What is proved

* `cubeFamilyAverage_integral_sq_stripCellPotentialDatum_le_of_majorant` and its
  flux mirror --- the two grid binders `hpot`, `hflux` of
  `Closure.GammaTenStripBound.gammaTenStrip_cell_average_sq_le`, produced from a
  **pathwise** majorant `G` of the shifted fourth energy on the localization
  cube rather than from an integrability statement about that fourth energy
  itself.  The route is `Closure.GammaTenStripEnergy`'s pathwise fold
  `cubeFamilyAverage_sq_cubeAverage_vecNormSq_le_originCubeFourthEnergy`
  composed with
  `LocalizationFluctuationGridEighth.cubeFamilyAverage_integral_le_of_pointwise`.
* `closureStripRemainder_of_majorant` --- `ClosureStripRemainder d` from the two
  inputs, with the gate discharged `∀ᶠ K`.
* `closureStripRemainder_proved` and `diffusivity_asymptotics_proved` --- the
  two endpoints of this module: `ClosureStripRemainder d` and the frozen
  statement's conclusion, each from `(d : ℕ) [NeZero d] (hd : 2 ≤ d)` alone;
  every other input above is discharged internally.

## Binders

`closureStripRemainder_of_majorant` carries `hd : 2 <= d` and the two `Prop`
binders `hmaj` (the pathwise fourth-energy majorant with a localization-scale
free expectation bound) and `hsqD`/`hsqF` (the sample second moments of the two
cell data).  It carries **no** regime, **no** `inductionState`, **no**
`cgamma` smallness and **no** normalization of `e`, `e'`; the obligation it
proves has none either.

## Scope

Internal Provider infrastructure.  The intermediate declarations are a
conditional A route for `Closure.ClosureInteriorSplit.ClosureStripRemainder`;
the two endpoints `closureStripRemainder_proved` and
`diffusivity_asymptotics_proved` carry no conditional binder beyond `(d: ℕ)
[NeZero d] (2 ≤ d)`.  There is no `sorry`, no `admit`, no custom axiom and no
`set_option maxHeartbeats`.

## The scale gate on `m0` (-bin statement change)

`diffusivity_asymptotics_proved` gates `m0` at `mStarStar M < m0`, **not** at
the printed `m0 in (mstar, infty) cap Z`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Set
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open Algsuperdiff.Frozen.Assumptions
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two grid binders from a pathwise majorant -/

/-- **`hpot` from a pathwise majorant of the shifted fourth energy.**

on the cell second moments `hDsq`, on the sample integrability of the majorant
`G` and on its pathwise domination `hGD`.  No measurability of the fourth
energy itself is used. -/
theorem cubeFamilyAverage_integral_sq_stripCellPotentialDatum_le_of_majorant
    [NeZero d] (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (j : ℕ)
    (e e' : Vec d)
    (hDsq : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    {G : CutoffSample d → ℝ}
    (hGint : Integrable G (cutoffSampleLaw M).toMeasure)
    (hGD : ∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
      (fun x => e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x) ≤
        G omega) :
    cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
        (fun R => ∫ omega, stripCellPotentialDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤
      4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
        ∫ omega, G omega ∂(cutoffSampleLaw M).toMeasure := by
  classical
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hjle : (K : ℤ) - (j : ℤ) ≤ (K : ℤ) := by omega
  have hconst : (0 : ℝ) ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) := by positivity
  have hmem8 : ∀ omega : CutoffSample d,
      MemLp (fun x => e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    (memLp_const e').add (memLp_eight_grad_closureDirichletAlong hd M n h K e omega.val)
  have hle : ∀ omega : CutoffSample d,
      cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
          (fun R => stripCellPotentialDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ)) ≤
        4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) * G omega := by
    intro omega
    have hcell : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)),
        stripCellPotentialDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ) ≤
          4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
            cubeAverage R (fun x => vecNormSq
              (e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)) ^
              (2 : ℕ) := by
      intro R hR
      have hRd : R ∈ descendantsAtDepth (originCube d (K : ℤ))
          ((K : ℤ) - ((K : ℤ) - (j : ℤ))).toNat := by
        rwa [mesoCubeGrid_eq_descendantsAtDepth hjle] at hR
      have hg2 : MemLp
          (fun x => (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
        (memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hRd
          (memLp_eight_grad_closureDirichletAlong hd M n h K e omega.val)).mono_exponent
          (by norm_num)
      have hD0 : (0 : ℝ) ≤ stripCellPotentialDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega :=
        stripCellPotentialDatum_nonneg _ _ _ _ _ _ _ _ _ _
      have hbd := stripCellPotentialDatum_le_two_mul_energy M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega hg2
      have hEeq := meshCellBackgroundPotentialEnergy_eq_cubeAverage M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega
      have hsq := pow_le_pow_left₀ hD0 hbd 2
      rw [hEeq] at hsq
      calc stripCellPotentialDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ)
          ≤ (2 * (((Annealed.sigmaBar M n : ℝ))⁻¹ *
              cubeAverage R (fun x => vecNormSq
                (e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)))) ^
              (2 : ℕ) := hsq
        _ = 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
              cubeAverage R (fun x => vecNormSq
                (e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)) ^
                (2 : ℕ) := by ring
    calc cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
          (fun R => stripCellPotentialDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ))
        ≤ cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
            (fun R => 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
              cubeAverage R (fun x => vecNormSq
                (e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)) ^
                (2 : ℕ)) := cubeFamilyAverage_mono hcell
      _ = 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
            cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
              (fun R => cubeAverage R (fun x => vecNormSq
                (e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)) ^
                (2 : ℕ)) := cubeFamilyAverage_const_mul _ _ _
      _ ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) *
            originCubeFourthEnergy (K : ℤ)
              (fun x => e' +
                (closureDirichletAlong M n h K e omega.val).toH1Function.grad x) := by
          refine mul_le_mul_of_nonneg_left ?_ hconst
          exact cubeFamilyAverage_sq_cubeAverage_vecNormSq_le_originCubeFourthEnergy hjle
            _ (hmem8 omega)
      _ ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) * G omega :=
          mul_le_mul_of_nonneg_left (hGD omega) hconst
  have hmain := cubeFamilyAverage_integral_le_of_pointwise (cutoffSampleLaw M).toMeasure
    (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
    (fun R omega => stripCellPotentialDatum M n h (K : ℤ) e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
    (fun omega => 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) * G omega)
    hDsq (hGint.const_mul _) hle
  rwa [integral_const_mul] at hmain

/-- **`hflux` from a pathwise majorant of the shifted fourth energy.**

exactly as its potential mirror. -/
theorem cubeFamilyAverage_integral_sq_stripCellFluxDatum_le_of_majorant
    [NeZero d] (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (j : ℕ)
    (e e' : Vec d)
    (hFsq : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    {G : CutoffSample d → ℝ}
    (hGint : Integrable G (cutoffSampleLaw M).toMeasure)
    (hGN : ∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
      (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
        (closureNeumannAlong M n h K e' omega.val) x) ≤ G omega) :
    cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
        (fun R => ∫ omega, stripCellFluxDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤
      4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
        ∫ omega, G omega ∂(cutoffSampleLaw M).toMeasure := by
  classical
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hjle : (K : ℤ) - (j : ℤ) ≤ (K : ℤ) := by omega
  have hconst : (0 : ℝ) ≤ 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) := by positivity
  have hmem8 : ∀ omega : CutoffSample d,
      MemLp (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
        (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x)
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    (memLp_const e).add (memLp_eight_neumannFluxField_closure hd M n h K e' omega.val)
  have hle : ∀ omega : CutoffSample d,
      cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
          (fun R => stripCellFluxDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ)) ≤
        4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) * G omega := by
    intro omega
    have hcell : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)),
        stripCellFluxDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ) ≤
          4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
            cubeAverage R (fun x => vecNormSq
              (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
                (closureNeumannAlong M n h K e' omega.val) x)) ^ (2 : ℕ) := by
      intro R hR
      have hRd : R ∈ descendantsAtDepth (originCube d (K : ℤ))
          ((K : ℤ) - ((K : ℤ) - (j : ℤ))).toNat := by
        rwa [mesoCubeGrid_eq_descendantsAtDepth hjle] at hR
      have hg2 : MemLp
          (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
            (closureNeumannAlong M n h K e' omega.val))
          (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
        (memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hRd
          (memLp_eight_neumannFluxField_closure hd M n h K e' omega.val)).mono_exponent
          (by norm_num)
      have hD0 : (0 : ℝ) ≤ stripCellFluxDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega :=
        stripCellFluxDatum_nonneg _ _ _ _ _ _ _ _ _ _
      have hbd := stripCellFluxDatum_le_two_mul_energy M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega hg2
      have hEeq := meshCellBackgroundFluxEnergy_eq_cubeAverage M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega
      have hsq := pow_le_pow_left₀ hD0 hbd 2
      rw [hEeq] at hsq
      calc stripCellFluxDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ)
          ≤ (2 * (((Annealed.sigmaBar M n : ℝ)) *
              cubeAverage R (fun x => vecNormSq
                (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
                  (closureNeumannAlong M n h K e' omega.val) x)))) ^ (2 : ℕ) := hsq
        _ = 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
              cubeAverage R (fun x => vecNormSq
                (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
                  (closureNeumannAlong M n h K e' omega.val) x)) ^ (2 : ℕ) := by ring
    calc cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
          (fun R => stripCellFluxDatum M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
            R omega ^ (2 : ℕ))
        ≤ cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
            (fun R => 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
              cubeAverage R (fun x => vecNormSq
                (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
                  (closureNeumannAlong M n h K e' omega.val) x)) ^ (2 : ℕ)) :=
          cubeFamilyAverage_mono hcell
      _ = 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
            cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
              (fun R => cubeAverage R (fun x => vecNormSq
                (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
                  (closureNeumannAlong M n h K e' omega.val) x)) ^ (2 : ℕ)) :=
          cubeFamilyAverage_const_mul _ _ _
      _ ≤ 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) *
            originCubeFourthEnergy (K : ℤ)
              (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
                (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x) := by
          refine mul_le_mul_of_nonneg_left ?_ hconst
          exact cubeFamilyAverage_sq_cubeAverage_vecNormSq_le_originCubeFourthEnergy hjle
            _ (hmem8 omega)
      _ ≤ 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) * G omega :=
          mul_le_mul_of_nonneg_left (hGN omega) hconst
  have hmain := cubeFamilyAverage_integral_le_of_pointwise (cutoffSampleLaw M).toMeasure
    (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)))
    (fun R omega => stripCellFluxDatum M n h (K : ℤ) e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
    (fun omega => 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) * G omega)
    hFsq (hGint.const_mul _) hle
  rwa [integral_const_mul] at hmain

/-! ## The obligation -/

/-- **`Closure.ClosureInteriorSplit.ClosureStripRemainder d` from the pathwise
majorant and the two cell second moments.**

The strip constant is `Closure.GammaTenStripBound.gammaTenStripConst` at the two
grid moments produced above.  Its only localization-scale dependence is the
ellipticity moment, which `Closure.GammaTenStripLambdaGrowth` bounds by a
degree-eight polynomial in `K`; the gate's `3^{g-p}` decays geometrically in `K`
because `p = closureMeshDepth M n h K` is eventually `K - recurrenceMesoScale`.
`eventually_poly_le_geometric` compares the two rates.

on `hd`, `hmaj`, `hsqD`, `hsqF` and nothing else: no regime, no
`inductionState`, no `cgamma` smallness, no normalization of `e`, `e'` and no
positivity of `h`. -/
theorem closureStripRemainder_of_majorant (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hmaj : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (e e' : Vec d),
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ K : ℕ, n + (h : ℤ) ≤ (K : ℤ) →
          ∃ G : CutoffSample d → ℝ,
            (∀ omega, 0 ≤ G omega) ∧
            Integrable G (cutoffSampleLaw M).toMeasure ∧
            (∫ omega, G omega ∂(cutoffSampleLaw M).toMeasure ≤ B) ∧
            (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
                (fun x => e' +
                  (closureDirichletAlong M n h K e omega.val).toH1Function.grad x) ≤
                  G omega) ∧
            (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
                (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
                  (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x) ≤
                  G omega))
    (hsqD : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d) (jd : ℕ)
        (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd →
        ∀ G : CutoffSample d → ℝ, (∀ omega, 0 ≤ G omega) →
          Integrable G (cutoffSampleLaw M).toMeasure →
          (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
            (fun x => e' +
              (closureDirichletAlong M n h K e omega.val).toH1Function.grad x) ≤ G omega) →
          Integrable (fun omega : CutoffSample d =>
            stripCellPotentialDatum M n h (K : ℤ) e e'
              (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
              R omega ^ (2 : ℕ)) (cutoffSampleLaw M).toMeasure)
    (hsqF : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d) (jd : ℕ)
        (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd →
        ∀ G : CutoffSample d → ℝ, (∀ omega, 0 ≤ G omega) →
          Integrable G (cutoffSampleLaw M).toMeasure →
          (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
            (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
              (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x) ≤ G omega) →
          Integrable (fun omega : CutoffSample d =>
            stripCellFluxDatum M n h (K : ℤ) e e'
              (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
              R omega ^ (2 : ℕ)) (cutoffSampleLaw M).toMeasure) :
    ClosureStripRemainder d := by
  classical
  intro M n h e e'
  obtain ⟨B, hB0, hmajK⟩ := hmaj M n h e e'
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  set Cpot : ℝ := 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ (2 : ℕ) * B with hCpotDef
  set Cflux : ℝ := 4 * ((Annealed.sigmaBar M n : ℝ)) ^ (2 : ℕ) * B with hCfluxDef
  have hCpot0 : (0 : ℝ) ≤ Cpot := by rw [hCpotDef]; positivity
  have hCflux0 : (0 : ℝ) ≤ Cflux := by rw [hCfluxDef]; positivity
  set s : ℤ := recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ)
    with hsDef
  set L : ℝ := stripLambdaGrowthConst M * stripControlBase M (n + (h : ℤ)) ^ 8 with hLDef
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hLDef]
    exact mul_nonneg (stripLambdaGrowthConst_nonneg M)
      (pow_nonneg (stripControlBase_nonneg M (n + (h : ℤ))) 8)
  set A : ℝ := 2 * L * Cpot + 8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux with hADef
  have hA0 : (0 : ℝ) ≤ A := by rw [hADef]; positivity
  set A' : ℝ := (d : ℝ) * (3 : ℝ) ^ (closureStripGap M) * (3 : ℝ) ^ s * A with hA'Def
  have hc : (0 : ℝ) < M.gamma ^ (20 : ℕ) / 4 := by positivity
  filter_upwards [Filter.eventually_ge_atTop ((n + (h : ℤ)).toNat),
    eventually_closureMeshDepth_scale M n h,
    eventually_poly_le_geometric A' hc] with K hK1 hK2 hK3
  have hnhK : n + (h : ℤ) ≤ (K : ℤ) := by
    have hself := Int.self_le_toNat (n + (h : ℤ))
    have hcast : ((n + (h : ℤ)).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK1
    omega
  set p : ℕ := closureMeshDepth M n h K with hpDef
  have hscale : (K : ℤ) - (p : ℤ) = s := hK2
  obtain ⟨G, hG0, hGint, hGB, hGD, hGN⟩ := hmajK K hnhK
  have hjle : (K : ℤ) - (p : ℤ) ≤ (K : ℤ) := by omega
  have hmesh : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (p : ℤ)),
      R ∈ descendantsAtDepth (originCube d (K : ℤ))
        ((K : ℤ) - ((K : ℤ) - (p : ℤ))).toNat := by
    intro R hR
    rwa [mesoCubeGrid_eq_descendantsAtDepth hjle] at hR
  have hDsq : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (p : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega ^ (2 : ℕ)) (cutoffSampleLaw M).toMeasure := fun R hR =>
    hsqD M n h K e e' _ R (hmesh R hR) G hG0 hGint hGD
  have hFsq : ∀ R ∈ mesoCubeGrid d (K : ℤ) ((K : ℤ) - (p : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega ^ (2 : ℕ)) (cutoffSampleLaw M).toMeasure := fun R hR =>
    hsqF M n h K e e' _ R (hmesh R hR) G hG0 hGint hGN
  have hpot : cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (p : ℤ)))
      (fun R => ∫ omega, stripCellPotentialDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega ^ (2 : ℕ) ∂(cutoffSampleLaw M).toMeasure) ≤ Cpot := by
    refine le_trans (cubeFamilyAverage_integral_sq_stripCellPotentialDatum_le_of_majorant
      hd M n h K p e e' hDsq hGint hGD) ?_
    rw [hCpotDef]
    exact mul_le_mul_of_nonneg_left hGB (by positivity)
  have hflux : cubeFamilyAverage (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (p : ℤ)))
      (fun R => ∫ omega, stripCellFluxDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega ^ (2 : ℕ) ∂(cutoffSampleLaw M).toMeasure) ≤ Cflux := by
    refine le_trans (cubeFamilyAverage_integral_sq_stripCellFluxDatum_le_of_majorant
      hd M n h K p e e' hFsq hGint hGN) ?_
    rw [hCfluxDef]
    exact mul_le_mul_of_nonneg_left hGB (by positivity)
  refine ⟨gammaTenStripConst M n h (K : ℤ) Cpot Cflux, ?_, ?_⟩
  · exact gammaTenStrip_cell_average_sq_le M n h (K : ℤ) p e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
      hDsq hFsq hpot hflux
  · -- the gate
    have hK1R : (1 : ℝ) ≤ (1 + (K : ℝ)) ^ 8 := by
      have : (1 : ℝ) ≤ 1 + (K : ℝ) := by
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        linarith
      exact one_le_pow₀ this
    have hlam : stripLambdaMoment M (n + (h : ℤ)) (originCube d (K : ℤ)) ≤
        L * (1 + (K : ℝ)) ^ 8 := by
      have hbase := stripLambdaMoment_originCube_le M (n + (h : ℤ)) K
      have heq : stripLambdaGrowthConst M *
          (stripControlBase M (n + (h : ℤ)) * (1 + (K : ℝ))) ^ 8 =
            L * (1 + (K : ℝ)) ^ 8 := by
        rw [hLDef]
        ring
      rwa [heq] at hbase
    have hCstrip : gammaTenStripConst M n h (K : ℤ) Cpot Cflux ≤ A * (1 + (K : ℝ)) ^ 8 := by
      have h1 : 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d (K : ℤ)) * Cpot ≤
          2 * (L * (1 + (K : ℝ)) ^ 8) * Cpot :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlam (by norm_num : (0 : ℝ) ≤ 2)) hCpot0
      have h4 : (0 : ℝ) ≤ 8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux := by positivity
      have h3 : 8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux ≤
          8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux * (1 + (K : ℝ)) ^ 8 :=
        le_mul_of_one_le_right h4 hK1R
      have hfin : 2 * (L * (1 + (K : ℝ)) ^ 8) * Cpot +
          8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux * (1 + (K : ℝ)) ^ 8 = A * (1 + (K : ℝ)) ^ 8 := by
        rw [hADef]
        ring
      calc gammaTenStripConst M n h (K : ℤ) Cpot Cflux
          = 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d (K : ℤ)) * Cpot +
              8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux := rfl
        _ ≤ 2 * (L * (1 + (K : ℝ)) ^ 8) * Cpot +
              8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux * (1 + (K : ℝ)) ^ 8 := add_le_add h1 h3
        _ = A * (1 + (K : ℝ)) ^ 8 := hfin
    -- the geometric side
    have hTpos : (0 : ℝ) < (3 : ℝ) ^ (K : ℕ) := by positivity
    have hspos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
    have hppos : (0 : ℝ) < (3 : ℝ) ^ p := by positivity
    have h3p : (3 : ℝ) ^ (K : ℕ) = (3 : ℝ) ^ p * (3 : ℝ) ^ s := by
      have hz : ((K : ℤ)) = ((p : ℤ)) + s := by omega
      calc (3 : ℝ) ^ (K : ℕ) = (3 : ℝ) ^ ((K : ℕ) : ℤ) := (zpow_natCast (3 : ℝ) K).symm
        _ = (3 : ℝ) ^ (((p : ℕ) : ℤ) + s) := by rw [hz]
        _ = (3 : ℝ) ^ ((p : ℕ) : ℤ) * (3 : ℝ) ^ s :=
            zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ _
        _ = (3 : ℝ) ^ p * (3 : ℝ) ^ s := by rw [zpow_natCast]
    have hXnn : (0 : ℝ) ≤ (d : ℝ) *
        ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) := by positivity
    have hkey : (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
        gammaTenStripConst M n h (K : ℤ) Cpot Cflux ≤ (M.gamma ^ (10 : ℕ) / 2) ^ 2 := by
      have hstep1 : (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
          gammaTenStripConst M n h (K : ℤ) Cpot Cflux ≤
          (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
            (A * (1 + (K : ℝ)) ^ 8) := mul_le_mul_of_nonneg_left hCstrip hXnn
      have hident : (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
          (A * (1 + (K : ℝ)) ^ 8) = (A' * (1 + (K : ℝ)) ^ 8) / (3 : ℝ) ^ (K : ℕ) := by
        rw [hA'Def, h3p]
        field_simp
      have hstep2 : (A' * (1 + (K : ℝ)) ^ 8) / (3 : ℝ) ^ (K : ℕ) ≤
          M.gamma ^ (20 : ℕ) / 4 := by
        rw [div_le_iff₀ hTpos]
        exact hK3
      have hsq : (M.gamma ^ (10 : ℕ) / 2) ^ 2 = M.gamma ^ (20 : ℕ) / 4 := by ring
      rw [hsq]
      calc (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
            gammaTenStripConst M n h (K : ℤ) Cpot Cflux
          ≤ (d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
              (A * (1 + (K : ℝ)) ^ 8) := hstep1
        _ = (A' * (1 + (K : ℝ)) ^ 8) / (3 : ℝ) ^ (K : ℕ) := hident
        _ ≤ M.gamma ^ (20 : ℕ) / 4 := hstep2
    have hg0 : (0 : ℝ) ≤ M.gamma ^ (10 : ℕ) / 2 := by positivity
    rw [← Real.sqrt_mul hXnn]
    calc Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ p) *
          gammaTenStripConst M n h (K : ℤ) Cpot Cflux)
        ≤ Real.sqrt ((M.gamma ^ (10 : ℕ) / 2) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = M.gamma ^ (10 : ℕ) / 2 := Real.sqrt_sq hg0

/-! ## The obligation, unconditionally -/

/-- **`Closure.ClosureInteriorSplit.ClosureStripRemainder d`.**

The two `Prop` binders of `closureStripRemainder_of_majorant` are discharged by
`Closure.GammaTenStripPathwise.exists_strip_fourthEnergy_majorant` and by the
two cell second moments of `Closure.GammaTenStripCellSquare`.  Only `d`,
`[NeZero d]` and `hd : 2 <= d` survive. -/
theorem closureStripRemainder_proved (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ClosureStripRemainder d :=
  closureStripRemainder_of_majorant d hd
    (fun M n h e e' => exists_strip_fourthEnergy_majorant d hd M n h e e')
    (fun M n h K e e' _jd _R hR _G hG0 hGint hGD =>
      integrable_stripCellPotentialDatum_sq_closure d hd M n h K e e' hR hG0 hGint hGD)
    (fun M n h K e e' _jd _R hR _G hG0 hGint hGN =>
      integrable_stripCellFluxDatum_sq_closure d hd M n h K e e' hR hG0 hGint hGN)

/-- **The diffusivity asymptotics.**

The proof consumes the two produced obligations of
`Closure.ClosureInteriorSplit`: the interior-mesh Besov envelope
(`Closure.GammaTenInteriorHosc.closureInteriorBesovEnvelopeInput_proved`) and
the boundary-strip residual (`closureStripRemainder_proved`).

Binder note: the frozen statement's binder list is `(d : ℕ)` alone; this
composition additionally carries `[NeZero d]` and `hd : 2 <= d`, which come from
`Closure.ClosureTerminalStrip.diffusivity_asymptotics_of_strip` and are not
derivable from `d : ℕ`. -/
theorem diffusivity_asymptotics_proved (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2) :=
  diffusivity_asymptotics_of_strip d hd (closureInteriorBesovEnvelopeInput_proved d hd)
    (closureStripRemainder_proved d hd)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
