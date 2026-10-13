/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsPrincipal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationBackgroundClass

/-!
# SplitObligationsBackground

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Obligation (2) of `SplitScaleObligations`, reduced to two cell-energy moments

ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`, the
background display.

## What this module supplies

`Closure.SplitProducerFold.SplitScaleObligations`'s second conjunct, per
mesoscopic cell:

```
  omega |->  mu( a_omega; P_z + bfF_z )     is integrable under  cutoffSampleLaw M .
```

`doubledMuValue U a F` is the normalized average over `U` of the pointwise
doubled energy density `(1/2) F(x) . bfA(x) F(x)`.  Two unconditional facts
about that average are proved here:

* `doubledMuValue_le_plainUpperBound` --- the density is a.e. below the plain
  elliptic upper bound of its carrier, and *that* bound is integrable as soon as
  the two legs of `F` are vector-`L^2` on `U`, so
  `MeasureTheory.integral_mono_of_nonneg` gives

```
  mu( a; F )  <=  (1/2)(Lam + 2 lam^{-1} Lam^2) fint_U |F_pot|^2
                     +  lam^{-1} fint_U |F_flux|^2 .
```

At the genuine cutoff cell `lam = M.nu` and `Lam =
Cutoff.coefficientCutoffCubeEllipticityUpper M (n+h) omega R`, whose every
finite moment is proved.  Combining, obligation (2) reduces to **exactly two**
sample moments of the background's own normalized cell energies:

* the *second* moment of the potential leg's cell energy (it multiplies
  `Lam^2`), and
* the *first* moment of the flux leg's cell energy (it multiplies the
  deterministic `M.nu^{-1}`).

`integrable_doubledMuValue_meshCellBackground_of_cellMoments` is that
reduction.  The measurability half is the proved
`LocalizationFluctuationBackgroundClass.measurable_doubledMuValue_meshCellBackground`,
and the two typing properties are the proved
`memVectorL2_meshCellBackground_{potential,flux}`.

**What is not proved here.**  The two moment binders themselves.

## Binders

Beyond the typing binders: `[NeZero d]`, the two `MeasurableSpace`/`BorelSpace`
pairs on the doubled `L^2` carriers, the geometric membership of the cell in the
mesh below the localization cube, the two weak-solution properties of `e.def.w`,
and the two named cell-energy moments.  No smallness, no ellipticity gate and no
selection occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`, the
  background display, `e.CG.bounds.2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Block
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The doubled energy value of a fixed field -/

/-- **The doubled energy of any field is nonnegative.**  The pointwise density is
a.e. nonnegative by `CoeffOn.aeElliptic` and CoarseGraining's pointwise
coercivity, and the normalized average of an a.e. nonnegative function is
nonnegative even when the function is not known to be integrable.
Unconditional. -/
theorem doubledMuValue_nonneg (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    0 ≤ doubledMuValue U a F := by
  have hden : 0 ≤ ∫ x, blockEnergyDensityAt a (F.eval x) x
      ∂(volumeMeasureOn (U : Set (Vec d))) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [a.aeElliptic] with x hx
    have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix hx (F.eval x)
    have hself : (0 : ℝ) ≤ blockVecDot (F.eval x) (F.eval x) := by
      have h1 : (0 : ℝ) ≤ vecNormSq (F.eval x).1 := vecNormSq_nonneg _
      have h2 : (0 : ℝ) ≤ vecNormSq (F.eval x).2 := vecNormSq_nonneg _
      show (0 : ℝ) ≤ vecDot (F.eval x).1 (F.eval x).1 + vecDot (F.eval x).2 (F.eval x).2
      exact add_nonneg h1 h2
    have hc : (0 : ℝ) ≤ a.lam / (1 + 2 * a.Lam ^ 2) := by
      have hden : (0 : ℝ) < 1 + 2 * a.Lam ^ 2 := by positivity
      exact div_nonneg a.lam_pos.le hden.le
    show (0 : ℝ) ≤ (1 / 2 : ℝ) * blockVecDot (F.eval x)
      (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (F.eval x))
    nlinarith [mul_nonneg hc hself]
  show (0 : ℝ) ≤ (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
    ∫ x, blockEnergyDensityAt a (F.eval x) x ∂(volumeMeasureOn (U : Set (Vec d)))
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hden

/-- **The doubled energy of a vector-`L^2` field is below the plain elliptic
upper bound of its carrier.**

The pointwise density is bounded a.e. by CoarseGraining's
`blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix`, whose right
side is integrable because both legs are vector-`L^2`; the value itself is not
assumed integrable, `MeasureTheory.integral_mono_of_nonneg` needing only a.e.
nonnegativity on the left.

only on the two `L^2` typing properties. -/
theorem doubledMuValue_le_plainUpperBound (U : Domain d) (a : CoeffOn U)
    (F : DoubledField d)
    (hpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) F.flux) :
    doubledMuValue U a F ≤
      (1 / 2 : ℝ) * (a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) *
          average U (fun x => vecNormSq (F.potential x)) +
        a.lam⁻¹ * average U (fun x => vecNormSq (F.flux x)) := by
  classical
  have hpotInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (F.potential x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hpot hpot
  have hfluxInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (F.flux x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hflux hflux
  have hgInt : MeasureTheory.Integrable
      (fun x => (1 / 2 : ℝ) * ((a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq (F.potential x) +
        2 * a.lam⁻¹ * vecNormSq (F.flux x))) (volumeMeasureOn (U : Set (Vec d))) :=
    ((hpotInt.const_mul _).add (hfluxInt.const_mul _)).const_mul _
  have hnn : (0 : Vec d → ℝ) ≤ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => blockEnergyDensityAt a (F.eval x) x := by
    filter_upwards [a.aeElliptic] with x hx
    have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix hx (F.eval x)
    have hself : (0 : ℝ) ≤ blockVecDot (F.eval x) (F.eval x) := by
      have h1 : (0 : ℝ) ≤ vecNormSq (F.eval x).1 := vecNormSq_nonneg _
      have h2 : (0 : ℝ) ≤ vecNormSq (F.eval x).2 := vecNormSq_nonneg _
      show (0 : ℝ) ≤ vecDot (F.eval x).1 (F.eval x).1 + vecDot (F.eval x).2 (F.eval x).2
      exact add_nonneg h1 h2
    have hc : (0 : ℝ) ≤ a.lam / (1 + 2 * a.Lam ^ 2) := by
      have hden : (0 : ℝ) < 1 + 2 * a.Lam ^ 2 := by positivity
      exact div_nonneg a.lam_pos.le hden.le
    show (0 : ℝ) ≤ (1 / 2 : ℝ) * blockVecDot (F.eval x)
      (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (F.eval x))
    nlinarith [mul_nonneg hc hself]
  have hle : (fun x => blockEnergyDensityAt a (F.eval x) x) ≤ᵐ[volumeMeasureOn
      (U : Set (Vec d))] fun x =>
        (1 / 2 : ℝ) * ((a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq (F.potential x) +
          2 * a.lam⁻¹ * vecNormSq (F.flux x)) := by
    filter_upwards [a.aeElliptic] with x hx
    have hup := blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix hx
      (F.potential x) (F.flux x)
    show (1 / 2 : ℝ) * blockVecDot (F.potential x, F.flux x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
          (F.potential x, F.flux x)) ≤ _
    linarith
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn hgInt hle
  have haverage : average U
      (fun x => (1 / 2 : ℝ) * ((a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq (F.potential x) +
        2 * a.lam⁻¹ * vecNormSq (F.flux x)))
      = (1 / 2 : ℝ) * (a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) *
          average U (fun x => vecNormSq (F.potential x)) +
        a.lam⁻¹ * average U (fun x => vecNormSq (F.flux x)) := by
    unfold Ch02.average
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hpotInt.const_mul _) (hfluxInt.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  have hstep : doubledMuValue U a F ≤ average U
      (fun x => (1 / 2 : ℝ) * ((a.Lam + 2 * a.lam⁻¹ * a.Lam ^ 2) * vecNormSq (F.potential x) +
        2 * a.lam⁻¹ * vecNormSq (F.flux x))) := by
    show (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x, blockEnergyDensityAt a (F.eval x) x ∂(volumeMeasureOn (U : Set (Vec d))) ≤
      (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ * _
    exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 ENNReal.toReal_nonneg)
  rw [haverage] at hstep
  exact hstep

/-! ## The two named cell energies of the Step-2 background -/

/-- The normalized cell energy of the background's potential leg. -/
def meshCellBackgroundPotentialEnergy (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  average (cubeDomain R)
    fun x => vecNormSq ((meshCellBackground M n h Kc e e' wD wN R omega).potential x)

/-- The normalized cell energy of the background's flux leg. -/
def meshCellBackgroundFluxEnergy (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  average (cubeDomain R)
    fun x => vecNormSq ((meshCellBackground M n h Kc e e' wD wN R omega).flux x)

theorem meshCellBackgroundPotentialEnergy_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    0 ≤ meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega := by
  refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)

theorem meshCellBackgroundFluxEnergy_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    0 ≤ meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega := by
  refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)

/-! ## The two cell energies in closed form

The two moment binders below are therefore *exactly* second- and first-moment
statements about the normalized cell energies of the two corrector legs of
`e.def.w`, up to the fixed gauge factors `shom^{-1}` and `shom`. -/

/-- The potential leg's cell energy is `shom^{-1}` times the normalized cell
energy of `e' + grad w_D`.  Unconditional. -/
theorem meshCellBackgroundPotentialEnergy_eq (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega =
      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        Ch02.average (cubeDomain R)
          (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x)) := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hpt : (fun x =>
      vecNormSq ((meshCellBackground M n h Kc e e' wD wN R omega).potential x)) =
      fun x => ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        vecNormSq (e' + (wD omega.val).toH1Function.grad x) := by
    funext x
    simp only [meshCellBackground_potential]
    show vecNormSq ((Real.sqrt ((Annealed.sigmaBar M n : ℝ)))⁻¹ •
      (e' + (wD omega.val).toH1Function.grad x)) = _
    rw [vecNormSq_smul, inv_pow, Real.sq_sqrt hsig.le]
  show Ch02.average (cubeDomain R) _ = _
  rw [hpt]
  exact average_const_mul (cubeDomain R) _ _

/-- The flux leg's cell energy is `shom` times the normalized cell energy of
`e + (grad w_N + shom^{-1} h e')`.  Unconditional. -/
theorem meshCellBackgroundFluxEnergy_eq (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega =
      ((Annealed.sigmaBar M n : ℝ)) *
        Ch02.average (cubeDomain R)
          (fun x => vecNormSq (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
            (n + (h : ℤ)) e' (wN omega.val) x)) := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hpt : (fun x =>
      vecNormSq ((meshCellBackground M n h Kc e e' wD wN R omega).flux x)) =
      fun x => ((Annealed.sigmaBar M n : ℝ)) *
        vecNormSq (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
          (n + (h : ℤ)) e' (wN omega.val) x) := by
    funext x
    simp only [meshCellBackground_flux]
    show vecNormSq (Real.sqrt ((Annealed.sigmaBar M n : ℝ)) •
      (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
        (wN omega.val) x)) = _
    rw [vecNormSq_smul, Real.sq_sqrt hsig.le]
  show Ch02.average (cubeDomain R) _ = _
  rw [hpt]
  exact average_const_mul (cubeDomain R) _ _

/-! ## Obligation (2), reduced -/

/-- **Obligation (2) of `SplitScaleObligations` at one cell, from two cell-energy
moments.**

No estimate of the manuscript is used, and no competitor is selected. -/
theorem integrable_doubledMuValue_meshCellBackground_of_cellMoments [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d Kc)) (wD omega)
        (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
          (n + (h : ℤ)) e x))
    (hwN : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d Kc)) (wN omega)
        (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
          (n + (h : ℤ)) e' x))
    {jd : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) jd)
    [MeasurableSpace (HilbertBlockL2 (openCubeSet (originCube d Kc)))]
    [BorelSpace (HilbertBlockL2 (openCubeSet (originCube d Kc)))]
    [MeasurableSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    (hpotSq : Integrable
      (fun omega : CutoffSample d =>
        meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure)
    (hfluxOne : Integrable
      (fun omega : CutoffSample d =>
        meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega)
      (cutoffSampleLaw M).toMeasure) :
    Integrable
      (fun omega : CutoffSample d =>
        doubledMuValue (cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega))
      (cutoffSampleLaw M).toMeasure := by
  classical
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  set Lam : CutoffSample d → ℝ := fun omega =>
    coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R with hLamdef
  set Epot : CutoffSample d → ℝ := fun omega =>
    meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega with hEpotdef
  set Eflux : CutoffSample d → ℝ := fun omega =>
    meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega with hEfluxdef
  have hLamMeas : Measurable Lam :=
    measurable_coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) R
  have hLam0 : ∀ omega, 0 ≤ Lam omega := fun omega =>
    coefficientCutoffCubeEllipticityUpper_nonneg M (n + (h : ℤ)) omega R
  have hEpot0 : ∀ omega, 0 ≤ Epot omega := fun omega =>
    meshCellBackgroundPotentialEnergy_nonneg M n h Kc e e' wD wN R omega
  -- the potential leg's own strong measurability, recovered from its square
  have hEpotMeas : AEStronglyMeasurable Epot (cutoffSampleLaw M).toMeasure := by
    have hsq : AEStronglyMeasurable (fun omega : CutoffSample d => Epot omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure := hpotSq.aestronglyMeasurable
    have hroot := (Real.continuous_sqrt.comp_aestronglyMeasurable hsq)
    refine hroot.congr (Filter.Eventually.of_forall fun omega => ?_)
    have h := Real.sqrt_sq (hEpot0 omega)
    simpa using h
  have hEpotInt : Integrable Epot (cutoffSampleLaw M).toMeasure := by
    refine Integrable.mono' ((integrable_const ((1 : ℝ) / 2)).add
      (hpotSq.const_mul ((1 : ℝ) / 2))) hEpotMeas
      (Filter.Eventually.of_forall fun omega => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (hEpot0 omega)]
    nlinarith [sq_nonneg (Epot omega - 1)]
  have hLam2 : Integrable (fun omega : CutoffSample d => Lam omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure :=
    integrable_coefficientCutoffCubeEllipticityUpper_pow M (n + (h : ℤ)) R 2
  have hLam4 : Integrable (fun omega : CutoffSample d => Lam omega ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure :=
    integrable_coefficientCutoffCubeEllipticityUpper_pow M (n + (h : ℤ)) R 4
  have hLamE : Integrable (fun omega : CutoffSample d => Lam omega * Epot omega)
      (cutoffSampleLaw M).toMeasure :=
    integrable_mul_of_sq_integrable hLam0 hEpot0
      (hLamMeas.aestronglyMeasurable.mul hEpotMeas) hLam2 hpotSq
  have hLam2E : Integrable
      (fun omega : CutoffSample d => Lam omega ^ (2 : ℕ) * Epot omega)
      (cutoffSampleLaw M).toMeasure := by
    have hsq : (fun omega : CutoffSample d => (Lam omega ^ (2 : ℕ)) ^ (2 : ℕ)) =
        fun omega : CutoffSample d => Lam omega ^ (4 : ℕ) := by
      funext omega
      rw [← pow_mul]
    refine integrable_mul_of_sq_integrable (fun omega => by positivity) hEpot0
      ((hLamMeas.pow_const 2).aestronglyMeasurable.mul hEpotMeas) ?_ hpotSq
    rw [hsq]
    exact hLam4
  have hgint : Integrable (fun omega : CutoffSample d =>
      (1 / 2 : ℝ) * (Lam omega * Epot omega) +
        M.nu⁻¹ * (Lam omega ^ (2 : ℕ) * Epot omega) + M.nu⁻¹ * Eflux omega)
      (cutoffSampleLaw M).toMeasure :=
    ((hLamE.const_mul _).add (hLam2E.const_mul _)).add (hfluxOne.const_mul _)
  refine Integrable.mono' hgint
    (measurable_doubledMuValue_meshCellBackground M n h Kc e e' wD wN hwD hwN
      hR).aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
  have hnonneg := doubledMuValue_nonneg (cubeDomain R)
    (meshCellCoeff M (n + (h : ℤ)) R omega)
    (meshCellBackground M n h Kc e e' wD wN R omega)
  have hbound := doubledMuValue_le_plainUpperBound (cubeDomain R)
    (meshCellCoeff M (n + (h : ℤ)) R omega)
    (meshCellBackground M n h Kc e e' wD wN R omega)
    (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR omega)
    (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR omega)
  rw [Real.norm_of_nonneg hnonneg]
  refine hbound.trans ?_
  have hEp : average (cubeDomain R)
      (fun x => vecNormSq
        ((meshCellBackground M n h Kc e e' wD wN R omega).potential x)) = Epot omega := rfl
  have hEf : average (cubeDomain R)
      (fun x => vecNormSq
        ((meshCellBackground M n h Kc e e' wD wN R omega).flux x)) = Eflux omega := rfl
  have hlam : (meshCellCoeff M (n + (h : ℤ)) R omega).lam = M.nu := rfl
  have hLamEq : (meshCellCoeff M (n + (h : ℤ)) R omega).Lam = Lam omega := rfl
  rw [hEp, hEf, hlam, hLamEq]
  have hE0 := hEpot0 omega
  have hL0 := hLam0 omega
  nlinarith [hE0, hL0]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
