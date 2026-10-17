/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMuMeasCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSelectEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseGoodEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.AveragedBlock

/-!
# LocalizationFluctuationMuMeasCell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three integrability producers of the `gamma^{10}` endpoint

ABK26, `l.approximate.recurrence.formula`, Steps 1--2, read at the recurrence
pair `(n, n+h)`.

`integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add`
carries exactly three analytic binders --- `hintLHS`, `hintPrincipal`,
`hintFluctuation`.  This module supplies them.

* **`hintLHS`** is discharged *unconditionally*
  (`integrable_blockVecDot_coarseBlockMatrix_cutoffSampleLaw`): the load is the
  constant `recurrenceP`, so the integrand is a fixed quadratic form in the
  coarse block matrix, and the entrywise integrability of that matrix under the
  genuine cutoff law is the proved moment layer
  (`Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix`)
  transported along the pushforward `coefficientCutoffLaw = coefficientCutoff_*
  cutoffSampleLaw`.

* **`hintPrincipal`** is reduced to one almost-sure upper bound on the switch
  energy (`integrable_switchCubeEnergy_of_le`): its measurability half is the
  proved `PrincipalResponseGoodEnergy.aestronglyMeasurable_switchCubeEnergy` at
  a measurable load family, and its lower half is the unconditional
  nonnegativity of the coarse quadratic form.  The upper bound itself is the
  Step-3 good-event/bad-event budget and is **not** proved here; it is an
  explicit binder.

* **`hintFluctuation`** is reduced to a *fixed-competitor* statement
  (`integrable_meshFluctuationCellIntegrand`).  The cell integrand is
  `2 mu_field - P_z . bfA P_z`, and `mu_field` is squeezed between `0` and the
  energy of the background field `P_z + bfF_z` itself
  (`LocalizationFluctuationMuMeasCore.{doubledMuField_nonneg,
  doubledMuField_le_self}`), while its measurability is the countable-competitor
  identity of the same module.  What remains is therefore: measurability of the
  fixed-competitor energies, and integrability of the one background energy.
  **No measurable selection of a minimizer occurs anywhere.**

## References

* ABK26, `l.approximate.recurrence.formula`, `e.lower.bound.basic.split`, Step
  2, the switch display.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The coarse block matrix of the genuine cutoff, read on the sample -/

private theorem toFullBlockMat_eq_blockMatEntry (A : BlockMat d) (alpha beta : BlockCoord d) :
    toFullBlockMat A alpha beta = blockMatEntry A alpha beta := by
  cases alpha <;> cases beta <;> rfl

/-- **Every entry of the cell's coarse block matrix is sample-integrable.** The
proved entrywise integrability under the genuine coefficient-cutoff law,
transported to the sample carrier `CutoffSample d` along the pushforward.
Unconditional. -/
theorem integrable_blockMatEntry_switchCubeMatrix [NeZero d] (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (alpha beta : BlockCoord d) :
    Integrable
      (fun omega : CutoffSample d => blockMatEntry (switchCubeMatrix M m R omega) alpha beta)
      (cutoffSampleLaw M).toMeasure := by
  have hlaw : Integrable
      (fun a : RegCoeffField d =>
        blockMatEntry (HCPolySupport.coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
      (Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure) := by
    rw [← coefficientCutoffLaw_eq_map M m]
    exact Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
      M m R alpha beta
  have hcomp := (integrable_map_measure hlaw.aestronglyMeasurable
    (measurable_coefficientCutoff M.nu m).aemeasurable).1 hlaw
  refine hcomp.congr (Filter.Eventually.of_forall fun omega => ?_)
  exact congrArg (fun A => blockMatEntry A alpha beta)
    (coarseBlockMatrix_cubeSet_coefficientCutoff_eq M m omega R)

/-- **The `hintLHS` producer.**  For a *constant* doubled load the coarse
quadratic form of the cutoff cell matrix is sample-integrable.  Unconditional.

This is verbatim the `hintLHS` binder of
`integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add` once the
cube is `originCube d Kc` and the load is
`recurrenceP (Annealed.sigmaBar M n) e e'`. -/
theorem integrable_blockVecDot_coarseBlockMatrix_cutoffSampleLaw (M : ABKModel d) (m : ℤ)
    (Q : TriadicCube d) (X : BlockVec d) :
    Integrable
      (fun omega : CutoffSample d =>
        blockVecDot X
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q)) X))
      (cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hEq : (fun omega : CutoffSample d =>
        blockVecDot X
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q)) X)) =
      fun omega : CutoffSample d => ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
        blockMatEntry (switchCubeMatrix M m Q omega) alpha beta *
          (toFullBlockVec X alpha * toFullBlockVec X beta) := by
    funext omega
    change blockVecDot X (blockMatVecMul (switchCubeMatrix M m Q omega) X) = _
    rw [Provider.Block.blockVecDot_blockMatVecMul_eq_sum (switchCubeMatrix M m Q omega) X]
    refine Finset.sum_congr rfl fun alpha _ => Finset.sum_congr rfl fun beta _ => ?_
    rw [toFullBlockMat_eq_blockMatEntry]
    ring
  rw [hEq]
  exact integrable_finsetSum _ fun alpha _ =>
    integrable_finsetSum _ fun beta _ =>
      (integrable_blockMatEntry_switchCubeMatrix M m Q alpha beta).mul_const _

/-- The `hintLHS` binder of the endpoint, at its own carriers.  Unconditional. -/
theorem integrable_recurrenceP_coarseBlockMatrix (M : ABKModel d) (n Kc : ℤ) (h : ℕ)
    (e e' : Vec d) :
    Integrable
      (fun omega : CutoffSample d =>
        blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d Kc))
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                (originCube d Kc)))
            (recurrenceP (Annealed.sigmaBar M n) e e')))
      (cutoffSampleLaw M).toMeasure :=
  integrable_blockVecDot_coarseBlockMatrix_cutoffSampleLaw M (n + (h : ℤ)) (originCube d Kc)
    (recurrenceP (Annealed.sigmaBar M n) e e')

/-! ## The `hintPrincipal` producer -/

/-- The switch energy is nonnegative: the coarse doubled quadratic form of an
elliptic coefficient is a nonnegative quadratic form.  Unconditional. -/
theorem switchCubeEnergy_nonneg (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (X : BlockVec d)
    (omega : CutoffSample d) : 0 ≤ switchCubeEnergy M m R X omega :=
  blockVecDot_coarseBlockMatrix_nonneg _ _ _

/-- **The `hintPrincipal` producer.**  The switch energy at a measurable load
family is sample-integrable as soon as it admits an almost-sure integrable
upper bound; the lower bound is the unconditional nonnegativity of the coarse
doubled quadratic form.

exactly on `hX` (measurability of the load family, a regularity property of the
caller's corrector data, not a proof step) and on the a.s. domination `hle`,
which is the Step-3 budget and is not proved here. -/
theorem integrable_switchCubeEnergy_of_le (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    {X : CutoffSample d → BlockVec d} (hX : Measurable X)
    {g : CutoffSample d → ℝ} (hg : Integrable g (cutoffSampleLaw M).toMeasure)
    (hle : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      switchCubeEnergy M m R (X omega) omega ≤ g omega) :
    Integrable (fun omega : CutoffSample d => switchCubeEnergy M m R (X omega) omega)
      (cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  refine Integrable.mono' hg (aestronglyMeasurable_switchCubeEnergy M m R hX) ?_
  filter_upwards [hle] with omega hom
  rw [Real.norm_eq_abs, abs_of_nonneg (switchCubeEnergy_nonneg M m R (X omega) omega)]
  exact hom

/-! ## The cell carriers of the `hintFluctuation` producer

Three abbreviations for the sample-dependent data the Step-2 cell integrand is
built from.  Each is a plain unfolding of the endpoint's own expression; the
`rfl` lemmas below record that. -/

/-- The cell's coefficient along the sample, `bfA_m(z + cu_n)`. -/
def meshCellCoeff (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (omega : CutoffSample d) :
    CoeffOn (Ch02.cubeDomain R) :=
  (coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R

/-- The cell's principal load along the sample, `P_z` of `e.Pz.def`. -/
def meshCellLoad (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : BlockVec d :=
  principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
    (wD omega.val) (wN omega.val)

/-- The cell's background doubled field along the sample, `P_z + bfF_z`.  It is
the slope datum of the field-slope variational problem whose minimum is the
fluctuation number, and it is itself an admissible competitor. -/
def meshCellBackground (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : DoubledField d :=
  constantDoubledField (meshCellLoad M n h Kc e e' wD wN R omega) +
    localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
      (wD omega.val) (wN omega.val)

/-- **The cell integrand is twice the field-slope minimum minus the switch
energy.**  Definitional. -/
theorem meshFluctuationCellIntegrand_eq (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega =
      2 * doubledMuField (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega) -
        switchCubeEnergy M (n + (h : ℤ)) R (meshCellLoad M n h Kc e e' wD wN R omega) omega :=
  rfl

/-! ## The `hintFluctuation` producer -/

/-- **The `hintFluctuation` producer, at one cell.**

The Step-2 cell integrand is sample-integrable once

* the background field `P_z + bfF_z` is vector-`L^2` on the cell for every
  sample (`hpot`, `hflux`) --- a typing property of the corrector data;
* every *fixed-competitor* energy `mu(a_omega; P_z + bfF_z + D_k)` is
  sample-measurable (`hcomp`), `D` being the canonical countable competitor
  family of `LocalizationFluctuationMuMeasCore`;
* the *one* background energy `mu(a_omega; P_z + bfF_z)` is sample-integrable
  (`hbg`); and
* the switch energy at `P_z` is sample-integrable (`hprin`), which is the
  endpoint's own `hintPrincipal`.

No estimate on the fluctuation is used, and **no minimizer is selected**: the
variational minimum enters only through the two unconditional bounds
`0 <= mu_field <= mu(background)` and through the countable-infimum identity. -/
theorem integrable_meshFluctuationCellIntegrand (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d)
    (hpot : ∀ omega : CutoffSample d,
      MemVectorL2 ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).potential)
    (hflux : ∀ omega : CutoffSample d,
      MemVectorL2 ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).flux)
    (hcomp : ∀ k : ℕ, AEMeasurable
      (fun omega : CutoffSample d =>
        doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega +
            doubledMuFieldCompetitor (Ch02.cubeDomain R) k))
      (cutoffSampleLaw M).toMeasure)
    (hbg : Integrable
      (fun omega : CutoffSample d =>
        doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega))
      (cutoffSampleLaw M).toMeasure)
    (hprin : Integrable
      (fun omega : CutoffSample d =>
        switchCubeEnergy M (n + (h : ℤ)) R (meshCellLoad M n h Kc e e' wD wN R omega) omega)
      (cutoffSampleLaw M).toMeasure) :
    Integrable
      (fun omega : CutoffSample d => meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega)
      (cutoffSampleLaw M).toMeasure := by
  have hmu : Integrable
      (fun omega : CutoffSample d =>
        doubledMuField (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega))
      (cutoffSampleLaw M).toMeasure :=
    integrable_doubledMuField (Ch02.cubeDomain R)
      (fun omega => meshCellCoeff M (n + (h : ℤ)) R omega)
      (fun omega => meshCellBackground M n h Kc e e' wD wN R omega) hpot hflux hcomp hbg
  have hEq : (fun omega : CutoffSample d =>
        meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega) =
      fun omega : CutoffSample d =>
        2 * doubledMuField (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
            (meshCellBackground M n h Kc e e' wD wN R omega) -
          switchCubeEnergy M (n + (h : ℤ)) R
            (meshCellLoad M n h Kc e e' wD wN R omega) omega := by
    funext omega
    exact meshFluctuationCellIntegrand_eq M n h Kc e e' wD wN R omega
  rw [hEq]
  exact (hmu.const_mul 2).sub hprin

/-- **The `hintFluctuation` producer at one cell, in the choice-free form.**
The fixed-competitor hypothesis quantifies over *every* test field on the cell,
so the canonical (choice-named) competitor family occurs in no hypothesis. -/
theorem integrable_meshFluctuationCellIntegrand' (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d)
    (hpot : ∀ omega : CutoffSample d,
      MemVectorL2 ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).potential)
    (hflux : ∀ omega : CutoffSample d,
      MemVectorL2 ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).flux)
    (hcomp : ∀ Y : DoubledField d, IsDoubledTestField (Ch02.cubeDomain R) Y → AEMeasurable
      (fun omega : CutoffSample d =>
        doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega + Y))
      (cutoffSampleLaw M).toMeasure)
    (hbg : Integrable
      (fun omega : CutoffSample d =>
        doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega))
      (cutoffSampleLaw M).toMeasure)
    (hprin : Integrable
      (fun omega : CutoffSample d =>
        switchCubeEnergy M (n + (h : ℤ)) R (meshCellLoad M n h Kc e e' wD wN R omega) omega)
      (cutoffSampleLaw M).toMeasure) :
    Integrable
      (fun omega : CutoffSample d => meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega)
      (cutoffSampleLaw M).toMeasure :=
  integrable_meshFluctuationCellIntegrand M n h Kc e e' wD wN R hpot hflux
    (fun k => hcomp _ (isDoubledTestField_doubledMuFieldCompetitor (Ch02.cubeDomain R) k)) hbg hprin

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
