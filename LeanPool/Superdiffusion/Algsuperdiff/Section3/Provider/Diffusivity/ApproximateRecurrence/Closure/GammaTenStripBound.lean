/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripCell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripMoment

/-!
# GammaTenStripBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `hstrip` binder, at the crude elliptic majorant

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.basic.split`, `e.CG.bounds.2`.

## What this module is

`cubeFamilyAverage_sq_integral_meshFluctuationCellIntegrand_le_of_majorant`
reduced the `hstrip` binder of
`Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`
to two statements about the **nonnegative** crude elliptic majorant

```
  maj_R  =  (Lam_R + 2 nu^{-1} Lam_R^2) . D_R  +  2 nu^{-1} . F_R ,
```

namely its sample integrability at each cell and the bound

```
  avsum_{R in 3^{n} Zd cap cu_{Kc}} ( E[ maj_R ] )^2  <=  Cstrip .
```

Here `D_R` and `F_R` are the two named **cell data** of the majorant, defined
below: the Step-2 background's potential (resp. flux) cell energy plus the
squared length of the matching leg of the cell's principal load `P_z`.  This
module discharges both statements from the **second grid moments** of `D` and
`F` alone, with the coefficient leg paid by the cell-uniform ellipticity moment
of `Closure.GammaTenStripMoment`.

## The estimate, in one line

Cauchy--Schwarz in the sample separates the coefficient from the cell datum:

```
  E[ maj_R ]  <=  E[ W . D_R ] + 2 nu^{-1} E[ F_R ]
              <=  sqrt(E[W^2]) sqrt(E[D_R^2])  +  2 nu^{-1} sqrt(E[F_R^2]) ,
```

`W` being the cell-uniform ellipticity weight of `Closure.GammaTenStripMoment`
(which dominates `Lam_R + 2 nu^{-1} Lam_R^2` at **every** cell of the mesh at
once), and then `(x+y)^2 <= 2x^2 + 2y^2` and the grid average give

```
  Cstrip  =  2 . stripLambdaMoment M (n+h) (cu_{Kc}) . Cpot  +  8 nu^{-2} . Cflux .
```

Nothing else enters: no Besov envelope, no minimizer, no interior restriction,
no oscillation cell, no gauge and no smallness gate.

## What is proved

* `stripCellPotentialDatum`, `stripCellFluxDatum`, their nonnegativity, and
  `stripCellMajorant_eq_data` --- the majorant read at the two data
  (definitional).
* `stripCellMajorant_le_weight_mul_data` --- the cell-uniform pointwise
  majorization, conditional only on the geometric containment of the cell in the
  localization cube.
* `integrable_stripCellMajorant_of_data_sq` --- the sample integrability of the
  majorant at one cell, from the two cell data's second moments.  No
  measurability of the corrector data is assumed: both data inherit their
  a.e.-strong measurability from their own square's integrability.
* `cubeFamilyAverage_sq_integral_stripCellMajorant_le` --- the grid bound at the
  majorant.
* `gammaTenStripConst` and `gammaTenStrip_cell_average_sq_le` --- **the `hstrip`
  binder itself**, in the exact shape
  `Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`
  consumes, at the explicit constant above.

## Binders, and what is left

`gammaTenStrip_cell_average_sq_le` is on exactly four hypotheses, all of them
moment statements about the two cell data of the majorant on the full mesh:

* `hDsq`, `hFsq` --- per cell, the sample integrability of `D_R^2`, `F_R^2`;
* `hpot`, `hflux` --- the grid averages of those second moments, below `Cpot`
  and `Cflux`.

Nothing else is assumed: no smallness gate, no induction state, no Besov datum,
no measurable selection and no interior-mesh restriction occurs, and neither the
integrability nor the measurability of the Step-2 cell integrand itself is used.

The two grid binders are **not** discharged here.  Their intended route is the
exact tiling identity
`LocalizationGrid.cubeAverage_originCube_eq_mesoGridAverage` composed with the
per-cell Jensen step and the annealed fourth energy of `e.nablaw.in.L.eight`
(`LocalizationEnvelopeSpatial.originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le`
together with `LocalizationEnvelopeMoment`'s `Gamma_1` second moment); none of
that is invoked below and no declaration here asserts it.

## The size of `Cstrip`

`stripLambdaMoment M (n+h) (cu_{Kc})` is the second sample moment of the
ellipticity weight at the canonical origin cover of the **localization cube**,
and therefore depends on `Kc`: see the scale discussion in
`Closure.GammaTenStripMoment`.  No `Kc`-independence is claimed here, and the
consumer's absorption gate `hgate` is stated at whatever `Cstrip` it is given.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.Pz.def`, `e.Fz.def`, `e.CG.bounds.2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Block
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two Cauchy--Schwarz steps in the sample -/

private theorem holderConjTwoTwo : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

private theorem ofRealTwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

/-- **Cauchy--Schwarz in the sample.**  For two nonnegative `L^2` observables the
mean of the product is below the product of the roots of the second moments.

on `hf`, `hg` (nonnegativity) and the two `L^2` memberships. -/
private theorem integral_mul_le_sqrt_mul_sqrt {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {f g : Omega → ℝ} (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfm : MemLp f 2 mu) (hgm : MemLp g 2 mu) :
    ∫ w, f w * g w ∂mu ≤
      Real.sqrt (∫ w, f w ^ (2 : ℕ) ∂mu) * Real.sqrt (∫ w, g w ^ (2 : ℕ) ∂mu) := by
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by rwa [ofRealTwo]
  have hg2 : MemLp g (ENNReal.ofReal (2 : ℝ)) mu := by rwa [ofRealTwo]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg holderConjTwoTwo
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hg) hf2 hg2
  have hptf : ∀ w : Omega, f w ^ (2 : ℝ) = f w ^ (2 : ℕ) := fun w => by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hptg : ∀ w : Omega, g w ^ (2 : ℝ) = g w ^ (2 : ℕ) := fun w => by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hptf, hptg] at hh
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [one_div] using hh

/-- **Cauchy--Schwarz against the constant `1`.**  On a probability space the
mean of a nonnegative `L^2` observable is below the root of its second moment.

on `hf` and the `L^2` membership. -/
private theorem integral_le_sqrt_integral_sq_prob {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {f : Omega → ℝ} (hf : ∀ w, 0 ≤ f w)
    (hfm : MemLp f 2 mu) :
    ∫ w, f w ∂mu ≤ Real.sqrt (∫ w, f w ^ (2 : ℕ) ∂mu) := by
  have hone : MemLp (fun _ : Omega => (1 : ℝ)) 2 mu := memLp_const 1
  have hcs := integral_mul_le_sqrt_mul_sqrt mu hf (fun _ => zero_le_one) hfm hone
  simpa using hcs

/-- `(x+y)^2 <= 2x^2 + 2y^2`, on abstract reals. -/
private theorem sq_add_le_two_mul_sq (x y : ℝ) : (x + y) ^ (2 : ℕ) ≤
    2 * x ^ (2 : ℕ) + 2 * y ^ (2 : ℕ) := by
  nlinarith [sq_nonneg (x - y)]

/-! ## Two integrability transfers -/

/-- A nonnegative observable with an integrable square is a.e.-strongly
measurable: it is the square root of its own square. -/
private theorem aestronglyMeasurable_of_sq_integrable {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : Omega → ℝ} (hA0 : ∀ omega, 0 ≤ A omega)
    (hA : Integrable (fun omega => A omega ^ (2 : ℕ)) mu) :
    AEStronglyMeasurable A mu := by
  have hroot := Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  refine hroot.congr (Filter.Eventually.of_forall fun omega => ?_)
  simpa using Real.sqrt_sq (hA0 omega)

/-- A nonnegative observable with an integrable square is integrable on a finite
measure space. -/
private theorem integrable_of_sq_integrable' {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {A : Omega → ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA : Integrable (fun omega => A omega ^ (2 : ℕ)) mu) : Integrable A mu := by
  refine Integrable.mono' ((integrable_const ((1 : ℝ) / 2)).add
    (hA.const_mul ((1 : ℝ) / 2))) (aestronglyMeasurable_of_sq_integrable hA0 hA)
    (Filter.Eventually.of_forall fun omega => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (hA0 omega)]
  nlinarith [sq_nonneg (A omega - 1)]

/-! ## The two cell data of the crude elliptic majorant -/

/-- **The potential datum of the cell**: the Step-2 background's normalized
potential cell energy plus the squared length of the potential leg of the cell's
principal load `P_z`.  It is the factor the ellipticity constant multiplies in
`Closure.GammaTenStripCell.stripCellMajorant`. -/
def stripCellPotentialDatum (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega +
    vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1

/-- **The flux datum of the cell**, the flux mirror of `stripCellPotentialDatum`.
It carries only the deterministic factor `2 nu^{-1}`. -/
def stripCellFluxDatum (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega +
    vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2

theorem stripCellPotentialDatum_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    0 ≤ stripCellPotentialDatum M n h Kc e e' wD wN R omega :=
  add_nonneg (meshCellBackgroundPotentialEnergy_nonneg M n h Kc e e' wD wN R omega)
    (vecNormSq_nonneg _)

theorem stripCellFluxDatum_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    0 ≤ stripCellFluxDatum M n h Kc e e' wD wN R omega :=
  add_nonneg (meshCellBackgroundFluxEnergy_nonneg M n h Kc e e' wD wN R omega)
    (vecNormSq_nonneg _)

/-- The crude elliptic majorant, read at the two cell data.  Definitional. -/
theorem stripCellMajorant_eq_data (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    stripCellMajorant M n h Kc e e' wD wN R omega =
      (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
            2 * M.nu⁻¹ *
              coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
          stripCellPotentialDatum M n h Kc e e' wD wN R omega +
        2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega :=
  rfl

/-! ## The cell-uniform majorization -/

/-- **The majorant is below the cell-uniform ellipticity weight times the
potential datum, plus the flux datum.**

The only cell-dependent factor of the coefficient leg is replaced by the
envelope of `Closure.GammaTenStripMoment`, which is uniform over every cube
inside the localization cube.

only on the geometric containment `hsub`. -/
theorem stripCellMajorant_le_weight_mul_data (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {R : TriadicCube d} (hsub : openCubeSet R ⊆ openCubeSet (originCube d Kc))
    (omega : CutoffSample d) :
    stripCellMajorant M n h Kc e e' wD wN R omega ≤
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
          stripCellPotentialDatum M n h Kc e e' wD wN R omega +
        2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega := by
  have hD0 : (0 : ℝ) ≤ stripCellPotentialDatum M n h Kc e e' wD wN R omega :=
    stripCellPotentialDatum_nonneg M n h Kc e e' wD wN R omega
  have hA := ellipticityUpper_weight_le_stripEllipticityWeight M (n + (h : ℤ)) hsub omega
  have hmul := mul_le_mul_of_nonneg_right hA hD0
  rw [stripCellMajorant_eq_data]
  linarith

/-! ## The sample integrability of the majorant at one cell -/

/-- **The `hint` binder of
`cubeFamilyAverage_sq_integral_meshFluctuationCellIntegrand_le_of_majorant`,
at one cell.**

on the geometric containment `hsub` and on the second sample moments `hDsq`,
`hFsq` of the two cell data.  No measurability of the corrector data is
assumed: each datum is the square root of its own square, hence a.e.-strongly
measurable as soon as that square is integrable. -/
theorem integrable_stripCellMajorant_of_data_sq (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {R : TriadicCube d} (hsub : openCubeSet R ⊆ openCubeSet (originCube d Kc))
    (hDsq : Integrable (fun omega : CutoffSample d =>
      stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure)
    (hFsq : Integrable (fun omega : CutoffSample d =>
      stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d =>
      stripCellMajorant M n h Kc e e' wD wN R omega) (cutoffSampleLaw M).toMeasure := by
  classical
  have hD0 : ∀ omega, (0 : ℝ) ≤ stripCellPotentialDatum M n h Kc e e' wD wN R omega :=
    fun omega => stripCellPotentialDatum_nonneg M n h Kc e e' wD wN R omega
  have hF0 : ∀ omega, (0 : ℝ) ≤ stripCellFluxDatum M n h Kc e e' wD wN R omega :=
    fun omega => stripCellFluxDatum_nonneg M n h Kc e e' wD wN R omega
  have hDm := aestronglyMeasurable_of_sq_integrable hD0 hDsq
  have hFm := aestronglyMeasurable_of_sq_integrable hF0 hFsq
  have hW0 : ∀ omega, (0 : ℝ) ≤
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega :=
    fun omega => stripEllipticityWeight_nonneg M (n + (h : ℤ)) (originCube d Kc) omega
  have hWmeas := measurable_stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc)
  have hWsq := integrable_sq_stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc)
  have hWD : Integrable (fun omega : CutoffSample d =>
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
        stripCellPotentialDatum M n h Kc e e' wD wN R omega)
      (cutoffSampleLaw M).toMeasure :=
    integrable_mul_of_sq_integrable hW0 hD0
      (hWmeas.aestronglyMeasurable.mul hDm) hWsq hDsq
  have hFint : Integrable (fun omega : CutoffSample d =>
      stripCellFluxDatum M n h Kc e e' wD wN R omega) (cutoffSampleLaw M).toMeasure :=
    integrable_of_sq_integrable' hF0 hFsq
  have hsum : Integrable (fun omega : CutoffSample d =>
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
          stripCellPotentialDatum M n h Kc e e' wD wN R omega +
        2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega)
      (cutoffSampleLaw M).toMeasure := hWD.add (hFint.const_mul _)
  have hLam : Measurable (fun omega : CutoffSample d =>
      coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R) :=
    measurable_coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) R
  have hmajm : AEStronglyMeasurable (fun omega : CutoffSample d =>
      stripCellMajorant M n h Kc e e' wD wN R omega) (cutoffSampleLaw M).toMeasure :=
    (((hLam.add (measurable_const.mul (hLam.pow_const 2))).aestronglyMeasurable).mul
      hDm).add (hFm.const_mul _)
  refine Integrable.mono' hsum hmajm (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_of_nonneg (stripCellMajorant_nonneg M n h Kc e e' wD wN R omega)]
  exact stripCellMajorant_le_weight_mul_data M n h Kc e e' wD wN hsub omega

/-! ## The grid bound at the majorant -/

/-- **The grid average of the squared cell expectations of the majorant.**

on the two per-cell second moments `hDsq`, `hFsq` and on their two grid
averages `hpot`, `hflux`.  The coefficient leg is paid once, by the
cell-uniform `Closure.GammaTenStripMoment.stripLambdaMoment`. -/
theorem cubeFamilyAverage_sq_integral_stripCellMajorant_le (M : ABKModel d) (n : ℤ)
    (h : ℕ) (Kc : ℤ) (j : ℕ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {Cpot Cflux : ℝ}
    (hDsq : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hFsq : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hpot : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => ∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤ Cpot)
    (hflux : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤ Cflux) :
    cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ (2 : ℕ)) ≤
      2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) * Cpot +
        8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux := by
  classical
  have hjle : Kc - (j : ℤ) ≤ Kc := by omega
  have hmesh : mesoCubeGrid d Kc (Kc - (j : ℤ)) =
      descendantsAtDepth (originCube d Kc) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hjle]
    congr 1
    omega
  have hMw0 : (0 : ℝ) ≤ stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) :=
    stripLambdaMoment_nonneg M (n + (h : ℤ)) (originCube d Kc)
  have hW0 : ∀ omega, (0 : ℝ) ≤
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega :=
    fun omega => stripEllipticityWeight_nonneg M (n + (h : ℤ)) (originCube d Kc) omega
  have hWmeas := measurable_stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc)
  have hWsq := integrable_sq_stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc)
  have hWL2 : MemLp (fun omega : CutoffSample d =>
      stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega) 2
      (cutoffSampleLaw M).toMeasure :=
    (memLp_two_iff_integrable_sq hWmeas.aestronglyMeasurable).2 hWsq
  have hstep : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      (∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ (2 : ℕ) ≤
        2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) *
            (∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
              ∂(cutoffSampleLaw M).toMeasure) +
          8 * M.nu⁻¹ ^ (2 : ℕ) *
            (∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
              ∂(cutoffSampleLaw M).toMeasure) := by
    intro R hR
    have hRd : R ∈ descendantsAtDepth (originCube d Kc) j := by rwa [hmesh] at hR
    have hsub : openCubeSet R ⊆ openCubeSet (originCube d Kc) :=
      openCubeSet_subset_of_mem_descendantsAtDepth hRd
    have hD0 : ∀ omega, (0 : ℝ) ≤ stripCellPotentialDatum M n h Kc e e' wD wN R omega :=
      fun omega => stripCellPotentialDatum_nonneg M n h Kc e e' wD wN R omega
    have hF0 : ∀ omega, (0 : ℝ) ≤ stripCellFluxDatum M n h Kc e e' wD wN R omega :=
      fun omega => stripCellFluxDatum_nonneg M n h Kc e e' wD wN R omega
    have hDm := aestronglyMeasurable_of_sq_integrable hD0 (hDsq R hR)
    have hFm := aestronglyMeasurable_of_sq_integrable hF0 (hFsq R hR)
    have hDL2 : MemLp (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h Kc e e' wD wN R omega) 2
        (cutoffSampleLaw M).toMeasure :=
      (memLp_two_iff_integrable_sq hDm).2 (hDsq R hR)
    have hFL2 : MemLp (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h Kc e e' wD wN R omega) 2
        (cutoffSampleLaw M).toMeasure :=
      (memLp_two_iff_integrable_sq hFm).2 (hFsq R hR)
    have hWD : Integrable (fun omega : CutoffSample d =>
        stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
          stripCellPotentialDatum M n h Kc e e' wD wN R omega)
        (cutoffSampleLaw M).toMeasure :=
      integrable_mul_of_sq_integrable hW0 hD0
        (hWmeas.aestronglyMeasurable.mul hDm) hWsq (hDsq R hR)
    have hFint : Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h Kc e e' wD wN R omega) (cutoffSampleLaw M).toMeasure :=
      integrable_of_sq_integrable' hF0 (hFsq R hR)
    have hmajint := integrable_stripCellMajorant_of_data_sq M n h Kc e e' wD wN hsub
      (hDsq R hR) (hFsq R hR)
    have hsumint : Integrable (fun omega : CutoffSample d =>
        stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
            stripCellPotentialDatum M n h Kc e e' wD wN R omega +
          2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega)
        (cutoffSampleLaw M).toMeasure := hWD.add (hFint.const_mul _)
    have h1 : ∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure ≤
        ∫ omega, (stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
              stripCellPotentialDatum M n h Kc e e' wD wN R omega +
            2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega)
          ∂(cutoffSampleLaw M).toMeasure :=
      integral_mono hmajint hsumint fun omega =>
        stripCellMajorant_le_weight_mul_data M n h Kc e e' wD wN hsub omega
    have h2 : ∫ omega, (stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
            stripCellPotentialDatum M n h Kc e e' wD wN R omega +
          2 * M.nu⁻¹ * stripCellFluxDatum M n h Kc e e' wD wN R omega)
          ∂(cutoffSampleLaw M).toMeasure =
        (∫ omega, stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega *
            stripCellPotentialDatum M n h Kc e e' wD wN R omega
            ∂(cutoffSampleLaw M).toMeasure) +
          2 * M.nu⁻¹ * ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega
            ∂(cutoffSampleLaw M).toMeasure := by
      rw [integral_add hWD (hFint.const_mul _), integral_const_mul]
    have h3 := integral_mul_le_sqrt_mul_sqrt (cutoffSampleLaw M).toMeasure hW0 hD0
      hWL2 hDL2
    have h4 := integral_le_sqrt_integral_sq_prob (cutoffSampleLaw M).toMeasure hF0 hFL2
    have hnuinv : (0 : ℝ) ≤ 2 * M.nu⁻¹ := by
      have hnu : (0 : ℝ) < M.nu := M.nu_pos
      positivity
    have h5 : 2 * M.nu⁻¹ * ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure ≤
        2 * M.nu⁻¹ * Real.sqrt (∫ omega,
          stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
            ∂(cutoffSampleLaw M).toMeasure) := mul_le_mul_of_nonneg_left h4 hnuinv
    have hmaj0 : (0 : ℝ) ≤ ∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
        ∂(cutoffSampleLaw M).toMeasure :=
      integral_nonneg fun omega => stripCellMajorant_nonneg M n h Kc e e' wD wN R omega
    have h6 : ∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure ≤
        Real.sqrt (stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc)) *
            Real.sqrt (∫ omega,
              stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
                ∂(cutoffSampleLaw M).toMeasure) +
          2 * M.nu⁻¹ * Real.sqrt (∫ omega,
            stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
              ∂(cutoffSampleLaw M).toMeasure) := by
      rw [h2] at h1
      have hMw : stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) =
          ∫ omega, stripEllipticityWeight M (n + (h : ℤ)) (originCube d Kc) omega ^ (2 : ℕ)
            ∂(cutoffSampleLaw M).toMeasure := rfl
      rw [hMw]
      linarith
    have h7 := pow_le_pow_left₀ hmaj0 h6 2
    have h8 := sq_add_le_two_mul_sq
      (Real.sqrt (stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc)) *
        Real.sqrt (∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure))
      (2 * M.nu⁻¹ * Real.sqrt (∫ omega,
        stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure))
    have hpotint0 : (0 : ℝ) ≤ ∫ omega,
        stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure := integral_nonneg fun omega => sq_nonneg _
    have hfluxint0 : (0 : ℝ) ≤ ∫ omega,
        stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure := integral_nonneg fun omega => sq_nonneg _
    have hsq1 : (Real.sqrt (stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc)) *
        Real.sqrt (∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure)) ^ (2 : ℕ) =
        stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) *
          ∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
            ∂(cutoffSampleLaw M).toMeasure := by
      rw [mul_pow, Real.sq_sqrt hMw0, Real.sq_sqrt hpotint0]
    have hsq2 : (2 * M.nu⁻¹ * Real.sqrt (∫ omega,
        stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure)) ^ (2 : ℕ) =
        4 * M.nu⁻¹ ^ (2 : ℕ) *
          ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
            ∂(cutoffSampleLaw M).toMeasure := by
      rw [mul_pow, Real.sq_sqrt hfluxint0]
      ring
    rw [hsq1, hsq2] at h8
    linarith
  calc cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ (2 : ℕ))
      ≤ cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
          (fun R => 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) *
              (∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
                ∂(cutoffSampleLaw M).toMeasure) +
            8 * M.nu⁻¹ ^ (2 : ℕ) *
              (∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
                ∂(cutoffSampleLaw M).toMeasure)) := cubeFamilyAverage_mono hstep
    _ = 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) *
            cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
              (fun R => ∫ omega,
                stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
                  ∂(cutoffSampleLaw M).toMeasure) +
          8 * M.nu⁻¹ ^ (2 : ℕ) *
            cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
              (fun R => ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
                ∂(cutoffSampleLaw M).toMeasure) := by
        rw [cubeFamilyAverage_add, cubeFamilyAverage_const_mul, cubeFamilyAverage_const_mul]
    _ ≤ 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) * Cpot +
          8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux := by
        have hc1 : (0 : ℝ) ≤ 2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) := by
          linarith
        have hc2 : (0 : ℝ) ≤ 8 * M.nu⁻¹ ^ (2 : ℕ) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hpot hc1)
          (mul_le_mul_of_nonneg_left hflux hc2)

/-! ## `hstrip` -/

/-- **The strip constant.**  `2. (second moment of the cell-uniform ellipticity
weight). Cpot  +  8 nu^{-2}. Cflux`.  Its only inputs are the model's uniform
lower ellipticity `nu`, the ellipticity moment of the localization cube and the
two grid second moments of the cell data. -/
def gammaTenStripConst (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (Cpot Cflux : ℝ) : ℝ :=
  2 * stripLambdaMoment M (n + (h : ℤ)) (originCube d Kc) * Cpot +
    8 * M.nu⁻¹ ^ (2 : ℕ) * Cflux

/-- **`hstrip`.**  The full-mesh average of the squared cell expectations of the
Step-2 cell integrand is below `gammaTenStripConst`.

This is the exact shape of the `hstrip` binder of
`Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`.

on exactly the four moment binders `hDsq`, `hFsq`, `hpot`, `hflux` of
`cubeFamilyAverage_sq_integral_stripCellMajorant_le`: the sign of the cell
integrand is removed by `Closure.GammaTenStripCell`, and no Besov envelope, no
minimizer, no measurable selection and no interior restriction enters. -/
theorem gammaTenStrip_cell_average_sq_le (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (j : ℕ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {Cpot Cflux : ℝ}
    (hDsq : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hFsq : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hpot : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => ∫ omega, stripCellPotentialDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤ Cpot)
    (hflux : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => ∫ omega, stripCellFluxDatum M n h Kc e e' wD wN R omega ^ (2 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤ Cflux) :
    cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ 2) ≤
      gammaTenStripConst M n h Kc Cpot Cflux := by
  classical
  have hjle : Kc - (j : ℤ) ≤ Kc := by omega
  have hmesh : mesoCubeGrid d Kc (Kc - (j : ℤ)) =
      descendantsAtDepth (originCube d Kc) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hjle]
    congr 1
    omega
  refine cubeFamilyAverage_sq_integral_meshFluctuationCellIntegrand_le_of_majorant
    M n h Kc j e e' wD wN (fun R hR => ?_)
    (cubeFamilyAverage_sq_integral_stripCellMajorant_le M n h Kc j e e' wD wN
      hDsq hFsq hpot hflux)
  have hRd : R ∈ descendantsAtDepth (originCube d Kc) j := by rwa [hmesh] at hR
  exact integrable_stripCellMajorant_of_data_sq M n h Kc e e' wD wN
    (openCubeSet_subset_of_mem_descendantsAtDepth hRd) (hDsq R hR) (hFsq R hR)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
