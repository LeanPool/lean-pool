/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsBackground
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsQuadratic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationGridMoment

/-!
# GammaTenStripCell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 cell integrand, bounded on **both** sides at **every** cell

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.basic.split`, `e.CG.bounds.2`.

## What this module is

Every proved bound on `LocalizationFluctuationSelectEndpoint.
meshFluctuationCellIntegrand` --- `Closure.GammaTenAssemblyCell.
meshFluctuationCellIntegrand_le_of_besovEnvelope` and its two fold shapes ---
is **one-sided** (an upper bound) and needs a pathwise Besov envelope `Bg` of
the gauged `bfF_z` on the cell.  The envelope's moment carrier is the
*interior* mesh, which is why
`Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`
has to pay for the boundary strip, and its `hstrip` binder asks for a full-mesh
average of the **squares** of the cell expectations --- a quantity that needs a
bound of the integrand from **below** as well.

This module supplies the missing side.  The bound below is not a refinement of
the Besov route; it is the crude elliptic one, and it needs no envelope, no
minimizer, no Besov exponent, no gauge and no cell-membership beyond the
geometric one that types the `L^2` legs:

```
  |fluct_R(omega)|
    <=  (Lam_R + 2 nu^{-1} Lam_R^2) ( Epot_R + |P_R^{pot}|^2 )
          +  2 nu^{-1} ( Eflux_R + |P_R^{flux}|^2 ) ,
```

`Lam_R = Cutoff.coefficientCutoffCubeEllipticityUpper M (n+h) omega R` being the
realized upper ellipticity constant of the cell's own cutoff coefficient, `nu`
the model's uniform lower one, and `Epot_R`, `Eflux_R` the two named cell
energies of `Closure.SplitObligationsBackground`.

## Where each side comes from

`LocalizationFluctuationMuMeasCell.meshFluctuationCellIntegrand_eq` is the
definitional identity

```
  fluct_R  =  2 mu_field( a_omega; P_z + bfF_z )  -  switch_R(P_z) ,
```

and both summands are bracketed unconditionally:

* `0 <= mu_field <= mu(background)`
  (`LocalizationFluctuationMuMeasCore.doubledMuField_nonneg`,
  `doubledMuField_le_self`) --- the field slope is its own competitor and every
  doubled energy density is a.e. nonnegative;
* `0 <= switch_R(P_z) <= (Lam + 2 nu^{-1} Lam^2)|P^{pot}|^2 + 2 nu^{-1}|P^{flux}|^2`
  (`LocalizationFluctuationMuMeasCell.switchCubeEnergy_nonneg`,
  `Closure.SplitObligationsQuadratic.switchCubeEnergy_le_ellipticityUpper`);
* `mu(background)` itself is below the plain elliptic upper bound of its carrier
  (`Closure.SplitObligationsBackground.doubledMuValue_le_plainUpperBound`), whose
  two averages are *definitionally* the two named cell energies.

The lower half of the integrand uses only the first item's left inequality and
the second item's right one; the upper half only the converse pair.  Nothing is
assumed about the corrector data beyond the vector-`L^2` typing of the two
background legs, which
`LocalizationFluctuationBackgroundClass.memVectorL2_meshCellBackground_{potential,flux}`
supplies from the cell's geometric membership alone.

## What is proved

* `stripCellMajorant` --- the right-hand side above, as a named nonnegative
  sample function of the cell.
* `stripCellMajorant_nonneg`.
* `abs_meshFluctuationCellIntegrand_le_stripCellMajorant` --- the display, at
  every cell of the **full** mesh `descendantsAtDepth (cu_{Kc}) jd` and at every
  sample point.
* `sq_integral_le_sq_integral_of_abs_le` --- the measure-theoretic step that
  turns a two-sided pointwise bound into a bound on the **square of the sample
  integral**, with no integrability of the dominated function assumed: where it
  is integrable the two `abs_le` halves apply, and where it is not the Bochner
  integral is `0` while the majorant's is nonnegative.
* `cubeFamilyAverage_sq_integral_meshFluctuationCellIntegrand_le_of_majorant` ---
  **the reduction of `hstrip`**: the full-mesh average of the squared cell
  expectations is below the same average read at the crude elliptic majorant.
  What is left of `Closure.GammaTenStripAssembly`'s `hstrip` after it is a
  statement about a **nonnegative** grid family --- no minimizer, no Besov datum,
  no interior restriction --- namely the sample integrability of the majorant at
  each cell together with
  ```
    cubeFamilyAverage (mesoCubeGrid d Kc (Kc - j))
      (fun R => (int_omega stripCellMajorant ... R omega)^2) <= Cstrip .
  ```
  That residual is **not** proved here.

## Binders

For the pointwise bound, the cell's geometric membership `hR` and nothing else:
no smallness gate, no Besov exponent, no gauge parameter, no measurability, no
integrability, no moment and no weak-solution property occurs, and the two
correctors enter only as the arguments of the carriers.  The integral step adds
the integrability and nonnegativity of the majorant alone.

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

noncomputable section

variable {d : ℕ}

/-! ## The crude elliptic majorant of the cell -/

/-- **The crude elliptic majorant of the Step-2 cell integrand.**

```
  (Lam_R + 2 nu^{-1} Lam_R^2) ( Epot_R + |P_R^{pot}|^2 )
    +  2 nu^{-1} ( Eflux_R + |P_R^{flux}|^2 ) ,
```

with `Lam_R` the realized upper ellipticity constant of the cell's cutoff
coefficient, `nu` the model's uniform lower one, `Epot_R`, `Eflux_R` the two
named cell energies of the Step-2 background and `P_R` the cell's principal
load.  It mentions no Besov datum and no minimizer. -/
def stripCellMajorant (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
      2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
      (meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega +
        vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1) +
    2 * M.nu⁻¹ *
      (meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega +
        vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2)

/-- The crude elliptic majorant is nonnegative.  Unconditional. -/
theorem stripCellMajorant_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    0 ≤ stripCellMajorant M n h Kc e e' wD wN R omega := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hLam0 : (0 : ℝ) ≤ coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R :=
    coefficientCutoffCubeEllipticityUpper_nonneg M _ omega R
  have hEpot0 : (0 : ℝ) ≤ meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega :=
    meshCellBackgroundPotentialEnergy_nonneg M n h Kc e e' wD wN R omega
  have hEflux0 : (0 : ℝ) ≤ meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega :=
    meshCellBackgroundFluxEnergy_nonneg M n h Kc e e' wD wN R omega
  have hP10 : (0 : ℝ) ≤ vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 :=
    vecNormSq_nonneg _
  have hP20 : (0 : ℝ) ≤ vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 :=
    vecNormSq_nonneg _
  unfold stripCellMajorant
  positivity

/-! ## The two-sided cell bound -/

/-- **The Step-2 cell integrand is bounded in absolute value by the crude
elliptic majorant, at every cell of the full mesh and at every sample point.**

```
  |fluct_R(omega)|  <=  stripCellMajorant M n h Kc e e' wD wN R omega .
```

The upper half drops the switch energy by its nonnegativity and bounds the
field-slope minimum by the energy of its own slope field; the lower half drops
the field-slope minimum by its nonnegativity and bounds the switch energy by the
plain elliptic upper bound of the cell's coefficient.  Neither half mentions a
Besov envelope, so neither is restricted to the interior mesh.

only on the cell's geometric membership `hR`, which is used solely to type the
two background legs as vector-`L^2` on the cell. -/
theorem abs_meshFluctuationCellIntegrand_le_stripCellMajorant
    (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {jd : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) jd)
    (omega : CutoffSample d) :
    |meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega| ≤
      stripCellMajorant M n h Kc e e' wD wN R omega := by
  classical
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hLam0 : (0 : ℝ) ≤ coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R :=
    coefficientCutoffCubeEllipticityUpper_nonneg M _ omega R
  have hA0 : (0 : ℝ) ≤ coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
      2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2 := by
    positivity
  have hB0 : (0 : ℝ) ≤ 2 * M.nu⁻¹ := by positivity
  have hEpot0 : (0 : ℝ) ≤ meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega :=
    meshCellBackgroundPotentialEnergy_nonneg M n h Kc e e' wD wN R omega
  have hEflux0 : (0 : ℝ) ≤ meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega :=
    meshCellBackgroundFluxEnergy_nonneg M n h Kc e e' wD wN R omega
  have hP10 : (0 : ℝ) ≤ vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 :=
    vecNormSq_nonneg _
  have hP20 : (0 : ℝ) ≤ vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 :=
    vecNormSq_nonneg _
  -- the switch energy, two-sidedly
  have hsw0 : (0 : ℝ) ≤
      switchCubeEnergy M (n + (h : ℤ)) R (meshCellLoad M n h Kc e e' wD wN R omega) omega :=
    switchCubeEnergy_nonneg M _ R _ omega
  have hswle :
      switchCubeEnergy M (n + (h : ℤ)) R (meshCellLoad M n h Kc e e' wD wN R omega) omega ≤
        (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
            2 * M.nu⁻¹ *
              coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
            vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 +
          2 * M.nu⁻¹ * vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 :=
    switchCubeEnergy_le_ellipticityUpper M _ R _ omega
  -- the field-slope minimum, two-sidedly
  have hmu0 : (0 : ℝ) ≤ doubledMuField (cubeDomain R)
      (meshCellCoeff M (n + (h : ℤ)) R omega)
      (meshCellBackground M n h Kc e e' wD wN R omega) :=
    doubledMuField_nonneg _ _ _
  have hmule : doubledMuField (cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
      (meshCellBackground M n h Kc e e' wD wN R omega) ≤
      (1 / 2 : ℝ) *
          (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
            2 * M.nu⁻¹ *
              coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
          meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega +
        M.nu⁻¹ * meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega :=
    le_trans (doubledMuField_le_self _ _ _)
      (doubledMuValue_le_plainUpperBound (cubeDomain R)
        (meshCellCoeff M (n + (h : ℤ)) R omega)
        (meshCellBackground M n h Kc e e' wD wN R omega)
        (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR omega)
        (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR omega))
  -- the four products of the majorant
  have hApot : (0 : ℝ) ≤
      (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
          2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
        meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega :=
    mul_nonneg hA0 hEpot0
  have hBflux : (0 : ℝ) ≤ 2 * M.nu⁻¹ *
      meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega := mul_nonneg hB0 hEflux0
  have hAP1 : (0 : ℝ) ≤
      (coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R +
          2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M (n + (h : ℤ)) omega R ^ 2) *
        vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 := mul_nonneg hA0 hP10
  have hBP2 : (0 : ℝ) ≤ 2 * M.nu⁻¹ *
      vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 := mul_nonneg hB0 hP20
  rw [meshFluctuationCellIntegrand_eq, stripCellMajorant, abs_le]
  constructor
  · linarith [hmu0, hswle, hApot, hBflux]
  · linarith [hmule, hsw0, hAP1, hBP2]

/-! ## From the pointwise bound to the square of the sample integral -/

/-- **The square of the integral of a two-sidedly dominated function.**

If `|f| <= g` almost surely with `g` nonnegative and integrable, then
`(int f)^2 <= (int g)^2`.  **No** integrability of `f` is assumed: where `f` is
integrable the bound is `abs_integral_le_integral_abs` followed by
`integral_mono_ae`, and where it is not the Bochner integral of `f` is `0`,
whose absolute value is below the nonnegative integral of `g`.

only on `hg`, `hg0` and `hfg`. -/
theorem sq_integral_le_sq_integral_of_abs_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {f g : Omega → ℝ} (hg : Integrable g mu)
    (hg0 : ∀ w, 0 ≤ g w) (hfg : ∀ᵐ w ∂mu, |f w| ≤ g w) :
    (∫ w, f w ∂mu) ^ 2 ≤ (∫ w, g w ∂mu) ^ 2 := by
  classical
  have hgint0 : (0 : ℝ) ≤ ∫ w, g w ∂mu := integral_nonneg hg0
  have hkey : |∫ w, f w ∂mu| ≤ ∫ w, g w ∂mu := by
    by_cases hf : Integrable f mu
    · exact le_trans (abs_integral_le_integral_abs) (integral_mono_ae hf.abs hg hfg)
    · rw [integral_undef hf, abs_zero]
      exact hgint0
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hkey
  exact sq_le_sq' hlow hhigh

/-! ## `hstrip`, reduced to a nonnegative-majorant grid average -/

/-- **The `hstrip` binder of `Closure.GammaTenStripAssembly`, reduced.**

The left-hand side of

```
  cubeFamilyAverage (mesoCubeGrid d Kc (Kc - j))
    (fun R => (int_omega fluct_R)^2) <= Cstrip
```

is below the same average taken at the **crude elliptic majorant** instead of the
cell integrand.  The passage from the one to the other is the only place where
the sign of the integrand matters, and it is exactly what
`abs_meshFluctuationCellIntegrand_le_stripCellMajorant` removes: after it, the
residual is a statement about a **nonnegative** grid family, with no minimizer,
no Besov datum and no interior restriction left in it.

on the sample integrability of the majorant at each cell of the mesh and on the
majorant's own grid average `hmaj`.  Neither the integrability nor the
measurability of the cell integrand itself is assumed. -/
theorem cubeFamilyAverage_sq_integral_meshFluctuationCellIntegrand_le_of_majorant
    (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {Cstrip : ℝ}
    (hint : ∀ R ∈ mesoCubeGrid d Kc (Kc - (j : ℤ)),
      Integrable (fun omega : CutoffSample d =>
        stripCellMajorant M n h Kc e e' wD wN R omega) (cutoffSampleLaw M).toMeasure)
    (hmaj : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, stripCellMajorant M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ 2) ≤ Cstrip) :
    cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ 2) ≤ Cstrip := by
  classical
  have hjle : Kc - (j : ℤ) ≤ Kc := by omega
  have hmesh : mesoCubeGrid d Kc (Kc - (j : ℤ)) =
      descendantsAtDepth (originCube d Kc) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hjle]
    congr 1
    omega
  refine le_trans (cubeFamilyAverage_mono ?_) hmaj
  intro R hR
  have hRd : R ∈ descendantsAtDepth (originCube d Kc) j := by rwa [hmesh] at hR
  exact sq_integral_le_sq_integral_of_abs_le _ (hint R hR)
    (fun omega => stripCellMajorant_nonneg M n h Kc e e' wD wN R omega)
    (Filter.Eventually.of_forall fun omega =>
      abs_meshFluctuationCellIntegrand_le_stripCellMajorant M n h Kc e e' wD wN hRd omega)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
