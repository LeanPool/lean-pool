/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGridEighth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeSpatial
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeJensenVec

/-!
# GammaTenStripEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The energy leg of `hstrip`: the exact tiling fold of the cell second moments

ABK26, Step 2 of `l.approximate.recurrence.formula`, `e.nablaw.in.L.eight`.

## What this module is

`Closure.GammaTenStripBound.gammaTenStrip_cell_average_sq_le` leaves exactly two
grid binders: the mesh averages of the sample second moments of the two cell
data `D_R`, `F_R` of the crude elliptic majorant.  This module folds those two
averages onto the **localization cube** by the exact mesh tiling identity
`LocalizationGrid.cubeAverage_originCube_eq_mesoGridAverage`, whose constant is
`1` and which loses nothing at boundary cells:

```
  avsum_{R in 3^n Zd cap cu_K} ( fint_R |u|^2 )^2
      <=  avsum_R fint_R |u|^4  =  fint_{cu_K} |u|^4  =  originCubeFourthEnergy K u .
```

The first step is the per-cell Jensen inequality of CoarseGraining
(`sq_cubeAverage_le_cubeAverage_sq_of_memLp`); the second is the tiling
identity; the third is the definition of the annealed fourth energy of
`LocalizationEnvelopeMesh`.  Its consumer `Closure.GammaTenStripRemainder`
composes the fold with
`LocalizationFluctuationGridEighth.cubeFamilyAverage_integral_le_of_pointwise`
in the sample, which reduces the two grid binders to **one expectation per
leg**,

```
  E[ fint_{cu_K} | e' + grad w_D |^4 ]   and   E[ fint_{cu_K} | e + F |^4 ] ,
```

which is the shape `e.nablaw.in.L.eight` controls through
`LocalizationEnvelopeSpatial.originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le`
and `LocalizationEnvelopeMoment`'s `Gamma_1` second moment.

## The load legs cost nothing

Both cell data are `energy + |load|^2` with the load the cell average of the
same field, so the vector Jensen inequality
(`vecNormSq_const_add_cubeAverageVec_le`, the constant-shifted form proved here)
gives `|load|^2 <= energy` at every cell and hence `D_R <= 2 Epot_R`,
`F_R <= 2 Eflux_R`.  No separate load moment is needed: the `P_z` legs are
absorbed by a factor `4` in the constant.

## What is proved

* `cubeAverageVec_const`, `vecNormSq_const_add_cubeAverageVec_le` --- the
  constant-shifted vector Jensen step at one cube.
* `cubeFamilyAverage_sq_cubeAverage_vecNormSq_le_originCubeFourthEnergy` --- the
  pathwise fold: Jensen and the exact tiling identity, constant `1`.
* `stripCellPotentialDatum_le_two_mul_energy`,
  `stripCellFluxDatum_le_two_mul_energy` --- the two cell data against twice
  their own cell energies.

A pair of grid statements assembling these into the two binders of
`Closure.GammaTenStripBound.gammaTenStrip_cell_average_sq_le` directly from an
annealed fourth energy per leg once stood here too.  Their callers moved to the
pathwise-majorant form `Closure.GammaTenStripRemainder` states
(`..._le_of_majorant`), they lost every consumer, and they were removed; git
history keeps them.

## Binders

Beyond the typing binders: the mesh scale gate `hn` (which only names the mesh);
the per-sample spatial `L^8` membership of the leg field on the localization
cube; and the per-cell `L^2` membership used by the two cell-datum comparisons.
No smallness gate, no induction state, no measurable selection and no
interior-mesh restriction occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.Pz.def`, `e.Fz.def`,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Block
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Membership bookkeeping -/

/-- `|u|^2` is square-integrable on a cube whose `L^8` membership is known. -/
private theorem memLp_vecNormSq_two_of_memLp_eight (Q : TriadicCube d) {u : Vec d → Vec d}
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MemLp (fun x => vecNormSq (u x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have huE : MemLp (fun x => Book.Ch02.vecNorm (u x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_vecNorm_of_memLp Q hu
  have huE4 : MemLp (fun x => Book.Ch02.vecNorm (u x)) (4 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := huE.mono_exponent (by norm_num)
  have h := (memLp_norm_rpow_iff (μ := normalizedCubeMeasure Q)
      (f := fun x => Book.Ch02.vecNorm (u x)) (p := (4 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      huE4.aestronglyMeasurable (by norm_num) (by norm_num)).2 huE4
  have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  rw [hdiv] at h
  have hfun : (fun x => ‖Book.Ch02.vecNorm (u x)‖ ^ ((2 : ℝ≥0∞).toReal)) =
      fun x => vecNormSq (u x) := by
    funext x
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Book.Ch02.vecNorm (u x) ^ (2 : ℕ)),
      Book.Ch02.vecNorm_sq_eq_vecNormSq]
  rwa [hfun] at h

/-- Integrability against the normalized cube measure is integrability against
Lebesgue measure on the closed cube. -/
private theorem integrableOn_cubeSet_of_integrable_normalizedCubeMeasure (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : Integrable f (normalizedCubeMeasure Q)) :
    IntegrableOn f (cubeSet Q) volume := by
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  rw [normalizedCubeMeasure, cubeMeasure] at hf
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hf

/-- `|u|^4` is integrable on a cube whose `L^8` membership is known. -/
private theorem integrableOn_cubeSet_vecNormSq_sq (Q : TriadicCube d) {u : Vec d → Vec d}
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x) ^ (2 : ℕ)) (cubeSet Q) volume := by
  have hf2 := memLp_vecNormSq_two_of_memLp_eight Q hu
  have hint : Integrable (fun x => vecNormSq (u x) ^ (2 : ℕ)) (normalizedCubeMeasure Q) :=
    (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).1 hf2
  exact integrableOn_cubeSet_of_integrable_normalizedCubeMeasure Q hint

/-! ## The constant-shifted vector Jensen step -/

/-- The cube average of a constant vector field is that constant. -/
theorem cubeAverageVec_const (R : TriadicCube d) (c : Vec d) :
    cubeAverageVec R (fun _ => c) = c := by
  funext i
  exact cubeAverage_const R (c i)

/-- **Jensen with a constant shift.**  `|c + (g)_R|^2 <= fint_R |c + g|^2`.

only on the `L^2` membership of `g` on the cube. -/
theorem vecNormSq_const_add_cubeAverageVec_le (R : TriadicCube d) (c : Vec d)
    (g : Vec d → Vec d) (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (c + cubeAverageVec R g) ≤
      cubeAverage R (fun x => vecNormSq (c + g x)) := by
  have hgL2 : MemVectorL2 (cubeSet R) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R hg
  have hcL2 : MemVectorL2 (cubeSet R) (fun _ : Vec d => c) :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R (memLp_const c)
  have hsum : MemLp (fun x => c + g x) (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    (memLp_const c).add hg
  have havg : cubeAverageVec R (fun x => c + g x) = c + cubeAverageVec R g := by
    rw [cubeAverageVec_add R (fun _ => c) g hcL2 hgL2, cubeAverageVec_const]
  have hjensen := vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp R
    (fun x => c + g x) hsum
  rw [cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp R (fun x => c + g x) hsum]
  rw [havg] at hjensen
  exact hjensen

/-! ## The pathwise fold -/

/-- **The exact mesh fold of the squared cell energies.**

```
  avsum_{R in 3^n Zd cap cu_K} ( fint_R |u|^2 )^2  <=  fint_{cu_K} |u|^4 .
```

Per cell this is Jensen; over the mesh it is the tiling identity, whose constant
is `1`.  Boundary cells are included: nothing in the statement distinguishes
them.

on the scale gate `hn`, which only names the mesh, and on the spatial `L^8`
membership `hu` on the localization cube. -/
theorem cubeFamilyAverage_sq_cubeAverage_vecNormSq_le_originCubeFourthEnergy
    {K n : ℤ} (hn : n ≤ K) (u : Vec d → Vec d)
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K))) :
    cubeFamilyAverage (mesoCubeGrid d K n)
        (fun R => cubeAverage R (fun x => vecNormSq (u x)) ^ (2 : ℕ)) ≤
      originCubeFourthEnergy K u := by
  classical
  have hint := integrableOn_cubeSet_vecNormSq_sq (originCube d K) hu
  have hcell : ∀ R ∈ mesoCubeGrid d K n,
      cubeAverage R (fun x => vecNormSq (u x)) ^ (2 : ℕ) ≤
        cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ)) := by
    intro R hR
    have hRd : R ∈ descendantsAtDepth (originCube d K) (K - n).toNat := by
      rwa [mesoCubeGrid_eq_descendantsAtDepth hn] at hR
    have hR8 : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hRd hu
    exact sq_cubeAverage_le_cubeAverage_sq_of_memLp R (fun x => vecNormSq (u x))
      (memLp_vecNormSq_two_of_memLp_eight R hR8)
  have htile := cubeAverage_originCube_eq_mesoGridAverage hn
    (fun x => vecNormSq (u x) ^ (2 : ℕ)) hint
  calc cubeFamilyAverage (mesoCubeGrid d K n)
        (fun R => cubeAverage R (fun x => vecNormSq (u x)) ^ (2 : ℕ))
      ≤ cubeFamilyAverage (mesoCubeGrid d K n)
          (fun R => cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ))) :=
        cubeFamilyAverage_mono hcell
    _ = cubeAverage (originCube d K) (fun x => vecNormSq (u x) ^ (2 : ℕ)) := htile.symm
    _ = originCubeFourthEnergy K u := (originCubeFourthEnergy_eq_cubeAverage K u).symm

/-! ## The two cell energies as cube averages -/

/-- The Chapter-2 cell average is the cube average of the cell's open cube. -/
private theorem average_cubeDomain_eq_cubeAverage (R : TriadicCube d) (f : Vec d → ℝ) :
    average (cubeDomain R) f = cubeAverage R f := by
  have h1 : average (cubeDomain R) f = volumeAverage (openCubeSet R) f := rfl
  rw [h1, volumeAverage_openCubeSet_eq_cubeAverage']

/-- The potential cell energy is `shom^{-1}` times the cube average of
`|e' + grad w_D|^2`.  Unconditional. -/
theorem meshCellBackgroundPotentialEnergy_eq_cubeAverage (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega =
      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        cubeAverage R (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x)) := by
  rw [meshCellBackgroundPotentialEnergy_eq, average_cubeDomain_eq_cubeAverage]

/-- The flux cell energy is `shom` times the cube average of `|e + F|^2`.
Unconditional. -/
theorem meshCellBackgroundFluxEnergy_eq_cubeAverage (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega =
      ((Annealed.sigmaBar M n : ℝ)) *
        cubeAverage R (fun x => vecNormSq (e + neumannFluxField (Annealed.sigmaBar M n)
          omega.val n (n + (h : ℤ)) e' (wN omega.val) x)) := by
  rw [meshCellBackgroundFluxEnergy_eq, average_cubeDomain_eq_cubeAverage]

/-! ## The load legs are below their own cell energies -/

/-- **The potential load leg is below the potential cell energy.**  This is the
constant-shifted Jensen inequality at the cell, read through the two closed
forms; the gauge `shom^{-1}` is common to both sides.

only on the cell `L^2` membership of the corrector gradient. -/
theorem vecNormSq_meshCellLoad_fst_le_energy (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d)
    (hg : MemLp (fun x => (wD omega.val).toH1Function.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R)) :
    vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 ≤
      meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hjensen := vecNormSq_const_add_cubeAverageVec_le R e'
    (fun x => (wD omega.val).toH1Function.grad x) hg
  have hload : vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).1 =
      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        vecNormSq (e' +
          cubeAverageVec R (fun x => (wD omega.val).toH1Function.grad x)) := by
    simp only [meshCellLoad, principalPz_fst]
    change vecNormSq ((Real.sqrt ((Annealed.sigmaBar M n : ℝ)))⁻¹ • _) = _
    rw [vecNormSq_smul, inv_pow, Real.sq_sqrt hsig.le]
  rw [hload, meshCellBackgroundPotentialEnergy_eq_cubeAverage]
  exact mul_le_mul_of_nonneg_left hjensen (inv_nonneg.2 hsig.le)

/-- **The flux load leg is below the flux cell energy.**

only on the cell `L^2` membership of the flux leg field. -/
theorem vecNormSq_meshCellLoad_snd_le_energy (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d)
    (hg : MemLp (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
      (wN omega.val)) (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 ≤
      meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hjensen := vecNormSq_const_add_cubeAverageVec_le R e
    (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
      (wN omega.val)) hg
  have hload : vecNormSq (meshCellLoad M n h Kc e e' wD wN R omega).2 =
      ((Annealed.sigmaBar M n : ℝ)) *
        vecNormSq (e + cubeAverageVec R (neumannFluxField (Annealed.sigmaBar M n)
          omega.val n (n + (h : ℤ)) e' (wN omega.val))) := by
    simp only [meshCellLoad, principalPz_snd]
    change vecNormSq (Real.sqrt ((Annealed.sigmaBar M n : ℝ)) • _) = _
    rw [vecNormSq_smul, Real.sq_sqrt hsig.le]
  rw [hload, meshCellBackgroundFluxEnergy_eq_cubeAverage]
  exact mul_le_mul_of_nonneg_left hjensen hsig.le

/-- The potential cell datum is below twice the potential cell energy. -/
theorem stripCellPotentialDatum_le_two_mul_energy (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d)
    (hg : MemLp (fun x => (wD omega.val).toH1Function.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R)) :
    stripCellPotentialDatum M n h Kc e e' wD wN R omega ≤
      2 * meshCellBackgroundPotentialEnergy M n h Kc e e' wD wN R omega := by
  have hle := vecNormSq_meshCellLoad_fst_le_energy M n h Kc e e' wD wN R omega hg
  unfold stripCellPotentialDatum
  linarith

/-- The flux cell datum is below twice the flux cell energy. -/
theorem stripCellFluxDatum_le_two_mul_energy (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d)
    (hg : MemLp (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
      (wN omega.val)) (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    stripCellFluxDatum M n h Kc e e' wD wN R omega ≤
      2 * meshCellBackgroundFluxEnergy M n h Kc e e' wD wN R omega := by
  have hle := vecNormSq_meshCellLoad_snd_le_energy M n h Kc e e' wD wN R omega hg
  unfold stripCellFluxDatum
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
