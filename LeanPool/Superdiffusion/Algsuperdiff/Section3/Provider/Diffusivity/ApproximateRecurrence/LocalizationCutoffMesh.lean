/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationActualSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationParams

/-!
# LocalizationCutoffMesh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the localization split at the actual cutoff coefficient, mesh-averaged

Source displays in ABK26:

* `e.recurrence.params`: the two scale gates `K >= m + 10^10 gamma^{-1}`
  and `n:= m - h - 16 ceil|log_3 gamma|`;
* `e.recurrence.P.def`, `e.def.w`, `e.Pz.def`, `e.Fz.def`;
* the gluing sentence "Observe that `X_z = S_z + tilde S_z`.  Since. we may
  insert it into the minimization problem in `e.variational.mu.U.P` for
  `bfA_m(cu_K)`";
* `e.variational.mu.U.P`, the variational problem the glued field is inserted
  into.

`LocalizationActualSplit.lean` produces the per-cell fields `S_z`,
`tilde S_z` at the actual carriers but leaves the coefficient family abstract
and the mesh average absent.  `LocalizationGrid.lean` supplies the mesh tiling
identity but at an arbitrary integrable function.  This module composes the
two **at the genuine cutoff coefficient**: the global `bfA_m(cu_K)` and every
cell `bfA_m(z+cu_n)` are the *same* `Cutoff.coefficientCutoffTriadicCoeffFamily`
evaluated at `cu_K` and at each descendant cell, and the right-hand side is the
mesh average over the scale-`n` grid.

## The coefficient compatibility that makes "simultaneously at `cu_K` and at
each cell" true

`Cutoff.coefficientCutoffTriadicCoeffFamily M m omega` gives every triadic cube
the *same literal* coefficient field `a_m = nu I + k_m`; only the recorded upper
ellipticity constant varies with the cube, and `blockMatrixField` does not read
it.  Hence the restriction of the family's representative from `cu_K` to a
descendant cell is an **identity of functions**, not an a.e. identity, and no
null set is spent.  That is
`toCoeffField_coefficientCutoffTriadicCoeffFamily_congr` below and its two
consequences; they are what let the mesh step replace `bfA_m(cu_K)`'s
representative by `bfA_m(z+cu_n)`'s inside each cell integral.  A caller working
with a general `Ch02.TriadicCoeffFamily` would have to spend
`Ch02.pointwiseCoeffOnRestrict` and an a.e. argument instead; at the actual
cutoff coefficient neither is needed.

## What is proved

* `toCoeffField_coefficientCutoffTriadicCoeffFamily_congr`,
  `blockMatrixField_coefficientCutoffTriadicCoeffFamily_congr`,
  `blockEnergyDensityAt_coefficientCutoffTriadicCoeffFamily_congr` -- the
  compatibility layer just described, at the level of the coefficient field, of
  the doubled matrix field, and of the doubled energy density.
* `two_mul_doubledMuValue_gluedDoubledField_eq_mesoGridAverage` -- **the mesh
  step**: for the actual cutoff coefficient, `fint_{cu_K} X. bfA_m X = avsum_{z
  in 3^n Zd cap cu_K} fint_{z+cu_n} X_z. bfA_m X_z` when `X` is the glued field
  of the cell fields `X_z`.  The tiling constant is `1`.
* `exists_localizationCutoffCellSplit_blockVecDot_coarseBlockMatrix_le` -- the
  frozen pre-mesh intermediate of `LocalizationActualSplit.lean` **instantiated
  at the actual coefficient family**, `a := (...).coeffOn Q` and `aCell R:=
  (.).coeffOn R`, with the glued field's membership in `P + L^2_{pot,0}(cu_K) x
  Lsolo(cu_K)` carried in the conclusion.
* `exists_localizationCutoffMeshSplit_le_mesoGridAverage` -- **the first line
  of `e.lower.bound.basic.split`** at the actual coefficients, at the actual
  carriers, at the recurrence scales, mesh-averaged.
* `exists_localizationCutoffMeshSplit_le_mesoGridAverage_expanded` -- the same
  bound with the cell energy replaced by the manuscript's **third line**, i.e.
  `P_z. bfA_m(z+cu_n) P_z + 2 P_z. fint bfA_m tilde S_z + fint tilde S_z. bfA_m
  tilde S_z`, mesh-averaged.

## Which printed lines are proved here, and which are not

Proved here (as conditional helper statements, with the binders listed in each
docstring): the inequalities, both mesh-averaged over the full scale-`n` grid,
both at `bfA_m` on `cu_K` and on every cell.  The passage between them runs
through inside `LocalizationBasicSplit.doubledMuValue_add`; the intermediate
line is therefore *used*, and no declaration below states it as a separate
mesh-averaged display.

NOT proved here, and not claimed: any estimate on `S_z`, on `tilde S_z`, on
`bfF_z` or on the correctors; the expectation (Step 2); the reverse of the
insertion inequality.

## Divergences from the printed statement

* **.**  Only the inequality direction of the insertion is produced.
* **.**  The site set `3^n Z^d cap cu_K` is `mesoCubeGrid d K n`, the finite
  family of scale-`n` triadic descendants of `cu_K`, indexed by cubes rather
  than by corner points.  On this family the tiling identity holds at constant
  `1`, which is what the mesh step below uses.
* The line composed below is the full-grid leg, where
  `LocalizationGrid.cubeAverage_originCube_eq_mesoGridAverage` applies exactly
  and no deficit is incurred.  likewise bears on the interior/full mismatch of
  a different average and is not consumed below.
* **: the gap multiplier stays free.**  The meso scale is `recurrenceMesoScale
  a gamma m h` at a **free** `a: Nat`; the printed `16` is nowhere written, and
  no `a >= 28` gate is assumed, because the mesh step needs only `n <= K`.
* **The `K` gate is carried, not derived.**  `hK` below is the printed `K >= m
  + 10^10 gamma^{-1}`.  Only its consequence `m <= K` is used; nothing here
  derives the gate from `e.cgamma.constraints`.
* **.**  Carrier and totalization conventions are inherited unchanged from
  `LocalizationSelectionExistence.lean` and
  `LocalizationGluingAdmissible.lean`: `S` and `T` are total functions on
  `TriadicCube d` and every conclusion is quantified over the grid, the values
  off it being neither used nor mentioned.
* **The factor two.**  As in `LocalizationBasicSplit.lean`, the manuscript's
  `fint_U X . bfA X` is twice CoarseGraining's `doubledMuValue`; the factor is
  carried explicitly and neither object is renormalized.
* **The scale pair.**  `highScale` is the manuscript's `m` and `lowScale` is
  `m - h`: `Corrector.streamForcing sigmaInv omega lowScale highScale e` is the
  forcing `shom_{m-h}^{-1}(k_m - k_{m-h}) e` of `e.def.w`.  The coefficient
  family is therefore taken at `highScale`, which is `bfA_m`, and the meso scale
  at `m = highScale`, `h = highScale - lowScale`.
* **One sample drives both sides.**  `omega : Cutoff.CutoffSample d` supplies the
  coefficient `bfA_m` and, through its underlying shell sequence, the correctors
  and `bfF_z`; no second, unrelated sample appears.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section24.Sensitivity.Provider.Path

noncomputable section

variable {d : ℕ}

/-! ## The coefficient compatibility layer -/

/-- **The actual cutoff coefficient is one field, shared by every cube.**  The
representative of `Cutoff.coefficientCutoffTriadicCoeffFamily M m omega` on `Q`
and its representative on `R` are the *same function* `a_m = nu I + k_m`; the
family's cube dependence lives entirely in the recorded upper ellipticity
constant, which no statement below reads.  Unconditional. -/
theorem toCoeffField_coefficientCutoffTriadicCoeffFamily_congr (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q R : TriadicCube d) :
    ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q).toCoeffField =
      ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R).toCoeffField :=
  rfl

/-- **The doubled matrix field of the actual cutoff coefficient is cube-free.**
`bfA_m` computed on `cu_K` and `bfA_m` computed on a cell agree as functions on
all of space, because `blockMatrixField` reads only `toCoeffField`.
Unconditional. -/
theorem blockMatrixField_coefficientCutoffTriadicCoeffFamily_congr (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q R : TriadicCube d) :
    blockMatrixField ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q) =
      blockMatrixField ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) := by
  unfold blockMatrixField
  rw [toCoeffField_coefficientCutoffTriadicCoeffFamily_congr M m omega Q R]

/-- **The doubled energy density of the actual cutoff coefficient is cube-free.**
This is the pointwise identity the mesh step consumes: inside a cell the
integrand `X . bfA_m X` may be read at the cell's own representative of `bfA_m`
without changing its value, at *every* point and not merely a.e.
Unconditional. -/
theorem blockEnergyDensityAt_coefficientCutoffTriadicCoeffFamily_congr (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q R : TriadicCube d) (Y : BlockVec d) (x : Vec d) :
    blockEnergyDensityAt ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q) Y x =
      blockEnergyDensityAt ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) Y x := by
  change (1 / 2 : ℝ) * blockVecDot Y
      (blockMatVecMul
        (blockMatrixField ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q) x) Y) = _
  rw [blockMatrixField_coefficientCutoffTriadicCoeffFamily_congr M m omega Q R]
  rfl

/-! ## Two elementary facts about the grid average -/

private theorem two_mul_cubeFamilyAverage (I : Finset (TriadicCube d))
    (F : TriadicCube d → ℝ) :
    2 * cubeFamilyAverage I F = cubeFamilyAverage I fun R => 2 * F R := by
  have h : ∑ R ∈ I, (2 : ℝ) * F R = 2 * ∑ R ∈ I, F R := by rw [Finset.mul_sum]
  rw [cubeFamilyAverage, cubeFamilyAverage, h]
  ring

private theorem cubeFamilyAverage_congr {I : Finset (TriadicCube d)}
    {F G : TriadicCube d → ℝ} (h : ∀ R ∈ I, F R = G R) :
    cubeFamilyAverage I F = cubeFamilyAverage I G := by
  rw [cubeFamilyAverage, cubeFamilyAverage, Finset.sum_congr rfl h]

private theorem cubeAverage_eq_volumeAverage_openCubeSet (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    cubeAverage Q f = volumeAverage (openCubeSet Q) f := by
  rw [← volumeAverage_cubeSet_eq_cubeAverage]
  exact ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q f

/-! ## The mesh step -/

/-- **The descendant mesh average of the glued energy, at the actual cutoff
coefficient.**

```
fint_{cu_K} X . bfA_m X
  = avsum_{z in 3^n Zd cap cu_K} fint_{z+cu_n} X_z . bfA_m X_z ,
      X = sum_z X_z 1_{z+cu_n} .
```

Two ingredients meet here.  The tiling identity
`LocalizationGrid.cubeAverage_originCube_eq_mesoGridAverage` splits the average
over `cu_K` into the average of the cell averages at tiling constant `1`; inside
each cell the glued field is the cell field
(`LocalizationGluingAdmissible.gluedDoubledField_eval_of_mem_openCubeSet`) and
`bfA_m(cu_K)`'s representative is `bfA_m(z+cu_n)`'s
(`blockEnergyDensityAt_coefficientCutoffTriadicCoeffFamily_congr`), so each cell
average is exactly the cell's own doubled energy.  The factor `2` is
`LocalizationBasicSplit.lean`'s normalization convention.

: on `hn : n <= K` and on the two `MemVectorL2` memberships of the glued field
on `cu_K`, which supply the integrability the tiling identity consumes.  Both
memberships are discharged from the gluing admissibility at the call site below
and are not manuscript premises. -/
theorem two_mul_doubledMuValue_gluedDoubledField_eq_mesoGridAverage (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) {K n : ℤ} (hn : n ≤ K)
    (X : TriadicCube d → DoubledField d)
    (hpot : MemVectorL2 (openCubeSet (originCube d K))
      (gluedDoubledField (originCube d K) (K - n).toNat X).potential)
    (hflux : MemVectorL2 (openCubeSet (originCube d K))
      (gluedDoubledField (originCube d K) (K - n).toNat X).flux) :
    2 * doubledMuValue (cubeDomain (originCube d K))
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn (originCube d K))
        (gluedDoubledField (originCube d K) (K - n).toNat X) =
      cubeFamilyAverage (mesoCubeGrid d K n) fun R =>
        2 * doubledMuValue (cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) (X R) := by
  classical
  set f : Vec d → ℝ := fun x =>
    blockEnergyDensityAt
      ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn (originCube d K))
      ((gluedDoubledField (originCube d K) (K - n).toNat X).eval x) x with hf
  have hfint : IntegrableOn f (cubeSet (originCube d K)) volume :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
      (integrableOn_blockEnergyDensity
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn (originCube d K)) hpot hflux)
  have hbig : doubledMuValue (cubeDomain (originCube d K))
      ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn (originCube d K))
      (gluedDoubledField (originCube d K) (K - n).toNat X) =
      cubeAverage (originCube d K) f :=
    (cubeAverage_eq_volumeAverage_openCubeSet (originCube d K) f).symm
  have hcell : ∀ R ∈ mesoCubeGrid d K n,
      2 * cubeAverage R f =
        2 * doubledMuValue (cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) (X R) := by
    intro R hR
    have hRd : R ∈ descendantsAtDepth (originCube d K) (K - n).toNat := by
      rwa [mesoCubeGrid_eq_descendantsAtDepth hn] at hR
    have hae : f =ᵐ[volumeMeasureOn (openCubeSet R)]
        fun x => blockEnergyDensityAt
          ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) ((X R).eval x) x := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      change blockEnergyDensityAt
          ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn (originCube d K))
          ((gluedDoubledField (originCube d K) (K - n).toNat X).eval x) x = _
      rw [gluedDoubledField_eval_of_mem_openCubeSet X hRd hx]
      exact blockEnergyDensityAt_coefficientCutoffTriadicCoeffFamily_congr M m omega
        (originCube d K) R ((X R).eval x) x
    have hRval : cubeAverage R f =
        doubledMuValue (cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) (X R) := by
      rw [cubeAverage_eq_volumeAverage_openCubeSet, volumeAverage_congr_ae hae]
      rfl
    rw [hRval]
  rw [hbig, cubeAverage_originCube_eq_mesoGridAverage hn f hfint, two_mul_cubeFamilyAverage]
  exact cubeFamilyAverage_congr hcell

/-! ## The pre-mesh intermediate at the actual coefficient -/

/-- **The frozen pre-mesh intermediate of `LocalizationActualSplit.lean`,
instantiated at the actual cutoff coefficient on the cube and on every cell.**

`a` and `aCell` are no longer free: both are
`Cutoff.coefficientCutoffTriadicCoeffFamily M highScale omega`, the
development's rendering of `bfA_m`, evaluated at `Q` and at each descendant
cell respectively.  The one sample `omega` supplies the coefficient and,
through its underlying shell sequence, `P_z`, `bfF_z` and the correctors of
`e.def.w`.

The conclusion additionally carries the membership assertion, `sum_z X_z
1_{z+cu_n} in P + L^2_{pot,0}(cu_K) x Lsolo(cu_K)`, which is *derived* here
from `isDoubledMuAdmissible_localizationBackground` and the cell minimality,
not assumed; the mesh step consumes it for the integrability of the glued
energy density.

Per only the inequality direction is available.

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`. -/
theorem exists_localizationCutoffCellSplit_blockVecDot_coarseBlockMatrix_le
    (M : ABKModel d) (sigma : PositiveScalar) (omega : CutoffSample d)
    (lowScale highScale : ℤ) (e e' : Vec d) (Q : TriadicCube d) (j : ℕ)
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ (omega : ShellSeq d)
        lowScale highScale e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ descendantsAtDepth Q j,
          IsDoubledMuMinimizer (cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
            (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN) (S R)) ∧
        (∀ R ∈ descendantsAtDepth Q j,
            IsDoubledMuMinimizerField (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
              (localizationFz sigma (omega : ShellSeq d) lowScale highScale e' R wD wN) (T R)) ∧
          (∀ R ∈ descendantsAtDepth Q j,
              IsDoubledResponseField (cubeDomain R)
                ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) (T R)) ∧
            IsDoubledMuAdmissible (cubeDomain Q) (recurrenceP sigma e e')
                (gluedDoubledField Q j fun R => S R + T R) ∧
              blockVecDot (recurrenceP sigma e e')
                  (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain Q)
                    ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q))
                    (recurrenceP sigma e e')) ≤
                2 * doubledMuValue (cubeDomain Q)
                  ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q)
                  (gluedDoubledField Q j fun R => S R + T R) := by
  obtain ⟨S, T, hS, hT, hresp, hle⟩ :=
    exists_localizationActualCellSplit_blockVecDot_coarseBlockMatrix_le sigma
      (omega : ShellSeq d) lowScale highScale e e' j
      ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q)
      (fun R => (coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) wD hwN
  refine ⟨S, T, hS, hT, hresp, ?_, hle⟩
  refine isDoubledMuAdmissible_gluedDoubledField
    (isDoubledMuAdmissible_localizationBackground sigma (omega : ShellSeq d) lowScale highScale
      e e' wD hwN) ?_
  intro R hR
  have hsub : openCubeSet R ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hFpot := memVectorL2_localizationFz_potential sigma (omega : ShellSeq d) lowScale
    highScale e' R R hsub wD wN
  have hFflux := memVectorL2_localizationFz_flux sigma (omega : ShellSeq d) lowScale
    highScale e' R R hsub wD wN
  have hadd := isDoubledMuMinimizerField_add (U := cubeDomain R)
    (a := (coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
    (P := principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN)
    (F := localizationFz sigma (omega : ShellSeq d) lowScale highScale e' R wD wN)
    hFpot hFflux (hS R hR) (hT R hR)
  rw [localizationBackground_eq_constantDoubledField_principalPz_add_localizationFz] at hadd
  exact hadd.1

/-! ## The recurrence scales -/

/-- **The meso scale of `e.recurrence.params` at the recurrence's own scale pair.**
With `highScale = m` and `lowScale = m - h` -- the two endpoints of the fresh
shell `h = k_m - k_{m-h}` carried by `Corrector.streamForcing` -- this is `n =
m - h - a ceil|log_3 gamma|` at a **free** multiplier `a` (; the printed `16`
is nowhere written). -/
def cutoffMesoScale (a : ℕ) (gamma : ℝ) (lowScale highScale : ℤ) : ℤ :=
  recurrenceMesoScale a gamma highScale (highScale - lowScale)

/-- The meso scale never exceeds `m - h = lowScale`.  This is
`LocalizationParams.recurrenceMesoScale_le` at the recurrence's scale pair;
nothing about the multiplier `a` or about `gamma` is used.  Unconditional. -/
theorem cutoffMesoScale_le (a : ℕ) (gamma : ℝ) (lowScale highScale : ℤ) :
    cutoffMesoScale a gamma lowScale highScale ≤ lowScale := by
  have h := recurrenceMesoScale_le a gamma highScale (highScale - lowScale)
  have hsimp : highScale - (highScale - lowScale) = lowScale := by ring
  rwa [hsimp] at h

/-- The meso scale sits below the big scale `K`.  The printed gate is `K >= m +
10^10 gamma^{-1}`; only its consequence `m <= K` is used, together with `h >=
0`.: on `hgamma0`, `hlow` and `hK`, all caller-supplied; nothing here derives
`hK` from `e.cgamma.constraints`. -/
theorem cutoffMesoScale_le_bigScale (a : ℕ) {gamma : ℝ} (hgamma0 : 0 < gamma)
    {lowScale highScale K : ℤ} (hlow : lowScale ≤ highScale)
    (hK : (highScale : ℝ) + 10 ^ 10 * gamma⁻¹ ≤ (K : ℝ)) :
    cutoffMesoScale a gamma lowScale highScale ≤ K := by
  have hpos : (0 : ℝ) < 10 ^ 10 * gamma⁻¹ := by positivity
  have hcast : (highScale : ℝ) ≤ (K : ℝ) := by linarith
  have hint : highScale ≤ K := by exact_mod_cast hcast
  exact le_trans (le_trans (cutoffMesoScale_le a gamma lowScale highScale) hlow) hint

/-! ## The first line of `e.lower.bound.basic.split`, mesh-averaged -/

/-- **The first line of `e.lower.bound.basic.split`, at the actual coefficients, at
the actual carriers, at the recurrence scales, mesh-averaged.**

```
P . bfA_m(cu_K) P  <=  avsum_{z in 3^n Zd cap cu_K} fint_{z+cu_n} X_z . bfA_m X_z ,
    X_z = S_z + tilde S_z ,   P = bfAhom_{m-h}^{-1/2}(e'; e) .
```

Every object is the manuscript's own: `P` is `e.recurrence.P.def`, the big cube
is `cu_K` at the scale, the site set is `3^n Z^d cap cu_K` at the meso scale,
`S_z` is the constant-load minimizer at `P_z` of `e.Pz.def`, `tilde S_z` is the
minimizer over `bfF_z + (L^2_{pot,0} x Lsolo)(z+cu_n)` of `e.Fz.def`, and
`bfA_m` is `Cutoff.coefficientCutoffTriadicCoeffFamily M highScale omega` **on
the cube and on every cell simultaneously**.  The tiling constant of the mesh
average is `1`.

Per this direction, and only this direction, is available.

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`, and on the three scale
binders `hgamma0`, `hlow` (`h >= 0`) and `hK`. -/
theorem exists_localizationCutoffMeshSplit_le_mesoGridAverage (M : ABKModel d)
    (sigma : PositiveScalar) (omega : CutoffSample d) (gapMultiplier : ℕ) {gamma : ℝ}
    (hgamma0 : 0 < gamma) {lowScale highScale K : ℤ} (hlow : lowScale ≤ highScale)
    (hK : (highScale : ℝ) + 10 ^ 10 * gamma⁻¹ ≤ (K : ℝ)) (e e' : Vec d)
    (wD : H10Function (openCubeSet (originCube d K)))
    {wN : H1MeanZeroFunction (openCubeSet (originCube d K))}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet (originCube d K)) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ (omega : ShellSeq d)
        lowScale highScale e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
          IsDoubledMuMinimizer (cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
            (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN) (S R)) ∧
        (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
            IsDoubledMuMinimizerField (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
              (localizationFz sigma (omega : ShellSeq d) lowScale highScale e' R wD wN) (T R)) ∧
          (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
              IsDoubledResponseField (cubeDomain R)
                ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) (T R)) ∧
            blockVecDot (recurrenceP sigma e e')
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d K))
                  ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn
                    (originCube d K)))
                  (recurrenceP sigma e e')) ≤
              cubeFamilyAverage
                (mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale))
                fun R => 2 * doubledMuValue (cubeDomain R)
                  ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
                  (S R + T R) := by
  have hn : cutoffMesoScale gapMultiplier gamma lowScale highScale ≤ K :=
    cutoffMesoScale_le_bigScale gapMultiplier hgamma0 hlow hK
  obtain ⟨S, T, hS, hT, hresp, hglue, hle⟩ :=
    exists_localizationCutoffCellSplit_blockVecDot_coarseBlockMatrix_le M sigma omega
      lowScale highScale e e' (originCube d K)
      (K - cutoffMesoScale gapMultiplier gamma lowScale highScale).toNat wD hwN
  have hgrid : ∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
      R ∈ descendantsAtDepth (originCube d K)
        (K - cutoffMesoScale gapMultiplier gamma lowScale highScale).toNat := by
    intro R hR
    rwa [mesoCubeGrid_eq_descendantsAtDepth hn] at hR
  refine ⟨S, T, fun R hR => hS R (hgrid R hR), fun R hR => hT R (hgrid R hR),
    fun R hR => hresp R (hgrid R hR), ?_⟩
  rw [← two_mul_doubledMuValue_gluedDoubledField_eq_mesoGridAverage M highScale omega hn
    (fun R => S R + T R) (memVectorL2_potential_of_isDoubledMuAdmissible hglue)
    (memVectorL2_flux_of_isDoubledMuAdmissible hglue)]
  exact hle

/-! ## The third line of `e.lower.bound.basic.split`, mesh-averaged -/

/-- **The third line of `e.lower.bound.basic.split`, at the actual coefficients, at
the actual carriers, at the recurrence scales, mesh-averaged.**

```
P . bfA_m(cu_K) P
  <= avsum_{z in 3^n Zd cap cu_K} ( P_z . bfA_m(z+cu_n) P_z
       + 2 P_z . fint_{z+cu_n} bfA_m tilde S_z
       + fint_{z+cu_n} tilde S_z . bfA_m tilde S_z ) .
```

The passage from the previous statement runs cell by cell through
`LocalizationActualSplit.two_mul_doubledMuValue_localizationActual_add_eq`,
whose own route is the quadratic expansion followed by the Euler--Lagrange
collapse of the cross term; the intermediate printed line is therefore used,
and is not restated here as a separate display.  All three occurrences of
`bfA_m` on the right are the *cell's* representative of the same cutoff family
whose `cu_K` representative appears on the left.

Per this direction, and only this direction, is available.  No estimate on
`P_z`, on `tilde S_z` or on `bfF_z` is asserted; bounding the two fluctuation
terms is Step 2 of the manuscript and is not attempted here.

: identical to the previous statement -- `hwN` and the three scale binders
`hgamma0`, `hlow`, `hK`. -/
theorem exists_localizationCutoffMeshSplit_le_mesoGridAverage_expanded (M : ABKModel d)
    (sigma : PositiveScalar) (omega : CutoffSample d) (gapMultiplier : ℕ) {gamma : ℝ}
    (hgamma0 : 0 < gamma) {lowScale highScale K : ℤ} (hlow : lowScale ≤ highScale)
    (hK : (highScale : ℝ) + 10 ^ 10 * gamma⁻¹ ≤ (K : ℝ)) (e e' : Vec d)
    (wD : H10Function (openCubeSet (originCube d K)))
    {wN : H1MeanZeroFunction (openCubeSet (originCube d K))}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet (originCube d K)) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ (omega : ShellSeq d)
        lowScale highScale e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
          IsDoubledMuMinimizer (cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
            (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN) (S R)) ∧
        (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
            IsDoubledMuMinimizerField (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
              (localizationFz sigma (omega : ShellSeq d) lowScale highScale e' R wD wN) (T R)) ∧
          (∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
              IsDoubledResponseField (cubeDomain R)
                ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) (T R)) ∧
            blockVecDot (recurrenceP sigma e e')
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d K))
                  ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn
                    (originCube d K)))
                  (recurrenceP sigma e e')) ≤
              cubeFamilyAverage
                (mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale))
                fun R =>
                  blockVecDot
                      (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN)
                      (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain R)
                        ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R))
                        (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN))
                    + 2 * volumeAverage (openCubeSet R) (fun x =>
                        blockVecDot
                          (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN)
                          (blockMatVecMul
                            (blockMatrixField
                              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
                              x)
                            ((T R).eval x)))
                    + 2 * doubledMuValue (cubeDomain R)
                        ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)
                        (T R) := by
  obtain ⟨S, T, hS, hT, hresp, hle⟩ :=
    exists_localizationCutoffMeshSplit_le_mesoGridAverage M sigma omega gapMultiplier
      hgamma0 hlow hK e e' wD hwN
  refine ⟨S, T, hS, hT, hresp, ?_⟩
  have hcell : ∀ R ∈ mesoCubeGrid d K (cutoffMesoScale gapMultiplier gamma lowScale highScale),
      2 * doubledMuValue (cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) (S R + T R) =
        blockVecDot (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R))
              (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN))
          + 2 * volumeAverage (openCubeSet R) (fun x =>
              blockVecDot
                (principalPz sigma (omega : ShellSeq d) lowScale highScale e e' R wD wN)
                (blockMatVecMul
                  (blockMatrixField
                    ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) x)
                  ((T R).eval x)))
          + 2 * doubledMuValue (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) (T R) := by
    intro R hR
    exact two_mul_doubledMuValue_localizationActual_add_eq sigma (omega : ShellSeq d)
      lowScale highScale e e' (Q := originCube d K) R
      ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R) wD wN
      (hS R hR) (hresp R hR)
  rwa [cubeFamilyAverage_congr hcell] at hle

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
