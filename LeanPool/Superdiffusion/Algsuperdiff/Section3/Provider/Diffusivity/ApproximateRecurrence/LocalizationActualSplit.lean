/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationActualBackground
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationBasicSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGluingAdmissible
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGluingCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionVariation

/-!
# LocalizationActualSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: `X_z = S_z + tilde S_z` and a generic pre-mesh intermediate toward the insertion step, at the actual carriers

Source displays in ABK26:

* `e.recurrence.P.def`, `e.def.w`, `e.Pz.def`, `e.Fz.def`;
* `S_z := S(., z+cu_n, -P_z, 0; a_m)`;
* the `X_z` display, and the `tilde S_z` display;
* the sentence "Observe that `X_z = S_z + tilde S_z`" and the gluing clause;

`LocalizationSelection*.lean` and `LocalizationGluing*.lean` prove all of this
for *abstract* slope data, carrying caller propositions.
`LocalizationActualBackground.lean` derives those propositions at the genuine
`P_z`, `bfF_z` and correctors.  This module composes the two: it selects the
per-cell `S_z` and `tilde S_z` at the actual carriers, D the cell field as
their sum, and feeds the resulting family into the gluing competitor bound and
the cell algebra.

## Why the sum is a definition and not a comparison

The manuscript defines `X_z` by its own `argmin` display and then *observes*
`X_z = S_z + tilde S_z`.  Selecting `X_z` independently would make that
observation an a.e. identity only, because the two `argmin`s are unique only up
to a null set.  Below, the cell field is *defined* as the sum `S_z + tilde
S_z`, so is literally true, and what is proved instead is that the sum
satisfies the minimizer property (`isDoubledMuMinimizerField.
(localizationBackground.) (S R + T R)`).  What
`exists_localizationActualCellFields` records as its uniqueness clauses is the
a.e. uniqueness of `S_z` and of `tilde S_z` individually; the agreement of the
defined sum with an *independently selected* `X_z` is NOT recorded as a theorem
here — a caller wanting it must apply
`LocalizationSelectionExistence.sameAE_of_isDoubledMuMinimizerField` to the
sum's minimizer property itself.

## What is proved

* `exists_localizationActualCellFields` -- on one localization cell: `S_z` and
  `tilde S_z` exist, are a.e. unique, their sum satisfies the `X_z` minimizer
  property, `tilde S_z` is a doubled response field (the Euler--Lagrange
  equation), and the Step-2 identity holds for it.
* `two_mul_doubledMuValue_localizationActual_add_eq` -- the second line of
  `e.lower.bound.basic.split` at the actual carriers.
* `exists_localizationActualCellSplit` -- the whole family over the descendant
  cells, produced by choice from the per-cell statement.
* `exists_localizationActualCellSplit_blockVecDot_coarseBlockMatrix_le` -- **a
  generic pre-mesh intermediate** (a term-level consumer of the selection and
  gluing layers, but NOT the manuscript's first insertion line): the glued
  field of the actual `S_z + tilde S_z` satisfies the pre-mesh shape, `P.
  bfA_m(cu_K) P <= fint_{cu_K} X. bfA_m X`, with `P` the genuine
  `bfAhom_{m-h}^{-1/2}(e'; e)` of `e.recurrence.P.def`, the coefficient family
  abstract and the mesh average not composed.

## Divergences from the printed statement

* **.**  Carrier as in `LocalizationSelectionExistence`.
* ** /.**  The manuscript's site set `3^n Z^d cap cu_K` is the full descendant
  family `descendantsAtDepth Q j`, inherited from
  `LocalizationGluingAdmissible.lean`.
* **.**  Only the inequality direction of the insertion is produced; nothing
  below asserts that the glued field minimizes anything.
* **.**  `S` and `T` below are total functions on `TriadicCube d` obtained by
  choice, and every conclusion is quantified over `descendantsAtDepth Q j`; the
  values off that family are not load-bearing and no statement mentions them.
  The manuscript's `X_z` is likewise indexed by the sites only.
* **.**  The identity is justified below by the Euler--Lagrange equation of
  `tilde S_z`, never by mean-zeroness of `bfF_z`.
* **The per-cell coefficient.**  As in `LocalizationSelectionFamily.lean`, the
  cell problems are posed at a family `aCell: (R: TriadicCube d) -> CoeffOn
  (cubeDomain R)`; a caller wanting the manuscript's `bfA_m` on every cell
  instantiates it with `Book.Ch02.pointwiseCoeffOnRestrict`.
* **The mesh average is absent.**  `avsum_{z in 3^n Z^d cap cu_K}` and the
  tiling identity belong to a separate lane; the bound below is stated at the
  glued field on `cu_K`, exactly as `LocalizationGluingCompetitor.lean` states
  it.  The per-cell identity that the mesh average would consume is
  `LocalizationGluingAdmissible.gluedDoubledField_eval_of_mem_openCubeSet`: on
  its own open cell the glued field *is* the cell field.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## One localization cell -/

/-- **`S_z`, `tilde S_z` and `X_z = S_z + tilde S_z` on one localization cell.**

At the actual carriers: `R` is the cell `z + cu_n` inside `cu_K`, `P_z` is
`e.Pz.def`, `bfF_z` is `e.Fz.def`, and the background of the `X_z` display is
`localizationBackground`.  The conclusions are, in order:

* `T` is a doubled response field, i.e. satisfies the Euler--Lagrange equation
  (first variation);
* the Step-2 identity holds for `T`, proved from that first variation and not
  from mean-zeroness.

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`, and on the inclusion
`hsub : openCubeSet R ⊆ openCubeSet Q` (the cell sits inside the big cube;
discharged by the descendant geometry at the call sites). -/
theorem exists_localizationActualCellFields (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (aR : CoeffOn (cubeDomain R)) (wD : H10Function (openCubeSet Q))
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    ∃ S T : DoubledField d,
      IsDoubledMuMinimizer (cubeDomain R) aR
          (principalPz sigma omega lowScale highScale e e' R wD wN) S ∧
        (∀ S' : DoubledField d,
            IsDoubledMuMinimizer (cubeDomain R) aR
              (principalPz sigma omega lowScale highScale e e' R wD wN) S' →
            DoubledField.SameAE (U := cubeDomain R) S S') ∧
        IsDoubledMuMinimizerField (cubeDomain R) aR
            (localizationFz sigma omega lowScale highScale e' R wD wN) T ∧
          (∀ T' : DoubledField d,
              IsDoubledMuMinimizerField (cubeDomain R) aR
                (localizationFz sigma omega lowScale highScale e' R wD wN) T' →
              DoubledField.SameAE (U := cubeDomain R) T T') ∧
          IsDoubledMuMinimizerField (cubeDomain R) aR
              (localizationBackground sigma omega lowScale highScale e e' wD wN) (S + T) ∧
            IsDoubledResponseField (cubeDomain R) aR T ∧
              2 * doubledMuValue (cubeDomain R) aR T =
                volumeAverage (openCubeSet R)
                  (doubledBlockPairingIntegrand (cubeDomain R) aR
                    (localizationFz sigma omega lowScale highScale e' R wD wN) T) := by
  have hFpot := memVectorL2_localizationFz_potential sigma omega lowScale highScale e'
    R R hsub wD wN
  have hFflux := memVectorL2_localizationFz_flux sigma omega lowScale highScale e'
    R R hsub wD wN
  have hFamb := isDoubledAmbientField_localizationFz sigma omega lowScale highScale e'
    R hsub wD hwN
  obtain ⟨S, hS⟩ := (doubledMuTheory (cubeDomain R) aR).minimizer_exists
    (principalPz sigma omega lowScale highScale e e' R wD wN)
  obtain ⟨T, hT, -⟩ := exists_isDoubledMuMinimizerField (cubeDomain R) aR hFpot hFflux
  refine ⟨S, T, hS, fun S' hS' =>
      (doubledMuTheory (cubeDomain R) aR).minimizer_unique_ae _ S S' hS hS', hT,
    fun T' hT' => sameAE_of_isDoubledMuMinimizerField hFpot hFflux hT hT', ?_, ?_, ?_⟩
  · have hadd := isDoubledMuMinimizerField_add (U := cubeDomain R) (a := aR)
      (P := principalPz sigma omega lowScale highScale e e' R wD wN)
      (F := localizationFz sigma omega lowScale highScale e' R wD wN) hFpot hFflux hS hT
    rwa [localizationBackground_eq_constantDoubledField_principalPz_add_localizationFz]
      at hadd
  · exact isDoubledResponseField_of_isDoubledMuMinimizerField hFamb hT
  · exact two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField hFamb hT

/-- **The second line of `e.lower.bound.basic.split` at the actual carriers.**
With `S = S_z` the constant-load minimizer at `P_z` and `T = tilde S_z` a
doubled response field on the cell,

```
fint_R (S+T) . bfA (S+T)
  = P_z . bfA(R) P_z + 2 P_z . fint_R bfA (tilde S_z) + fint_R tilde S_z . bfA tilde S_z .
```

This is `LocalizationBasicSplit.two_mul_doubledMuValue_add_eq` with the load
instantiated at `e.Pz.def`; the factor `2` is that module's normalization
convention.: on the two binders `hS`, `hT`, both of which
`exists_localizationActualCellFields` produces. -/
theorem two_mul_doubledMuValue_localizationActual_add_eq (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (aR : CoeffOn (cubeDomain R))
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q))
    {S T : DoubledField d}
    (hS : IsDoubledMuMinimizer (cubeDomain R) aR
      (principalPz sigma omega lowScale highScale e e' R wD wN) S)
    (hT : IsDoubledResponseField (cubeDomain R) aR T) :
    2 * doubledMuValue (cubeDomain R) aR (S + T) =
      blockVecDot (principalPz sigma omega lowScale highScale e e' R wD wN)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain R) aR)
            (principalPz sigma omega lowScale highScale e e' R wD wN))
        + 2 * volumeAverage (openCubeSet R)
            (fun x => blockVecDot (principalPz sigma omega lowScale highScale e e' R wD wN)
              (blockMatVecMul (blockMatrixField aR x) (T.eval x)))
        + 2 * doubledMuValue (cubeDomain R) aR T :=
  two_mul_doubledMuValue_add_eq aR _ hS hT

/-! ## The whole descendant family -/

/-- **The per-cell split over the whole localization family.**

`S` and `T` are the families `z |-> S_z` and `z |-> tilde S_z`, and the cell
field is *defined* as `fun R => S R + T R`, so "Observe that `X_z = S_z + tilde
S_z`" is literally true of it.  Every conclusion is quantified over
`descendantsAtDepth Q j`, the rendering of `3^n Z^d cap cu_K`.

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`. -/
theorem exists_localizationActualCellSplit (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (j : ℕ) (aCell : ∀ R : TriadicCube d, CoeffOn (cubeDomain R))
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ descendantsAtDepth Q j,
          IsDoubledMuMinimizer (cubeDomain R) (aCell R)
            (principalPz sigma omega lowScale highScale e e' R wD wN) (S R)) ∧
        (∀ R ∈ descendantsAtDepth Q j,
            IsDoubledMuMinimizerField (cubeDomain R) (aCell R)
              (localizationFz sigma omega lowScale highScale e' R wD wN) (T R)) ∧
          (∀ R ∈ descendantsAtDepth Q j,
              IsDoubledMuMinimizerField (cubeDomain R) (aCell R)
                (localizationBackground sigma omega lowScale highScale e e' wD wN)
                (S R + T R)) ∧
            (∀ R ∈ descendantsAtDepth Q j,
                IsDoubledResponseField (cubeDomain R) (aCell R) (T R)) ∧
              ∀ R ∈ descendantsAtDepth Q j,
                2 * doubledMuValue (cubeDomain R) (aCell R) (T R) =
                  volumeAverage (openCubeSet R)
                    (doubledBlockPairingIntegrand (cubeDomain R) (aCell R)
                      (localizationFz sigma omega lowScale highScale e' R wD wN) (T R)) := by
  classical
  have hex : ∀ R : TriadicCube d, ∃ ST : DoubledField d × DoubledField d,
      R ∈ descendantsAtDepth Q j →
        IsDoubledMuMinimizer (cubeDomain R) (aCell R)
            (principalPz sigma omega lowScale highScale e e' R wD wN) ST.1 ∧
          IsDoubledMuMinimizerField (cubeDomain R) (aCell R)
              (localizationFz sigma omega lowScale highScale e' R wD wN) ST.2 ∧
            IsDoubledMuMinimizerField (cubeDomain R) (aCell R)
                (localizationBackground sigma omega lowScale highScale e e' wD wN)
                (ST.1 + ST.2) ∧
              IsDoubledResponseField (cubeDomain R) (aCell R) ST.2 ∧
                2 * doubledMuValue (cubeDomain R) (aCell R) ST.2 =
                  volumeAverage (openCubeSet R)
                    (doubledBlockPairingIntegrand (cubeDomain R) (aCell R)
                      (localizationFz sigma omega lowScale highScale e' R wD wN) ST.2) := by
    intro R
    by_cases hR : R ∈ descendantsAtDepth Q j
    · obtain ⟨S, T, hS, -, hT, -, hsum, hresp, hstep⟩ :=
        exists_localizationActualCellFields sigma omega lowScale highScale e e' R
          (openCubeSet_subset_of_mem_descendantsAtDepth hR) (aCell R) wD hwN
      exact ⟨(S, T), fun _ => ⟨hS, hT, hsum, hresp, hstep⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hR⟩
  choose ST hST using hex
  exact ⟨fun R => (ST R).1, fun R => (ST R).2,
    fun R hR => (hST R hR).1, fun R hR => (hST R hR).2.1,
    fun R hR => (hST R hR).2.2.1, fun R hR => (hST R hR).2.2.2.1,
    fun R hR => (hST R hR).2.2.2.2⟩

/-! ## The term consumer -/

/-- **A generic pre-mesh intermediate toward the insertion step and the first line
of `e.lower.bound.basic.split`.**  This is NOT the manuscript's first insertion
line: the printed line carries the mesh average over the scale-`n` grid and the
actual cutoff coefficient `bfA_m` (the
`coefficientCutoffTriadicCoeffFamily.coeffOn` instantiation) on the cube and on
every cell; here the per-cell coefficient family `aCell` is abstract and the
mesh average is not composed.  Both are the successor module's mandate.

```
P . bfA_m(cu_K) P  <=  fint_{cu_K} X . bfA_m X ,
    X = sum_{z} (S_z + tilde S_z) 1_{z+cu_n} ,  P = bfAhom_{m-h}^{-1/2}(e'; e) .
```

Genuine ingredients: `P` is `e.recurrence.P.def`, the cell fields are the
actual `S_z + tilde S_z`, and the background whose class they live in is the
actual `bfAhom_{m-h}^{-1/2}(e' + grad w_D; e + grad w_N + shom^{-1} h e')`,
whose membership in `P + L^2_{pot,0}(cu_K) x Lsolo(cu_K)` is *derived* by
`isDoubledMuAdmissible_localizationBackground` and not assumed.  NOT yet
genuine: the coefficient family (abstract `aCell`, not the actual cutoff
coefficients) and the mesh form (absent).

Per this direction, and only this direction, is available; the mesh average of
the right-hand side is a separate lane's item.

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`. -/
theorem exists_localizationActualCellSplit_blockVecDot_coarseBlockMatrix_le
    (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ)
    (e e' : Vec d) {Q : TriadicCube d} (j : ℕ) (a : CoeffOn (cubeDomain Q))
    (aCell : ∀ R : TriadicCube d, CoeffOn (cubeDomain R))
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ descendantsAtDepth Q j,
          IsDoubledMuMinimizer (cubeDomain R) (aCell R)
            (principalPz sigma omega lowScale highScale e e' R wD wN) (S R)) ∧
        (∀ R ∈ descendantsAtDepth Q j,
            IsDoubledMuMinimizerField (cubeDomain R) (aCell R)
              (localizationFz sigma omega lowScale highScale e' R wD wN) (T R)) ∧
          (∀ R ∈ descendantsAtDepth Q j,
              IsDoubledResponseField (cubeDomain R) (aCell R) (T R)) ∧
            blockVecDot (recurrenceP sigma e e')
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain Q) a)
                  (recurrenceP sigma e e')) ≤
              2 * doubledMuValue (cubeDomain Q) a
                (gluedDoubledField Q j (fun R => S R + T R)) := by
  obtain ⟨S, T, hS, hT, hsum, hresp, -⟩ :=
    exists_localizationActualCellSplit sigma omega lowScale highScale e e' j aCell wD hwN
  refine ⟨S, T, hS, hT, hresp, ?_⟩
  exact blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue_glued a
    (recurrenceP sigma e e')
    (isDoubledMuAdmissible_localizationBackground sigma omega lowScale highScale e e' wD hwN)
    (fun R hR => (hsum R hR).1)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
