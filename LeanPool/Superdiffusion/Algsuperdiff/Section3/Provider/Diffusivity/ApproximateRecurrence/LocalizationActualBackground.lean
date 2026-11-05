/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Convexity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationBasicSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ZeroExtension
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.PDE.NeumannRHS

/-!
# LocalizationActualBackground

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the actual-carrier background of the localization split

Source displays in ABK26:

* `e.homs.defs` together with the two sentences, which say that each diagonal
  block of `bfAhom_m` is a **scalar** matrix;
* `e.recurrence.P.def`, `P = bfAhom_{m-h}^{-1/2}(e'; e)`;
* `e.def.w`, the two correctors `w_{D,e}^{(K)} in H^1_0(cu_K)` and
  `w_{N,e'}^{(K)} in H^1(cu_K)`;
* `e.Pz.def` and `e.Fz.def`;
* the `X_z` display, whose affine background is
  ```
  bfAhom_{m-h}^{-1/2} ( e' + grad w_{D,e}^{(K)};
  e  + grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e' );
  ```

`PrincipalResponsePz.lean` already carries `P_z` (`principalPz`) and `F_z`
(`principalFz`) as functions of the two correctors.  This module puts them on
the doubled-field carrier the localization selection/gluing layer consumes, and
**derives** -- never assumes -- the membership facts that layer left as caller
propositions.

## What is proved

* `linearH1OfDomain` / `potentialFieldOn_const` -- a constant field is the
  gradient of `x |-> p . x`, hence lies in `Lpot(U)`.
* `principalLoadField`, with `potentialFieldOn_smul` and
  `solenoidalFieldOn_smul` -- **the splitting question**:
  `bfAhom_{m-h}^{-1/2}` acts as a positive real scalar on each leg separately,
  and both Chapter-1 field spaces are closed under a real scalar, so
  `L^2_{pot,0} x Lsolo` and `Lpot x Lsol` are each mapped into themselves.  See
  "The `bfAhom` splitting question" below.
* `localizationFz` -- `e.Fz.def` on the `DoubledField d` carrier, per-sample
  `omega` explicit.
* `localizationBackground` -- the affine background of the `X_z` display on the
  same carrier, and
  `localizationBackground_eq_constantDoubledField_principalPz_add_localizationFz`,
  which is the identity `P_z + bfF_z` behind.
* `solenoidalZeroNormalTraceFieldOn_neumannFluxField` -- **derived**: the flux
  leg `grad w_N + shom^{-1} h e'` lies in `Lsolo(cu_K)`.  This is the second
  half of the manuscript's "Since." clause, and it is exactly the weak Neumann
  formulation of `e.def.w` read through the mean-zero gauge.
* `isDoubledMuAdmissible_localizationBackground` -- **the actual-source `hG`**,
  derived: the background lies in `P + L^2_{pot,0}(cu_K) x Lsolo(cu_K)`.
* `memVectorL2_localizationFz_potential` / `..._flux` -- **the actual-source
  `hFpot`/`hFflux`**, derived on every subcube.
* `isDoubledAmbientField_localizationFz` -- `bfF_z in Lpot x Lsol` on a
  localization cell, derived; this is the `hF` of
  `LocalizationSelectionVariation.lean`.

## The `bfAhom` splitting question, resolved

The manuscript's clause names the two memberships
`grad w_D in L^2_{pot,0}(cu_K)` and `grad w_N + shom^{-1} h e' in Lsolo(cu_K)`
for the *unnormalized* pair, and then asserts the membership of the glued field
in `P + L^2_{pot,0}(cu_K) x Lsolo(cu_K)` for the pair *after* applying
`bfAhom_{m-h}^{-1/2}`.  The step needs `bfAhom_{m-h}^{-1/2}` to preserve the
product splitting `L^2_{pot,0} x Lsolo`.

A general symmetric positive block matrix does **not**, and block-diagonality
alone is **not** enough either.  Two independent obstructions:

* off-diagonal blocks mix the legs, and `B v` for a solenoidal `v` is in
  general not a gradient;
* even for a constant *block-diagonal* `diag(A, D)` with `A` symmetric positive
  but not scalar the potential leg fails.  Minimal counterexample: `d = 2`,
  `A = diag(1,2)`, `u(x) = x_1 x_2`, so `grad u = (x_2, x_1)` and
  `A grad u = (x_2, 2 x_1)`, whose curl is `2 - 1 = 1 != 0`; hence `A grad u`
  is not a gradient at all.  The flux leg fails symmetrically:
  `div(D g) = sum_{i,j} D_{ij} d_i g_j` need not vanish when `div g = 0`
  unless `D` is scalar.

So the sentence really does require a structural fact about `bfAhom_{m-h}`, and
only scalarity of the diagonal blocks suffices.

The manuscript supplies the missing structural fact itself, and it is stronger
than block-diagonality: by `e.homs.defs` and the hypercube symmetry sentences
around it, `bfAhom_m = diag(shom_m, shom_m^{-1})` with `shom_m` a positive
**scalar** matrix.  Hence `bfAhom_{m-h}^{-1/2}` acts on a pair as `(u; v) |->
(shom^{-1/2} u; shom^{1/2} v)`, i.e. by a positive real scalar on each leg
separately, and both Chapter-1 field spaces are closed under multiplication by
a real scalar.  `principalLoadField` is that action, written at the
repository's already proved `annealedLimitBlockInvSqrt`, whose defining
`Ch02.blockDiag (shom^{-1/2}. 1) (shom^{1/2}. 1)` is the scalar block diagonal
of `e.homs.defs`; the closure of the two field spaces under a real scalar is
`potentialFieldOn_smul` and `solenoidalFieldOn_smul`, and the step is taken in
exactly that form inside `isDoubledMuAdmissible_localizationBackground`.

The only observation worth recording is presentational and is filed below as a
declared divergence: the manuscript's "Since." clause names the memberships
before the normalization is applied, so a reader must supply the scalarity of
`shom_{m-h}` to complete the sentence.

## Divergences from the printed statement

* **Presentational.**  The membership clause is stated for the unnormalized
  pair; the normalization `bfAhom_{m-h}^{-1/2}` is what actually has to
  preserve the class.  It does, by the scalarity of `shom_{m-h}`, which the
  sentence does not cite.  This is a gap in the printed justification only, not
  in the result; no tex change is proposed beyond citing `e.homs.defs`.
* **The Neumann gauge.**  `H^1(cu_K)` of `e.def.w` is normalized here by the
  mean-zero gauge `H1MeanZeroFunction`, exactly as in the already proved
  `FreshShellExistence.lean`; the gauge does not change the gradient, and
  `solenoidalZeroNormalTraceFieldOn_neumannFluxField` tests against *all* of
  `H^1(cu_K)` by passing to the mean-zero representative of the test function.
* **The conormal boundary condition.**  `n . (grad w_N + shom^{-1} h e') = 0`
  on `d cu_K` is the natural boundary condition of the weak formulation, so
  `Lsolo` membership is the weak formulation itself and not an extra input.
* **.**  No localization scale and no buffer constant occurs below; the
  localization cube enters only as a free `TriadicCube` argument.
* **Pin drift, reported not fixed.**  `Corrector/FreshShellExistence.lean`
  cites `e.def.w` as "".  The mathematical content cited is unchanged and
  that module is not edited here.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## Constant fields are gradients -/

/-- The linear function `x |-> p . x` as an `H^1` function on a Chapter-2
domain, assembled from the coordinate projections.  Unconditional. -/
def linearH1OfDomain (U : Domain d) (p : Vec d) : H1Function (U : Set (Vec d)) :=
  ∑ i : Fin d, p i •
    H1Function.coordOnIsSobolevRegularDomain U.isDomain.isSobolevRegularDomain i

private theorem h1Function_sum_grad {ι : Type} {U : Set (Vec d)} (s : Finset ι)
    (f : ι → H1Function U) :
    (∑ i ∈ s, f i).grad = fun x => ∑ i ∈ s, (f i).grad x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [H1Function.add_grad, Finset.sum_insert ha, ih]

/-- The gradient of `x |-> p . x` is the constant field `p`.  Unconditional. -/
@[simp] theorem linearH1OfDomain_grad (U : Domain d) (p : Vec d) :
    (linearH1OfDomain U p).grad = fun _ => p := by
  rw [linearH1OfDomain, h1Function_sum_grad]
  funext x
  simp only [H1Function.smul_grad, H1Function.coordOnIsSobolevRegularDomain_grad]
  funext j
  rw [Finset.sum_apply]
  simp [basisVec, Pi.single_apply, Finset.sum_ite_eq]

/-- A constant field lies in `Lpot(U)`.  Unconditional. -/
theorem potentialFieldOn_const (U : Domain d) (p : Vec d) :
    Book.Ch01.PotentialFieldOn (U : Set (Vec d)) (fun _ => p) := by
  have h := Book.Ch01.potentialFieldOn_of_h1 (linearH1OfDomain U p)
  rwa [linearH1OfDomain_grad] at h

/-! ## Scalar multiples and differences of the Chapter-1 field spaces

The two zero-trace halves are already proved in the Section 2.4 path lane as
`Algsuperdiff.Section24.Sensitivity.Provider.Path.potentialZeroTraceFieldOn_smul`
and `..._solenoidalZeroNormalTraceFieldOn_smul`, and are reused rather than
restated.  Only the two *ambient* halves, which that lane does not carry, are
proved here. -/

/-- `Lpot(U)` is closed under real scalar multiplication.  Conditional helper A: on
the caller proposition `hf` (membership of `f` in `Lpot(U)`). -/
theorem potentialFieldOn_smul {U : Set (Vec d)} {f : Vec d → Vec d} (c : ℝ)
    (hf : Book.Ch01.PotentialFieldOn U f) :
    Book.Ch01.PotentialFieldOn U (fun x => c • f x) := by
  obtain ⟨hmem, u, hae⟩ := hf
  refine ⟨by simpa using! hmem.const_smul c, c • u, ?_⟩
  filter_upwards [hae] with x hx
  show c • f x = (c • u).grad x
  rw [H1Function.smul_grad, hx]

/-- `Lpot(U)` is closed under differences.  Conditional helper A: on the caller
propositions `hf`, `hg` (membership of both fields in `Lpot(U)`). -/
theorem potentialFieldOn_sub {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : Book.Ch01.PotentialFieldOn U f) (hg : Book.Ch01.PotentialFieldOn U g) :
    Book.Ch01.PotentialFieldOn U (fun x => f x - g x) := by
  obtain ⟨hfmem, u, hfae⟩ := hf
  obtain ⟨hgmem, v, hgae⟩ := hg
  refine ⟨hfmem.sub hgmem, u - v, ?_⟩
  filter_upwards [hfae, hgae] with x hx hy
  show f x - g x = (u - v).grad x
  rw [H1Function.sub_grad, hx, hy]

/-- `Lsol(U)` is closed under differences.  Conditional helper A: on the caller
propositions `hf`, `hg` (membership of both fields in `Lsol(U)`). -/
theorem solenoidalFieldOn_sub {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : Book.Ch01.SolenoidalFieldOn U f) (hg : Book.Ch01.SolenoidalFieldOn U g) :
    Book.Ch01.SolenoidalFieldOn U (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, fun phi => ?_⟩
  have hint1 := integrableOn_vecDot_of_memVectorL2 hf.1 phi.toH1Function.grad_memVectorL2
  have hint2 := integrableOn_vecDot_of_memVectorL2 hg.1 phi.toH1Function.grad_memVectorL2
  have hpt : ∀ x : Vec d,
      vecDot (f x - g x) (phi.toH1Function.grad x)
        = vecDot (f x) (phi.toH1Function.grad x)
          - vecDot (g x) (phi.toH1Function.grad x) := by
    intro x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  calc
    ∫ x in U, vecDot (f x - g x) (phi.toH1Function.grad x) ∂volume
        = ∫ x in U, (vecDot (f x) (phi.toH1Function.grad x)
            - vecDot (g x) (phi.toH1Function.grad x)) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in U, vecDot (f x) (phi.toH1Function.grad x) ∂volume)
          - ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume :=
        integral_sub hint1 hint2
    _ = 0 := by rw [hf.2 phi, hg.2 phi, sub_zero]

/-- `Lsol(U)` is closed under real scalar multiplication.  Conditional helper A: on
the caller proposition `hg` (membership of `g` in `Lsol(U)`). -/
theorem solenoidalFieldOn_smul {U : Set (Vec d)} {g : Vec d → Vec d} (c : ℝ)
    (hg : Book.Ch01.SolenoidalFieldOn U g) :
    Book.Ch01.SolenoidalFieldOn U (fun x => c • g x) := by
  refine ⟨by simpa using! hg.1.const_smul c, fun phi => ?_⟩
  have hpt : ∀ x : Vec d,
      vecDot (c • g x) (phi.toH1Function.grad x)
        = c * vecDot (g x) (phi.toH1Function.grad x) :=
    fun x => vecDot_smul_left c (g x) (phi.toH1Function.grad x)
  calc
    ∫ x in U, vecDot (c • g x) (phi.toH1Function.grad x) ∂volume
        = ∫ x in U, c * vecDot (g x) (phi.toH1Function.grad x) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = c * ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume :=
        integral_const_mul _ _
    _ = 0 := by rw [hg.2 phi, mul_zero]

/-! ## `bfAhom^{-1/2}` on a doubled field -/

/-- **`bfAhom^{-1/2}` applied pointwise to a doubled field.**  By `e.homs.defs` and
the scalarity sentences, the matrix is the scalar block diagonal
`diag(shom^{-1/2}, shom^{1/2})`, so its action is a positive real scalar on
each leg, i.e. the pointwise block action of `annealedLimitBlockInvSqrt`.
Unconditional. -/
def principalLoadField (sigma : PositiveScalar) (X : DoubledField d) : DoubledField d where
  potential := fun x => inverseSqrtLoad sigma (X.potential x)
  flux := fun x => sqrtLoad sigma (X.flux x)

/-! ## Restricting the ambient field spaces to a subdomain -/

/-- A field with zero normal trace on `U` is solenoidal on every open subset `V` of
`U`: an `H^1_0(V)` test function extends by zero to an `H^1_0(U)` one with
gradient `1_V grad phi`.  Conditional helper A: on the caller propositions
`hU`/`hVopen`/`hVU` (openness and inclusion of the subdomain) and `hg`
(zero-normal-trace membership of `g` on `U`). -/
theorem solenoidalFieldOn_of_solenoidalZeroNormalTraceFieldOn_subset
    {U V : Set (Vec d)} (hU : IsOpen U) (hVopen : IsOpen V) (hVU : V ⊆ U)
    {g : Vec d → Vec d} (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) :
    Book.Ch01.SolenoidalFieldOn V g := by
  refine ⟨hg.1.mono_measure (Measure.restrict_mono hVU le_rfl), fun phi => ?_⟩
  have hzero := hg.2
    (Whitney.extendZeroH10 hU hVopen.measurableSet hVU phi).toH1Function
  rw [Whitney.extendZeroH10_grad] at hzero
  have hfun : (fun x => vecDot (g x) (V.indicator phi.toH1Function.grad x))
      = V.indicator fun y => vecDot (g y) (phi.toH1Function.grad y) := by
    funext x
    by_cases hx : x ∈ V
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  rw [hfun, setIntegral_indicator hVopen.measurableSet,
    Set.inter_eq_self_of_subset_right hVU] at hzero
  exact hzero

/-! ## `bfF_z` and the background of the `X_z` display, on the doubled carrier -/

/-- **`e.Fz.def` on Chapter 2's doubled-field carrier.**  The sample point
`omega` is explicit: the flux leg carries the fresh shell `h = k_{highScale} -
k_{lowScale}` of that sample through `Corrector.streamForcing`, so
`localizationFz` is a genuinely per-sample field.  The two components are
`PrincipalResponsePz.principalFz`, so this is a repackaging of the already
proved transcription and not a second reading of the display.  Unconditional. -/
def localizationFz (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    DoubledField d where
  potential := fun x => (principalFz sigma omega lowScale highScale e' R wD wN x).1
  flux := fun x => (principalFz sigma omega lowScale highScale e' R wD wN x).2

/-- The potential leg of `e.Fz.def`.  Unconditional. -/
theorem localizationFz_potential (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationFz sigma omega lowScale highScale e' R wD wN).potential =
      fun x => inverseSqrtLoad sigma
        (wD.toH1Function.grad x - cubeAverageVec R (fun y => wD.toH1Function.grad y)) := by
  funext x
  exact principalFz_fst sigma omega lowScale highScale e' R wD wN x

/-- The flux leg of `e.Fz.def`.  Unconditional. -/
theorem localizationFz_flux (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationFz sigma omega lowScale highScale e' R wD wN).flux =
      fun x => sqrtLoad sigma
        (neumannFluxField sigma omega lowScale highScale e' wN x -
          cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN)) := by
  funext x
  exact principalFz_snd sigma omega lowScale highScale e' R wD wN x

/-- **The affine background of the `X_z` display.**

```
bfAhom_{m-h}^{-1/2} ( e' + grad w_{D,e}^{(K)};
  e  + grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e' )
```

It does not depend on the localization cube: the `z`-dependence of the display
sits entirely in the correction space `(L^2_{pot,0} x Lsolo)(z+cu_n)`, which is
why the single field below is the common background of all the cell problems.
Unconditional. -/
def localizationBackground (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d}
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    DoubledField d :=
  principalLoadField sigma
    { potential := fun x => e' + wD.toH1Function.grad x
      flux := fun x => e + neumannFluxField sigma omega lowScale highScale e' wN x }

/-- The potential leg of the background.  Unconditional. -/
theorem localizationBackground_potential (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationBackground sigma omega lowScale highScale e e' wD wN).potential =
      fun x => inverseSqrtLoad sigma (e' + wD.toH1Function.grad x) :=
  rfl

/-- The flux leg of the background.  Unconditional. -/
theorem localizationBackground_flux (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationBackground sigma omega lowScale highScale e e' wD wN).flux =
      fun x => sqrtLoad sigma
        (e + neumannFluxField sigma omega lowScale highScale e' wN x) :=
  rfl

/-- **The identity behind, `P_z + bfF_z`.**  The background of the `X_z` display is
the constant field of `P_z` (`e.Pz.def`) plus `bfF_z` (`e.Fz.def`), for *every*
localization cube `R`.  This is the field-level statement whose variational
counterpart is `X_z = S_z + tilde S_z`.  Unconditional. -/
theorem localizationBackground_eq_constantDoubledField_principalPz_add_localizationFz
    (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ)
    (e e' : Vec d) {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    constantDoubledField (principalPz sigma omega lowScale highScale e e' R wD wN) +
        localizationFz sigma omega lowScale highScale e' R wD wN =
      localizationBackground sigma omega lowScale highScale e e' wD wN := by
  refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_ <;> funext x
  · have h := congrArg Prod.fst
      (principalPz_add_principalFz sigma omega lowScale highScale e e' R wD wN x)
    simpa [localizationBackground_potential] using! h
  · have h := congrArg Prod.snd
      (principalPz_add_principalFz sigma omega lowScale highScale e e' R wD wN x)
    simpa [localizationBackground_flux] using! h

/-! ## The two membership clauses, derived -/

private theorem matVecMul_identityMat (x : Vec d) :
    matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- **The potential clause, derived.** `grad w_{D,e}^{(K)} in L^2_{pot,0}(cu_K)`,
which is immediate from `w_{D,e}^{(K)} in H^1_0(cu_K)` -- exactly the
manuscript's reason.  No property of the Dirichlet leg of `e.def.w` beyond its
carrier is used.  Unconditional. -/
theorem potentialZeroTraceFieldOn_grad_dirichletCorrector {Q : TriadicCube d}
    (wD : H10Function (openCubeSet Q)) :
    Book.Ch01.PotentialZeroTraceFieldOn (openCubeSet Q) wD.toH1Function.grad :=
  Book.Ch01.potentialZeroTraceFieldOn_of_h10 wD

/-- **The flux clause, derived.** `grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e' in
Lsolo(cu_K)`.

It is not a manuscript premise and is discharged unconditionally, on every
triadic cube and at every sample point, by
`Corrector.exists_isMeanZeroNeumannRhsWeakSolution_streamForcing`; see
`exists_localizationBackground_isDoubledMuAdmissible` below for the produced
form.

The manuscript's conormal condition `n . (grad w_N + shom^{-1} h e') = 0` on
`d cu_K` is the natural boundary condition of that weak formulation, so
`Lsolo` membership is the formulation itself; the only work below is to pass
from the mean-zero gauge in which the problem is posed to arbitrary `H^1(cu_K)`
test functions, which is legitimate because subtracting the average does not
change a gradient. -/
theorem solenoidalZeroNormalTraceFieldOn_neumannFluxField (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet Q)
      (neumannFluxField sigma omega lowScale highScale e' wN) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q)
      (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e') :=
    Corrector.memVectorL2_openCubeSet_of_continuous Q
      (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e')
  have hmem : MemVectorL2 (openCubeSet Q)
      (neumannFluxField sigma omega lowScale highScale e' wN) :=
    wN.toH1Function.grad_memVectorL2.add hforcing
  refine ⟨hmem, fun phi => ?_⟩
  have hEL := hwN phi.toMeanZero
  simp only [H1Function.toMeanZero_grad, matVecMul_identityMat] at hEL
  have hint1 := integrableOn_vecDot_of_memVectorL2
    wN.toH1Function.grad_memVectorL2 phi.grad_memVectorL2
  have hint2 := integrableOn_vecDot_of_memVectorL2 hforcing phi.grad_memVectorL2
  have hneg : ∫ x in openCubeSet Q,
      vecDot (-Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)
        (phi.grad x) ∂volume
      = -∫ x in openCubeSet Q,
          vecDot (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)
            (phi.grad x) ∂volume := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [vecDot_neg_left])
  have hpt : ∀ x : Vec d,
      vecDot (neumannFluxField sigma omega lowScale highScale e' wN x) (phi.grad x)
        = vecDot (wN.toH1Function.grad x) (phi.grad x)
          + vecDot (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)
              (phi.grad x) :=
    fun x => vecDot_add_left _ _ _
  calc
    ∫ x in openCubeSet Q,
          vecDot (neumannFluxField sigma omega lowScale highScale e' wN x)
            (phi.grad x) ∂volume
        = ∫ x in openCubeSet Q,
            (vecDot (wN.toH1Function.grad x) (phi.grad x)
              + vecDot (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)
                  (phi.grad x)) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in openCubeSet Q, vecDot (wN.toH1Function.grad x) (phi.grad x) ∂volume)
          + ∫ x in openCubeSet Q,
              vecDot (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)
                (phi.grad x) ∂volume := integral_add hint1 hint2
    _ = 0 := by rw [hEL, hneg]; ring

/-! ## The actual-source `hG`, derived -/

/-- **The membership assertion, at the actual correctors.**

```
bfAhom_{m-h}^{-1/2} ( e' + grad w_D^{(K)}; e + grad w_N^{(K)} + shom_{m-h}^{-1} h e' )
    in  P + L^2_{pot,0}(cu_K) x Lsolo(cu_K) ,        P = bfAhom_{m-h}^{-1/2}(e'; e) .
```

This is the caller proposition `hG` of
`LocalizationGluingAdmissible.isDoubledMuAdmissible_gluedDoubledField`,
`LocalizationGluingCompetitor.blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue_glued`
and `LocalizationSelectionFamily.exists_localizationCellSelection`, D at the
genuine carriers rather than assumed.  The derivation is the manuscript's own:
the potential leg is a gradient of an `H^1_0(cu_K)` function, the flux leg is
the weak Neumann formulation of `e.def.w`, and the normalization
`bfAhom_{m-h}^{-1/2}` preserves both classes because it is a scalar block
diagonal (`e.homs.defs`; see the module header).

: on `hwN` only, the defining property of `w_{N,e'}^{(K)}`; see
`solenoidalZeroNormalTraceFieldOn_neumannFluxField` and the produced form
`exists_localizationBackground_isDoubledMuAdmissible`. -/
theorem isDoubledMuAdmissible_localizationBackground (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (wD : H10Function (openCubeSet Q))
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    IsDoubledMuAdmissible (cubeDomain Q) (recurrenceP sigma e e')
      (localizationBackground sigma omega lowScale highScale e e' wD wN) := by
  constructor
  · have hfun : (fun x =>
        (localizationBackground sigma omega lowScale highScale e e' wD wN).potential x -
          (recurrenceP sigma e e').1)
        = fun x => (Real.sqrt (sigma : ℝ))⁻¹ • wD.toH1Function.grad x := by
      funext x
      simp only [localizationBackground_potential, recurrenceP_fst, inverseSqrtLoad,
        smul_add]
      abel
    rw [hfun]
    exact _root_.Algsuperdiff.Section24.Sensitivity.Provider.Path.potentialZeroTraceFieldOn_smul
      (potentialZeroTraceFieldOn_grad_dirichletCorrector wD) _
  · have hfun : (fun x =>
        (localizationBackground sigma omega lowScale highScale e e' wD wN).flux x -
          (recurrenceP sigma e e').2)
        = fun x => Real.sqrt (sigma : ℝ) •
            neumannFluxField sigma omega lowScale highScale e' wN x := by
      funext x
      simp only [localizationBackground_flux, recurrenceP_snd, sqrtLoad, smul_add]
      abel
    rw [hfun]
    exact
      _root_.Algsuperdiff.Section24.Sensitivity.Provider.Path.solenoidalZeroNormalTraceFieldOn_smul
      (solenoidalZeroNormalTraceFieldOn_neumannFluxField sigma omega lowScale highScale e' hwN) _

/-! ## The actual-source `hFpot`, `hFflux` and ambient membership of `bfF_z` -/

/-- **The caller proposition `hFpot` of
`LocalizationSelectionExistence.exists_isDoubledMuMinimizerField`, derived.**
The potential leg of `bfF_z` is vector-`L^2` on every subcube of `cu_K`: it is
the gradient of the `H^1_0(cu_K)` corrector minus a constant, scaled by
`shom^{-1/2}`.: on the inclusion `hsub: openCubeSet S ⊆ openCubeSet Q`
(discharged by the descendant geometry at the call sites). -/
theorem memVectorL2_localizationFz_potential (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R S : TriadicCube d) (hsub : openCubeSet S ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemVectorL2 (openCubeSet S)
      (localizationFz sigma omega lowScale highScale e' R wD wN).potential := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet S)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet S
  rw [localizationFz_potential]
  have hgrad : MemVectorL2 (openCubeSet S) wD.toH1Function.grad :=
    memVectorL2_of_subset hsub wD.toH1Function.grad_memVectorL2
  have hconst : MemVectorL2 (openCubeSet S)
      (fun _ : Vec d => cubeAverageVec R (fun y => wD.toH1Function.grad y)) :=
    memVectorL2_const _
  simpa [inverseSqrtLoad] using! (hgrad.sub hconst).const_smul (Real.sqrt (sigma : ℝ))⁻¹

/-- **The caller proposition `hFflux`, derived.**  Same statement for the flux leg
of `bfF_z`.: on the inclusion `hsub: openCubeSet S ⊆ openCubeSet Q` (discharged
by the descendant geometry at the call sites); only square integrability is
claimed here, and the fresh-shell forcing is continuous. -/
theorem memVectorL2_localizationFz_flux (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R S : TriadicCube d) (hsub : openCubeSet S ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemVectorL2 (openCubeSet S)
      (localizationFz sigma omega lowScale highScale e' R wD wN).flux := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet S)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet S
  rw [localizationFz_flux]
  have hgrad : MemVectorL2 (openCubeSet S) wN.toH1Function.grad :=
    memVectorL2_of_subset hsub wN.toH1Function.grad_memVectorL2
  have hforcing : MemVectorL2 (openCubeSet S)
      (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e') :=
    Corrector.memVectorL2_openCubeSet_of_continuous S
      (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e')
  have hflux : MemVectorL2 (openCubeSet S)
      (neumannFluxField sigma omega lowScale highScale e' wN) := hgrad.add hforcing
  have hconst : MemVectorL2 (openCubeSet S)
      (fun _ : Vec d =>
        cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN)) :=
    memVectorL2_const _
  simpa [sqrtLoad] using! (hflux.sub hconst).const_smul (Real.sqrt (sigma : ℝ))

/-- **The caller proposition `hF` of
`LocalizationSelectionVariation.isDoubledResponseField_of_isDoubledMuMinimizerField`,
derived.**  On a localization cell `R` contained in `cu_K`, `bfF_z` lies in
`Lpot(R) x Lsol(R)`.

The two legs are the manuscript's own: the potential leg is a gradient (of the
`H^1_0(cu_K)` corrector restricted to `R`) minus a constant, and a constant is
itself a gradient; the flux leg is the zero-normal-trace field of
`solenoidalZeroNormalTraceFieldOn_neumannFluxField` restricted to `R`, minus a
constant, and a constant is solenoidal on `R` because zero-trace test gradients
integrate to zero.  The normalization `bfAhom_{m-h}^{-1/2}` preserves both
classes by the scalarity of `shom_{m-h}` (`e.homs.defs`).

: on `hwN`, the defining property of `w_{N,e'}^{(K)}`, and on the inclusion
`hsub : openCubeSet R ⊆ openCubeSet Q` (the cell sits inside the big cube;
discharged by the descendant geometry at the call sites). -/
theorem isDoubledAmbientField_localizationFz (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x)) :
    IsDoubledAmbientField (cubeDomain R)
      (localizationFz sigma omega lowScale highScale e' R wD wN) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet R
  constructor
  · rw [localizationFz_potential]
    have hgrad : Book.Ch01.PotentialFieldOn (openCubeSet R) wD.toH1Function.grad :=
      Book.Ch01.potentialFieldOn_of_h1
        (wD.toH1Function.restrict (isOpen_openCubeSet R) hsub)
    have hconst : Book.Ch01.PotentialFieldOn (openCubeSet R)
        (fun _ : Vec d => cubeAverageVec R (fun y => wD.toH1Function.grad y)) :=
      potentialFieldOn_const (cubeDomain R) _
    exact potentialFieldOn_smul _ (potentialFieldOn_sub hgrad hconst)
  · rw [localizationFz_flux]
    have hflux : Book.Ch01.SolenoidalFieldOn (openCubeSet R)
        (neumannFluxField sigma omega lowScale highScale e' wN) :=
      solenoidalFieldOn_of_solenoidalZeroNormalTraceFieldOn_subset
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub
        (solenoidalZeroNormalTraceFieldOn_neumannFluxField sigma omega lowScale highScale
          e' hwN)
    have hconst : Book.Ch01.SolenoidalFieldOn (openCubeSet R)
        (fun _ : Vec d =>
          cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN)) :=
      ⟨memVectorL2_const _, fun phi =>
        integral_vecDot_const_zeroTraceGrad_eq_zero phi _⟩
    exact solenoidalFieldOn_smul _ (solenoidalFieldOn_sub hflux hconst)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
