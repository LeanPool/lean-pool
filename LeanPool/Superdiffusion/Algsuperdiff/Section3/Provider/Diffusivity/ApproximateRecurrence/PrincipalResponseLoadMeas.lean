/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLowerShellMeas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableGradient

/-!
# PrincipalResponseLoadMeas

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The fresh-shell measurability's load, at the display's own load

Sources in ABK26:

* The sentence "Therefore, by independence of `bfA_{m-h}` and
  `G_{-(h)_{z+cu_n}} P_z` (the latter is a function of `k_m - k_{m-h}`),
  increasing `M` in `\eqref{e.cgamma.constraints}` if necessary,";
* `e.lower.bound.principal.one.pre` (label);
* `e.Pz.def` (label; display), the load itself;
* `e.Gh.def`, the doubled shear that gauges it.

## What this module supplies

```
Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)] W
```

for `W : Cutoff.ShellSeq d -> BlockVec d`.  It was carried as a binder at an
abstract `W` by every consumer, including
`PrincipalResponseLowerShellMeas.integral_blockQuadratic_shellSplit_eq_of_representative`.
This module supplies it at the **concrete** load the display gauges, i.e. at

```
G_{-(h)_{z+cu_n}} P_z
  = blockMatVecMul (blockGauge (-freshShellCubeAverage R omega n m))
      (principalPz sigma omega n m e e' R (wD omega) (wN omega)) ,
```

named `gaugedPrincipalLoadShell` below, and then instantiates the `hWmeas` slot
of the consumer of `PrincipalResponseLowerShellMeas` at it.

## The three legs, and where each one comes from

The load has three sample-dependent ingredients, and each is reduced here to a
**continuous** functional of an already-proved measurable `L^2` class over the
large cube `cu_K`:

1. the averaged fresh shell `(h)_{z+cu_n} = freshShellCubeAverage R omega n m`
   of `e.Gh.def`.  Reading the direction `Pi.single j 1` and the reciprocal
   scale `-1`, the field `x |-> (k_m - k_n)(x) e_j` is literally the negated
   forcing `-streamForcing (-1) omega n m e_j` of `e.def.w`, whose `L^2` class
   is the proved `Corrector.freshShellForcingL2`; its fresh-block measurability
   is `Corrector.measurable_freshShellForcingL2_shellIndexSigma`;
2. the potential average `(grad w_D)_{z+cu_n}`, from the proved
   `Corrector.measurable_shellIndexSigma_freshShellDirichletGradL2`;
3. the flux average `(grad w_N + shom^{-1} h e')_{z+cu_n}`, whose integrand is
   the sum of the Neumann gradient and `streamForcing`, hence whose `L^2` class
   is the difference of the proved Neumann gradient class and the proved
   forcing class, both measurable for the fresh block.

The passage from an `L^2` class on `openCubeSet Q` to the manuscript's cube
average over the localization cube `R` is `cubeAverage_eq_of_coeFn_ae`: for a
descendant `R` of `Q`, the restricted Lebesgue measure of `openCubeSet Q`,
further restricted to `cubeSet R`, is the plain restricted Lebesgue measure of
`cubeSet R`, so the class integrates against `cubeAverage`'s own
measure and may be replaced by any of its representatives.  The remaining
algebra -- `blockGauge`, `matVecMul`, `inverseSqrtLoad`, `sqrtLoad` and the
constants `e`, `e'` -- is finite and continuous.

## The matrix side

`hB` is discharged here as well, at an arbitrary representative of the matrix,
by transporting
`Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix`
across the two carrier changes that `PrincipalResponseIndepWire` already
performs for the *integral*.  See `integrable_blockMatEntry_of_representative`.

## Carriers, disclosed

Every declaration below lives on the shell-sequence carrier `Cutoff.ShellSeq
d`, which is the carrier `integral_blockQuadratic_shellSplit_eq` integrates
over.  No extension along `Subtype.val` is needed for the load:
`freshShellCubeAverage`, `principalPz` and `Corrector.streamForcing` are all
already defined at `Cutoff.ShellSeq d`, and the corrector families are taken at
that carrier, exactly as the proved measurability lemmas of
`Corrector.CorrectorMeasurableGradient` take them.
`gaugedPrincipalLoadShell_val` records that at a genuine cutoff sample the load
below is `PrincipalResponseIndepWire.gaugedSwitchLoad` at `principalPz`.

The matrix is not a concrete term of this file either.  Both declarations below
that mention it quantify over an arbitrary
`B : Cutoff.ShellSeq d -> BlockMat d` carrying the binder

```
∀ᵐ w ∂(Cutoff.cutoffSampleLaw M).toMeasure,
  B w.val = PrincipalResponseIndepWire.switchCubeMatrix M L R w
```

produced by
`PrincipalResponseLowerShellMeas.exists_measurable_representative_switchCubeMatrix`,
and both are invariant under that almost-everywhere identification: `B` is read
only under an integral or an integrability statement.  No value of `B` off the
lower-tail-good carrier is named, asserted or used anywhere below.

## What this module does NOT supply

It does not supply `hW` of
`PrincipalResponseLowerShellMeas.integral_blockQuadratic_shellSplit_eq_of_representative`:
the consuming statement below carries it as a binder, visible in its own
signature.  `hW` is the second-moment integrability of the gauged load, i.e.
the standing moment content of `e.nablaw.in.L.eight` (label) together with a
fourth moment of the averaged fresh shell; no bound on either is asserted or
used anywhere below.  Two ingredients that a later discharge of `hW` would need
are absent from this repository as of writing: any norm or moment estimate for
`cubeAverageMat`/`cubeAverageVec`, and any unconditional `MemLp` for the
corrector gradients on `Cutoff.ShellSeq d`.

`hB` **is** supplied, by `integrable_blockMatEntry_of_representative` below,
and that supply is free of good events and of any structural-law or `(P4)`
hypothesis; the one proposition it does carry is the representative binder
`hBrep` described under "Carriers, disclosed".

It does not supply `hBmeas` either: like the representative binder itself,
`hBmeas` is carried as a binder by the consumer below, and at this matrix it is
available from
`PrincipalResponseLowerShellMeas.exists_measurable_representative_switchCubeMatrix`.

It does not remove the independence binder `hindep`: that binder still stands on
`ApproximateRecurrence.PrincipalResponseBudgetWire`
`exists_smallCoupling_principalEnergy_bound_of_centering`
and on its predecessors, untouched by anything here.

It asserts nothing about the correctors beyond the two weak-solution properties
its binders name, and it constructs no measurable selection: the corrector
families `wD`, `wN` are arbitrary, exactly as in
`Corrector.CorrectorMeasurableGradient`.

## Main results

The public surface is the five declarations listed below, together with the two
component measurability legs of the Step-5 basket and their plain-measurability
corollaries (see the paragraph after the list); the remaining nine declarations
are `private`.  The window-average bridge, the class-to-cube-average reduction,
the flux-average leg and the `principalPz` step stay `private`, because each is
consumed only by a later declaration in this file.

* `gaugedPrincipalLoadShell` -- the load itself; it occurs in the two statements
  below, so it must be public.
* `gaugedPrincipalLoadShell_val` -- the bridge to
  `PrincipalResponseIndepWire.gaugedSwitchLoad`, hence to
  `PrincipalResponseSwitchActualPerCube.switchCubeQuad`.  A consumer that starts
  from the display's per-cube quadratic form on `Cutoff.CutoffSample d` needs
  exactly this identity to reach the shell-carrier statement below.
* `measurable_shellIndexSigma_gaugedPrincipalLoadShell` -- the `hWmeas` input.
* `integrable_blockMatEntry_of_representative` -- the `hB` input of the same
  factorization, at any representative of the matrix.  A consumer that
  instantiates
  `PrincipalResponseLowerShellMeas.integral_blockQuadratic_shellSplit_eq_of_representative`
  at any *other* load needs this one by name; it is therefore public rather
  than private.
* `integral_blockQuadratic_shellSplit_eq_gaugedPrincipalLoadShell` -- the
  consumer, with `hW` its only remaining integrability input.

Two of the component legs are also public, because the Step-5 basket of
`Closure.Step5Basket` needs them by name for its `hmeasX`, `hmeasS`, `hAmem` and
`hvmem` binders and there is no other route to them:

* `measurable_shellIndexSigma_freshShellCubeAverage` and its full-sigma-algebra
  corollary `measurable_freshShellCubeAverage`;
* `measurable_shellIndexSigma_cubeAverageVec_freshShellDirichletGrad` and its
  full-sigma-algebra corollary `measurable_cubeAverageVec_freshShellDirichletGrad`.

Publicizing changes no statement: the two `shellIndexSigma` legs are byte-stable
apart from the dropped `private` keyword, and the two corollaries are their
images under `Cutoff.shellIndexSigma_le_borel`.

## References

* ABK26, (the sentence and its parenthetical);
  `e.lower.bound.principal.one.pre` (label); `e.Pz.def` (label); `e.Gh.def`;
  `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## Generic measurability bookkeeping -/

/-- Internal.  Scalar dilation of a measurable vector-valued map. -/
private theorem measurable_const_smul_vec {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {f : Omega → Vec d} (hf : Measurable f) (c : ℝ) :
    Measurable fun omega => c • f omega := by
  refine Measurable.of_eval fun i => ?_
  exact ((measurable_pi_apply i).comp hf).const_mul c

/-- Internal.  The matrix-vector product of a measurable matrix-valued map and a
measurable vector-valued map is measurable. -/
private theorem measurable_matVecMul {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {A : Omega → Mat d} {x : Omega → Vec d} (hA : Measurable A) (hx : Measurable x) :
    Measurable fun omega => matVecMul (A omega) (x omega) := by
  refine Measurable.of_eval fun i => ?_
  change Measurable fun omega => ∑ j, A omega i j * x omega j
  exact Finset.measurable_sum _ fun j _ =>
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp hx))

/-- Internal.  Reading a direction against the fresh shell: with the reciprocal
scale `-1` and the direction `e_j`, the forcing of `e.def.w` is the `j`th column
of the fresh shell itself. -/
private theorem neg_streamForcing_neg_one_apply (omega : Cutoff.ShellSeq d) (n m : ℤ)
    (j0 : Fin d) (x : Vec d) (i : Fin d) :
    (-streamForcing (-1 : ℝ) omega n m (Pi.single j0 (1 : ℝ)) x) i =
      Cutoff.finiteShellIncrement omega n m x i j0 := by
  have hsingle : ∀ A : Mat d,
      matVecMul A (Pi.single j0 (1 : ℝ)) i = A i j0 := by
    intro A
    simp only [matVecMul]
    rw [Finset.sum_eq_single j0]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  change -((-1 : ℝ) • matVecMul (Cutoff.finiteShellIncrement omega n m x)
      (Pi.single j0 (1 : ℝ))) i = _
  rw [Pi.smul_apply, smul_eq_mul, hsingle, neg_mul, neg_neg, one_mul]

/-! ## From an `L^2` class on the large cube to a cube average on a descendant -/

/-- Internal.  The restricted Lebesgue measure of `openCubeSet Q`, further
restricted to `cubeSet R` for a descendant `R`, is the plain restricted Lebesgue
measure of `cubeSet R`: the two differ only inside the null boundary. -/
private theorem restrict_openCubeSet_restrict_cubeSet {Q R : TriadicCube d} {jd : ℕ}
    (hR : R ∈ descendantsAtDepth Q jd) :
    (volume.restrict (openCubeSet Q)).restrict (cubeSet R) =
      volume.restrict (cubeSet R) := by
  rw [Measure.restrict_restrict (measurableSet_cubeSet R)]
  refine Measure.restrict_congr_set ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [Filter.eventuallyEqSet_iff.1 (cubeSet_ae_eq_openCubeSet R)] with x hx
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, openCubeSet_subset_of_mem_descendantsAtDepth hR (hx.1 h)⟩

/-- Internal.  **The manuscript's cube average over a localization cube is a
continuous functional of the `L^2` class over the large cube.**

Conditional on its binders `hR` (geometric membership) and `hG` (the a.e.
representation of the field by the class).  For a descendant `R` of `Q`, and for
any `L^2` class `G` on `openCubeSet Q` that represents the field `F`, the
coordinate cube average `cubeAverage R (F . i)` is the normalized window
integral of `G` over `cubeSet R`.  No integrability of `F` is assumed: both
sides are Bochner integrals of a.e.-equal integrands against the same
measure. -/
private theorem cubeAverage_eq_of_coeFn_ae {Q R : TriadicCube d} {jd : ℕ}
    (hR : R ∈ descendantsAtDepth Q jd) (F : Vec d → Vec d)
    (G : HilbertVectorL2 (openCubeSet Q)) (i : Fin d)
    (hG : (fun x => (G : Vec d → HilbertVec d) x i)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => F x i) :
    cubeAverage R (fun x => F x i) =
      (cubeVolume R)⁻¹ *
        ∫ x in cubeSet R, G x i ∂(volumeMeasureOn (openCubeSet Q)) := by
  rw [cubeAverage]
  congr 1
  have hmeas : (volume.restrict (openCubeSet Q)).restrict (cubeSet R) =
      volume.restrict (cubeSet R) := restrict_openCubeSet_restrict_cubeSet hR
  have hcoord : (fun x => (G : Vec d → HilbertVec d) x i)
      =ᵐ[volume.restrict (cubeSet R)] fun x => F x i :=
    ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hG
  change ∫ x in cubeSet R, F x i ∂volume =
    ∫ x, (G : Vec d → HilbertVec d) x i
      ∂((volume.restrict (openCubeSet Q)).restrict (cubeSet R))
  rw [hmeas]
  exact (integral_congr_ae hcoord).symm

/-- Internal.  A coordinate of an `L^2` representative agrees a.e. with the
corresponding coordinate of the field it represents. -/
private theorem coeFn_ae_coord {U : Set (Vec d)} {F : Vec d → Vec d}
    {G : HilbertVectorL2 U}
    (h : (G : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn U] hilbertifyVecField F)
    (i : Fin d) :
    (fun x => (G : Vec d → HilbertVec d) x i)
      =ᵐ[volumeMeasureOn U] fun x => F x i := by
  filter_upwards [h] with x hx
  rw [hx]
  simp [hilbertifyVecField]

/-- Internal.  **A cube average of a family of fields represented by a
measurable family of `L^2` classes is measurable for the same sigma-field.**

Conditional on its binders `hR`, `hGmeas` and `hG`.  This is the single
reduction used three times below: the cube average is the composition of a fixed
continuous linear functional of the class with the measurable class-valued
map. -/
private theorem measurable_shellIndexSigma_cubeAverageVec_of_class
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) {I : Set ℤ}
    (F : Cutoff.ShellSeq d → Vec d → Vec d)
    (G : Cutoff.ShellSeq d → HilbertVectorL2 (openCubeSet Q))
    (hGmeas : Measurable[Cutoff.shellIndexSigma I] G)
    (hG : ∀ (omega : Cutoff.ShellSeq d) (i : Fin d),
      (fun x => (G omega : Vec d → HilbertVec d) x i)
        =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => F omega x i) :
    Measurable[Cutoff.shellIndexSigma I]
      fun omega : Cutoff.ShellSeq d => cubeAverageVec R (F omega) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : MeasurableSpace (Cutoff.ShellSeq d) := Cutoff.shellIndexSigma I
  have hEq : (fun omega : Cutoff.ShellSeq d => cubeAverageVec R (F omega)) =
      fun omega : Cutoff.ShellSeq d =>
        (fun i => (cubeVolume R)⁻¹ *
          hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet Q) (cubeSet R)
            (measurableSet_cubeSet R) i (G omega) : Vec d) := by
    funext omega
    funext i
    change cubeAverage R (fun x => F omega x i) = _
    rw [cubeAverage_eq_of_coeFn_ae hR (F omega) (G omega) i (hG omega i)]
    congr 1
    exact (hilbertVectorL2CoordSetIntegralCLM_apply (U := openCubeSet Q)
      (cubeSet R) (measurableSet_cubeSet R) i (G omega)).symm
  rw [hEq]
  refine Measurable.of_eval fun i => ?_
  exact Measurable.const_mul
    (((hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet Q) (cubeSet R)
      (measurableSet_cubeSet R) i).continuous.measurable).comp hGmeas) _

/-! ## Leg 1: the averaged fresh shell of `e.Gh.def` -/

/-- **The averaged fresh shell `(h)_{z+cu_n}` is a measurable function of the
fresh shells `(n, m]` alone.**

This is's parenthetical for the gauge factor of `e.Gh.def`.  Conditional on the
single binder `hR`: the localization cube `R` is any descendant of the large
cube `Q`.  No corrector and no solution property enters. -/
theorem measurable_shellIndexSigma_freshShellCubeAverage
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (n m : ℤ) :
    Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      fun omega : Cutoff.ShellSeq d => freshShellCubeAverage R omega n m := by
  let : MeasurableSpace (Cutoff.ShellSeq d) := Cutoff.shellIndexSigma (Set.Ioc n m)
  refine Measurable.of_eval fun i => Measurable.of_eval fun j0 => ?_
  have hbase : Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      fun omega : Cutoff.ShellSeq d =>
        cubeAverageVec R
          (fun x => -streamForcing (-1 : ℝ) omega n m (Pi.single j0 (1 : ℝ)) x) :=
    measurable_shellIndexSigma_cubeAverageVec_of_class hR _
      (fun omega => freshShellForcingL2 Q (-1 : ℝ) n m (Pi.single j0 (1 : ℝ)) omega)
      (measurable_freshShellForcingL2_shellIndexSigma Q (-1 : ℝ) n m
        (Pi.single j0 (1 : ℝ)))
      (fun _ i => coeFn_ae_coord (coeFn_toHilbertVectorL2OfVecField _) i)
  have hEq : (fun omega : Cutoff.ShellSeq d => freshShellCubeAverage R omega n m i j0) =
      fun omega : Cutoff.ShellSeq d =>
        cubeAverageVec R
          (fun x => -streamForcing (-1 : ℝ) omega n m (Pi.single j0 (1 : ℝ)) x) i := by
    funext omega
    rw [freshShellCubeAverage_apply]
    change cubeAverage R _ = cubeAverage R _
    exact congrArg (cubeAverage R)
      (funext fun x => (neg_streamForcing_neg_one_apply omega n m j0 x i).symm)
  rw [hEq]
  exact (measurable_pi_apply i).comp hbase

/-- **The averaged fresh shell is measurable for the full sigma-algebra.**  The
fresh-shell sigma-field is coarser than the ambient one
(`Cutoff.shellIndexSigma_le_borel`), so the statement above is the stronger one
and this is its plain-measurability corollary. -/
theorem measurable_freshShellCubeAverage
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (n m : ℤ) :
    Measurable fun omega : Cutoff.ShellSeq d => freshShellCubeAverage R omega n m :=
  (measurable_shellIndexSigma_freshShellCubeAverage hR n m).mono
    (Cutoff.shellIndexSigma_le_borel _) le_rfl

/-! ## Leg 2: the potential average of `e.Pz.def` -/

/-- **The potential average `(grad w_D)_{z+cu_n}` of `e.Pz.def` is a
measurable function of the fresh shells `(n, m]` alone.**

Conditional on its binders `hR` (geometric membership of the localization cube)
and `hwD` (the zero-trace Dirichlet weak-solution property of `e.def.w`).  The
corrector family is otherwise arbitrary: no measurability, continuity or
selection property is assumed, exactly as in
`Corrector.measurable_shellIndexSigma_freshShellDirichletGradL2`. -/
theorem measurable_shellIndexSigma_cubeAverageVec_freshShellDirichletGrad [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd)
    (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      fun omega : Cutoff.ShellSeq d =>
        cubeAverageVec R (fun x => (wD omega).toH1Function.grad x) :=
  measurable_shellIndexSigma_cubeAverageVec_of_class hR _
    (fun omega => (wD omega).toH1Function.gradToHilbertVectorL2)
    (measurable_shellIndexSigma_freshShellDirichletGradL2 Q sigmaInv n m e wD hwD)
    (fun omega i =>
      coeFn_ae_coord (H1Function.coeFn_gradToHilbertVectorL2 (wD omega).toH1Function) i)

/-- **The potential average is measurable for the full sigma-algebra.**  The
plain-measurability corollary of the statement above, by
`Cutoff.shellIndexSigma_le_borel`. -/
theorem measurable_cubeAverageVec_freshShellDirichletGrad [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd)
    (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega : Cutoff.ShellSeq d =>
      cubeAverageVec R (fun x => (wD omega).toH1Function.grad x) :=
  (measurable_shellIndexSigma_cubeAverageVec_freshShellDirichletGrad hR sigmaInv n m e
    wD hwD).mono (Cutoff.shellIndexSigma_le_borel _) le_rfl

/-! ## Leg 3: the flux average of `e.Pz.def` -/

/-- Internal.  **The flux average `(grad w_N + shom^{-1} h e')_{z+cu_n}` of
`e.Pz.def` is a measurable function of the fresh shells `(n, m]` alone.**

Conditional on its binders `hR` (geometric membership of the localization cube)
and `hwN` (the mean-zero Neumann weak-solution property of `e.def.w`).

The integrand is the sum of the Neumann corrector gradient and the forcing of
`e.def.w`, so its `L^2` class is the difference of the proved Neumann gradient
class and the proved forcing class; the forcing direction and reciprocal scale
of the flux term are those `e.Pz.def` prints, while the weak-solution binder
`hwN` keeps whatever direction and scale the corrector family carries. -/
private theorem measurable_shellIndexSigma_cubeAverageVec_neumannFluxField
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd)
    (sigma : PositiveScalar) (sigmaInv : ℝ) (n m : ℤ) (e e' : Vec d)
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      fun omega : Cutoff.ShellSeq d =>
        cubeAverageVec R (neumannFluxField sigma omega n m e' (wN omega)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  refine measurable_shellIndexSigma_cubeAverageVec_of_class hR _
    (fun omega => (wN omega).gradToHilbertVectorL2 -
      freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega)
    ((measurable_shellIndexSigma_freshShellNeumannGradL2 Q sigmaInv n m e wN hwN).sub
      (measurable_freshShellForcingL2_shellIndexSigma Q ((sigma : ℝ))⁻¹ n m e'))
    fun omega i => ?_
  have hgrad : ((wN omega).gradToHilbertVectorL2 : Vec d → HilbertVec d)
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        hilbertifyVecField (wN omega).toH1Function.grad :=
    H1Function.coeFn_gradToHilbertVectorL2 (wN omega).toH1Function
  have hforc : ((freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d)
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        hilbertifyVecField
          (fun x => -streamForcing ((sigma : ℝ))⁻¹ omega n m e' x) :=
    coeFn_toHilbertVectorL2OfVecField (U := openCubeSet Q)
      (memVectorL2_openCubeSet_of_continuous Q
        (continuous_streamForcing ((sigma : ℝ))⁻¹ omega n m e').neg)
  filter_upwards [Lp.coeFn_sub ((wN omega).gradToHilbertVectorL2)
      (freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega),
    coeFn_ae_coord hgrad i, coeFn_ae_coord hforc i] with x h1 h2 h3
  change ((((wN omega).gradToHilbertVectorL2 -
      freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x) i = _
  rw [h1]
  change ((((wN omega).gradToHilbertVectorL2 : Vec d → HilbertVec d) x) i -
      (((freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x) i) = _
  rw [h2, h3]
  change (wN omega).toH1Function.grad x i -
      -(streamForcing ((sigma : ℝ))⁻¹ omega n m e' x i) = _
  rw [sub_neg_eq_add]
  rfl

/-! ## The load `P_z` of `e.Pz.def` -/

/-- Internal.  **The localized principal load `P_z` of `e.Pz.def` is a
measurable function of the fresh shells `(n, m]` alone.**

Conditional on its binders `hR`, `hwD` and `hwN`. -/
theorem measurable_shellIndexSigma_principalPz [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd)
    (sigma : PositiveScalar) (sigmaInvD sigmaInvN : ℝ) (n m : ℤ)
    (eD eN e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInvD omega n m eD x))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInvN omega n m eN x)) :
    Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      fun omega : Cutoff.ShellSeq d =>
        principalPz sigma omega n m e e' R (wD omega) (wN omega) := by
  let : MeasurableSpace (Cutoff.ShellSeq d) := Cutoff.shellIndexSigma (Set.Ioc n m)
  have hD := measurable_shellIndexSigma_cubeAverageVec_freshShellDirichletGrad
    (R := R) hR sigmaInvD n m eD wD hwD
  have hN := measurable_shellIndexSigma_cubeAverageVec_neumannFluxField
    (R := R) hR sigma sigmaInvN n m eN e' wN hwN
  have hEq : (fun omega : Cutoff.ShellSeq d =>
      principalPz sigma omega n m e e' R (wD omega) (wN omega)) =
      fun omega : Cutoff.ShellSeq d =>
        ((Real.sqrt (sigma : ℝ))⁻¹ •
            (e' + cubeAverageVec R (fun x => (wD omega).toH1Function.grad x)),
          Real.sqrt (sigma : ℝ) •
            (e + cubeAverageVec R (neumannFluxField sigma omega n m e' (wN omega)))) := by
    funext omega
    refine Prod.ext ?_ ?_
    · rw [principalPz_fst]
      rfl
    · rw [principalPz_snd]
      rfl
  rw [hEq]
  exact (measurable_const_smul_vec (measurable_const.add hD) _).prodMk
    (measurable_const_smul_vec (measurable_const.add hN) _)

/-! ## The gauged load `G_{-(h)_{z+cu_n}} P_z` -/

/-- The gauged load `G_{-(h)_{z+cu_n}} P_z`, at the shell-sequence carrier and at
the manuscript's own centering constant `freshShellCubeAverage`.

This is a definition and carries no propositional binder: `wD` and `wN` enter as
bare families, with no solution, measurability or selection property required of
them. -/
def gaugedPrincipalLoadShell (sigma : PositiveScalar) {Q : TriadicCube d}
    (R : TriadicCube d) (lowScale highScale : ℤ) (e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : Cutoff.ShellSeq d) : BlockVec d :=
  blockMatVecMul
    (blockGauge (-freshShellCubeAverage R omega lowScale highScale))
    (principalPz sigma omega lowScale highScale e e' R (wD omega) (wN omega))

/-- At a genuine cutoff sample the load above is
`PrincipalResponseIndepWire.gaugedSwitchLoad` applied to `principalPz`, i.e. the
very load `PrincipalResponseSwitchActualPerCube.switchCubeQuad` conjugates.

This identity carries no propositional binder -- it is `rfl`, the two sides
being the same term read at the two carriers. -/
theorem gaugedPrincipalLoadShell_val (sigma : PositiveScalar) {Q : TriadicCube d}
    (R : TriadicCube d) (lowScale highScale : ℤ) (e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : CutoffSample d) :
    gaugedPrincipalLoadShell sigma R lowScale highScale e e' wD wN omega.1 =
      gaugedSwitchLoad R omega lowScale highScale
        (principalPz sigma omega.1 lowScale highScale e e' R (wD omega.1)
          (wN omega.1)) :=
  rfl

/-- **The `hWmeas` input of `integral_blockQuadratic_shellSplit_eq`, at the exact
gauged load.**

The load `G_{-(h)_{z+cu_n}} P_z` is a measurable function of the fresh shells
`(n, m]` alone.  This is the literal content of the parenthetical "the latter is
a function of `k_m - k_{m-h}`".

: this statement holds only under the propositions supplied by its binders,
which are exactly three:

* `hR`, the geometric membership of the localization cube `R` in the depth-`jd`
  grid below the large cube `Q`;
* `hwD`, the zero-trace Dirichlet weak-solution property of `e.def.w` for the
  family `wD`;
* `hwN`, the mean-zero Neumann weak-solution property of `e.def.w` for the
  family `wN`.

`hwD` and `hwN` are the defining property of the correctors, not extra
assumptions about them: they are what `e.def.w` says, and at a concrete
consumer they are discharged by the produced-existence route of
`Corrector.FreshShellExistence`.  Nothing is assumed about measurability,
continuity or selection of either family.  This is a provider A, not a
source-facing frozen declaration. -/
theorem measurable_shellIndexSigma_gaugedPrincipalLoadShell [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd)
    (sigma : PositiveScalar) (sigmaInvD sigmaInvN : ℝ) (n m : ℤ)
    (eD eN e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInvD omega n m eD x))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInvN omega n m eN x)) :
    Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
      (gaugedPrincipalLoadShell sigma R n m e e' wD wN) := by
  let : MeasurableSpace (Cutoff.ShellSeq d) := Cutoff.shellIndexSigma (Set.Ioc n m)
  have hPz := measurable_shellIndexSigma_principalPz hR sigma sigmaInvD sigmaInvN n m
    eD eN e e' wD wN hwD hwN
  have hH := measurable_shellIndexSigma_freshShellCubeAverage hR (R := R) n m
  have hEq : gaugedPrincipalLoadShell sigma R n m e e' wD wN =
      fun omega : Cutoff.ShellSeq d =>
        (((principalPz sigma omega n m e e' R (wD omega) (wN omega)).1 : Vec d),
          matVecMul (-freshShellCubeAverage R omega n m)
              (principalPz sigma omega n m e e' R (wD omega) (wN omega)).1 +
            (principalPz sigma omega n m e e' R (wD omega) (wN omega)).2) := by
    funext omega
    exact blockMatVecMul_blockGauge _ _
  rw [hEq]
  exact (measurable_fst.comp hPz).prodMk
    ((measurable_matVecMul hH.neg (measurable_fst.comp hPz)).add
      (measurable_snd.comp hPz))

/-! ## The entrywise integrability of the coarse matrix -/

/-- **The `hB` input of `integral_blockQuadratic_shellSplit_eq`, at the exact
matrix, in representative form.**  Every entry of any representative `B` of
`PrincipalResponseIndepWire.switchCubeMatrix` is integrable on the
shell-sequence carrier.

Integrability is invariant under the almost-everywhere identification the
binder `hBrep` supplies, so the statement is available at every representative
that
`PrincipalResponseLowerShellMeas.exists_measurable_representative_switchCubeMatrix`
can produce, and no value of `B` off the lower-tail-good carrier is read: the
transport only ever evaluates `B` on `Subtype.val` images, and only under an
integrability statement.

The route is the carrier transport of `PrincipalResponseIndepWire`
`integral_blockMatEntry_switchCubeMatrix_eq` run on integrability instead of on
the integral: push `M.P.toMeasure` back to the cutoff-sample law along
`Subtype.val`, replace `B` by `switchCubeMatrix` using `hBrep`, push forward
along `Cutoff.coefficientCutoff` to `RegCoeffField d`, and land on
`Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix`.

That last input is itself free of good events, of `(P4)` records and of any
structural-law hypothesis: it rests only on the deterministic coercivity `nu`
through the two cutoff moment lemmas of `Cutoff. and `Cutoff.

: this statement holds only under the propositions supplied by its binders,
here exactly the representative binder `hBrep`.  In particular it carries no
ellipticity event and no good event.  It is a provider A, not a source-facing
frozen declaration. -/
theorem integrable_blockMatEntry_of_representative [NeZero d]
    (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d)
    {B : ShellSeq d → BlockMat d}
    (hBrep : ∀ᵐ w ∂(cutoffSampleLaw M).toMeasure,
      B w.val = switchCubeMatrix M lowScale R w)
    (alpha beta : BlockCoord d) :
    Integrable
      (fun omega : ShellSeq d => blockMatEntry (B omega) alpha beta)
      M.P.toMeasure := by
  have hcs : Integrable
      (fun w : CutoffSample d =>
        blockMatEntry (switchCubeMatrix M lowScale R w) alpha beta)
      (cutoffSampleLaw M).toMeasure := by
    have hmeas : AEStronglyMeasurable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
        (Measure.map (coefficientCutoff M.nu lowScale)
          (cutoffSampleLaw M).toMeasure) := by
      rw [← coefficientCutoffLaw_eq_map M lowScale]
      exact Provider.Annealed.aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
        (coefficientCutoffLaw_lawCarrier M lowScale) R alpha beta
    have h1 : Integrable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
        (Measure.map (coefficientCutoff M.nu lowScale)
          (cutoffSampleLaw M).toMeasure) := by
      rw [← coefficientCutoffLaw_eq_map M lowScale]
      exact Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M lowScale R alpha beta
    rw [integrable_map_measure hmeas
      (measurable_coefficientCutoff M.nu lowScale).aemeasurable] at h1
    refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
    exact congrArg (fun A => blockMatEntry A alpha beta)
      (coarseBlockMatrix_cubeSet_coefficientCutoff_eq M lowScale w R)
  have hemb : MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)
  rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff]
  refine hcs.congr ?_
  filter_upwards [hBrep] with w hw
  exact (congrArg (fun A => blockMatEntry A alpha beta) hw).symm

/-! ## The consumer -/

/-- **The independence factorization at the exact load, at any representative of
the exact matrix.**

Relative to `PrincipalResponseLowerShellMeas`
`integral_blockQuadratic_shellSplit_eq_of_representative`, two further inputs
are gone:

* `hWmeas` is now the theorem
  `measurable_shellIndexSigma_gaugedPrincipalLoadShell` above, at the concrete
  gauged load `G_{-(h)_{z+cu_n}} P_z`, and in its place stand only the two
  weak-solution properties of `e.def.w` that the corrector displays already
  carry.  The geometric membership `hR` that the load's cube average needs is
  the same `hR` the annealed identification already needed, so no geometric
  binder is added;
* `hB`, the entrywise integrability of the coarse matrix, is
  `integrable_blockMatEntry_of_representative` above, applied at the same
  representative binder `hBrep` this statement already carries, so it too adds
  no binder.

The matrix stays abstract: `B` and its two properties `hBmeas` and `hBrep` are
binders here, exactly as in the direct predecessor of this statement in
`PrincipalResponseLowerShellMeas`, and at the display's own matrix both are
produced together by
`PrincipalResponseLowerShellMeas.exists_measurable_representative_switchCubeMatrix`
under the geometric inclusion `cubeSet R ⊆ U`.  No value of `B` off the
lower-tail-good carrier is read.

Exactly one integrability input remains a binder here, and it is still open:
`hW`, the second-moment integrability of the gauged load.  The independence
binder `hindep` of the downstream budget wire is likewise untouched, upstream of
this file.

: this statement holds only under the propositions supplied by its binders.  It
is a provider A, not a source-facing frozen declaration. -/
theorem integral_blockQuadratic_shellSplit_eq_gaugedPrincipalLoadShell [NeZero d]
    (M : ABKModel d) (sigma : PositiveScalar) {L n m : ℤ} (hLn : L ≤ n)
    {U : Set (Vec d)} {K : ℤ} {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d K) jd)
    {B : Cutoff.ShellSeq d → BlockMat d}
    (hBmeas : ∀ alpha beta : BlockCoord d,
      Measurable[Cutoff.lowerShellLocalCompletion M L U]
        fun omega : Cutoff.ShellSeq d => blockMatEntry (B omega) alpha beta)
    (hBrep : ∀ᵐ w ∂(cutoffSampleLaw M).toMeasure,
      B w.val = switchCubeMatrix M L R w)
    (sigmaInvD sigmaInvN : ℝ) (eD eN e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d K)))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d K)) (wD omega)
        (fun x => -streamForcing sigmaInvD omega n m eD x))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d K)) (wN omega)
        (fun x => -streamForcing sigmaInvN omega n m eN x))
    (hW : ∀ alpha beta : BlockCoord d,
      Integrable
        (fun omega =>
          toFullBlockVec
              (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega) alpha *
            toFullBlockVec
              (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega) beta)
        M.P.toMeasure) :
    (∫ omega, blockVecDot (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega)
        (blockMatVecMul (B omega)
          (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega))
        ∂M.P.toMeasure) =
      ∫ omega, blockVecDot (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M L)
            (((originCube d K).scale : ℤ) - (jd : ℤ)))
          (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega))
        ∂M.P.toMeasure :=
  integral_blockQuadratic_shellSplit_eq_of_representative M hLn hR hBmeas hBrep
    (measurable_shellIndexSigma_gaugedPrincipalLoadShell hR sigma sigmaInvD sigmaInvN
      n m eD eN e e' wD wN hwD hwN)
    (fun alpha beta =>
      integrable_blockMatEntry_of_representative M L R hBrep alpha beta)
    hW

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
