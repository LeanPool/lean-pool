/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseIndepWire
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsIndep
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal

/-!
# PrincipalResponseLowerShellMeas

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The lower-shell measurability's matrix, at the actual matrix

Sources in ABK26:

* The sentence "Therefore, by independence of `bfA_{m-h}` and
  `G_{-(h)_{z+cu_n}} P_z` (the latter is a function of `k_m - k_{m-h}`),
  increasing `M` in `\eqref{e.cgamma.constraints}` if necessary,";
* `e.lower.bound.principal.one.pre` (label).

## What this module supplies

The sentence describes its matrix `bfA_{m-h}` as built from the shells at or
below `m - h`.  In this repository that description is the binder `hBmeas` of
`ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq`, namely

```
∀ a b : BlockCoord d,
  Measurable[Cutoff.lowerShellLocalCompletion M L U]
    fun omega => blockMatEntry (B omega) a b
```

and it was carried as a binder by every consumer, at an abstract `B`.  This
module supplies it at the **concrete** matrix that
`PrincipalResponseSwitchActualPerCube.switchCubeQuad` conjugates, i.e. at
`PrincipalResponseIndepWire.switchCubeMatrix`, in two carrier forms:

* `measurable_cutoffSampleLocalSigma_blockMatEntry_switchCubeMatrix`, on the
  actual cutoff-sample carrier `Cutoff.CutoffSample d`, for the local field
  `Cutoff.cutoffSampleLocalSigma M lowScale U` of any observation set `U`
  containing `cubeSet R`;
* `exists_measurable_representative_switchCubeMatrix`, on the shell-sequence
  carrier `Cutoff.ShellSeq d`: an existential statement asserting that **some**
  function `B` on that carrier is entrywise
  `Cutoff.lowerShellLocalCompletion M lowScale U`-measurable -- literally the
  `hBmeas` binder shape -- and agrees with `switchCubeMatrix` almost everywhere
  under `Cutoff.cutoffSampleLaw M`.

## The carrier step, disclosed

`switchCubeMatrix` is a function of `Cutoff.CutoffSample d`, the lower-tail-good
subtype of `Cutoff.ShellSeq d`, because the genuine lower-infinite cutoff is
defined only there.  `integral_blockQuadratic_shellSplit_eq` integrates over
`(Cutoff.ShellSeq d, M.P.toMeasure)`.  The two are bridged here by an
**existential representative** on the shell-sequence carrier, and by nothing
else that a consumer can see.

The witness used inside the proofs is a `Function.extend` of `switchCubeMatrix`
along `Subtype.val`, which has to pick some value off the lower-tail-good
carrier.  That witness and its off-carrier convention are `private` to this
module: no statement exported from this file mentions either, and no exported
statement depends on the off-carrier value.  What is exported is only the
almost-everywhere identification under `Cutoff.cutoffSampleLaw M`, so the
consumer below is quantified over an arbitrary representative and every
integral it names is invariant under that identification.

## The route

1. `Provider.BadEvents.LambdaLocal` already carries the coarse-grained energy
   `Mu (cubeSet R) (coefficientCutoff M.nu L omega).toFun` and the two diagonal
   coarse blocks of the actual cutoff as `Cutoff.cutoffSampleLocalSigma M L
   U`-measurable functions, for any `U` with `cubeSet R ⊆ U`.  The two
   off-diagonal blocks are added here by the same polarization identities
   (`coarseBlockMatrix_upperRight_apply`, `coarseBlockMatrix_lowerLeft_apply`),
   giving every `blockMatEntry` of the ambient coarse block matrix of the
   cutoff on `cubeSet R`.
2. `PrincipalResponseIndepWire.coarseBlockMatrix_cubeSet_coefficientCutoff_eq`
   identifies that ambient matrix with `switchCubeMatrix` at every sample.
3. The `Subtype.val`-comap that defines `Cutoff.cutoffSampleLocalSigma` from
   `Cutoff.lowerShellLocalCompletion` is undone set by set, and the resulting
   preimage is a.e. equal to the upstairs witness because the lower-tail-good
   carrier is of full measure.
4. The private witness is then discarded from the interface: only its
   measurability and its almost-everywhere agreement with `switchCubeMatrix`
   are exported, as the two components of an existential statement.

## What this module does NOT supply

It does not supply `hWmeas`, `hB` or `hW` of
`integral_blockQuadratic_shellSplit_eq`: the consuming statement below carries
all three as binders, each visible in its own signature.  It also carries the
representative itself and both of the representative's properties as binders,
so the only input of `integral_blockQuadratic_shellSplit_eq` that the consumer
below discharges is `hBbar`.  No measurability of `gaugedSwitchLoad`,
`blockGauge`, `freshShellCubeAverage` or `principalPz` is asserted or used
anywhere below.

It does not remove the independence binder `hindep`: that binder still stands on
`ApproximateRecurrence.PrincipalResponseBudgetWire`
`exists_smallCoupling_principalEnergy_bound_of_centering`
and on its predecessors, untouched by anything here.

## Main results

The public surface is three declarations.  The zero-extension of
`switchCubeMatrix` along `Subtype.val`, the lemma computing it on the carrier,
and its entrywise measurability are all `private`, and so is the entrywise
expectation transport; none of them is nameable from another module.

* `measurable_cutoffSampleLocalSigma_blockMatEntry_switchCubeMatrix`
* `exists_measurable_representative_switchCubeMatrix`
* `integral_blockQuadratic_shellSplit_eq_of_representative`

## References

* ABK26, (the sentence quoted above); `e.lower.bound.principal.one.pre`
  (label).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Every entry of the ambient coarse block matrix of the actual cutoff -/

/-- Internal.  Every `blockMatEntry` of the ambient coarse block matrix of the
actual coefficient cutoff on `cubeSet R` is measurable for the integral-local
information of any observation set containing `cubeSet R`.

The two diagonal blocks are `LambdaLocal`'s; the two off-diagonal blocks are the
same polarization identity, which off the diagonal carries no case split. -/
private theorem measurable_cutoffSampleLocal_blockMatEntry_coarseBlockMatrix
    (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d) {U : Set (Vec d)}
    (hRU : cubeSet R ⊆ U) (alpha beta : BlockCoord d) :
    Measurable[cutoffSampleLocalSigma M lowScale U]
      fun omega : CutoffSample d =>
        blockMatEntry
          (coarseBlockMatrix (cubeSet R)
            (coefficientCutoff M.nu lowScale omega).toFun) alpha beta := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M lowScale U
  cases alpha with
  | inl i =>
    cases beta with
    | inl j =>
      exact Provider.BadEvents.measurable_coarseB_apply_cutoffSampleLocal
        M lowScale R hRU i j
    | inr j =>
      have hEq : (fun omega : CutoffSample d =>
          blockMatEntry
            (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff M.nu lowScale omega).toFun)
            (Sum.inl i) (Sum.inr j)) =
          fun omega : CutoffSample d =>
            Mu (cubeSet R) ((Pi.single i 1, 0) + (0, Pi.single j 1))
                (coefficientCutoff M.nu lowScale omega).toFun -
              Mu (cubeSet R) (Pi.single i 1, 0)
                (coefficientCutoff M.nu lowScale omega).toFun -
              Mu (cubeSet R) (0, Pi.single j 1)
                (coefficientCutoff M.nu lowScale omega).toFun := by
        funext omega
        exact coarseBlockMatrix_upperRight_apply (cubeSet R)
          (coefficientCutoff M.nu lowScale omega).toFun i j
      rw [hEq]
      exact ((Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
            M lowScale R hRU _).sub
          (Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
            M lowScale R hRU _)).sub
        (Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
          M lowScale R hRU _)
  | inr i =>
    cases beta with
    | inl j =>
      have hEq : (fun omega : CutoffSample d =>
          blockMatEntry
            (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff M.nu lowScale omega).toFun)
            (Sum.inr i) (Sum.inl j)) =
          fun omega : CutoffSample d =>
            Mu (cubeSet R) ((0, Pi.single i 1) + (Pi.single j 1, 0))
                (coefficientCutoff M.nu lowScale omega).toFun -
              Mu (cubeSet R) (0, Pi.single i 1)
                (coefficientCutoff M.nu lowScale omega).toFun -
              Mu (cubeSet R) (Pi.single j 1, 0)
                (coefficientCutoff M.nu lowScale omega).toFun := by
        funext omega
        exact coarseBlockMatrix_lowerLeft_apply (cubeSet R)
          (coefficientCutoff M.nu lowScale omega).toFun i j
      rw [hEq]
      exact ((Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
            M lowScale R hRU _).sub
          (Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
            M lowScale R hRU _)).sub
        (Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal
          M lowScale R hRU _)
    | inr j =>
      exact Provider.BadEvents.measurable_coarseSigmaStarInv_apply_cutoffSampleLocal
        M lowScale R hRU i j

/-! ## The exact matrix, on the actual cutoff carrier -/

/-- **The lower-shell measurability's matrix, on the cutoff-sample carrier.**
Every entry of `switchCubeMatrix` -- the very coarse block matrix that
`PrincipalResponseSwitchActualPerCube.switchCubeQuad` conjugates -- is
measurable for the integral-local information at shell index `lowScale` of any
observation set `U` containing `cubeSet R`.

: this statement holds under its binders, here the geometric inclusion `hRU`.  It
is a provider A, not a source-facing frozen declaration. -/
theorem measurable_cutoffSampleLocalSigma_blockMatEntry_switchCubeMatrix [NeZero d]
    (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d) {U : Set (Vec d)}
    (hRU : cubeSet R ⊆ U) (alpha beta : BlockCoord d) :
    Measurable[cutoffSampleLocalSigma M lowScale U]
      fun omega : CutoffSample d =>
        blockMatEntry (switchCubeMatrix M lowScale R omega) alpha beta := by
  have hEq : (fun omega : CutoffSample d =>
      blockMatEntry (switchCubeMatrix M lowScale R omega) alpha beta) =
      fun omega : CutoffSample d =>
        blockMatEntry
          (coarseBlockMatrix (cubeSet R)
            (coefficientCutoff M.nu lowScale omega).toFun) alpha beta := by
    funext omega
    rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq M lowScale omega R]
  rw [hEq]
  exact measurable_cutoffSampleLocal_blockMatEntry_coarseBlockMatrix
    M lowScale R hRU alpha beta

/-! ## The same matrix on the shell-sequence carrier -/

/-- Internal.  A representative of the matrix on the shell-sequence carrier:
`switchCubeMatrix` extended along `Subtype.val` by the zero block matrix off
the lower-tail-good carrier, on which the genuine lower-infinite cutoff is
undefined.

This definition is `private`, and deliberately so: the zero value off the
carrier is a convention with no source content, and no statement exported from
this module mentions this definition or depends on that value.  The exported
interface names only an existential representative and its almost-everywhere
agreement with `switchCubeMatrix`; see
`exists_measurable_representative_switchCubeMatrix`. -/
def switchCubeMatrixShell (M : ABKModel d) (lowScale : ℤ)
    (R : TriadicCube d) :
    ShellSeq d → BlockMat d :=
  Function.extend (Subtype.val : CutoffSample d → ShellSeq d)
    (switchCubeMatrix M lowScale R)
    fun _ => { upperLeft := 0, upperRight := 0, lowerLeft := 0, lowerRight := 0 }

/-- Internal.  On every genuine cutoff sample the private shell-carrier witness
is the original `switchCubeMatrix`. -/
private theorem switchCubeMatrixShell_val (M : ABKModel d) (lowScale : ℤ)
    (R : TriadicCube d) (omega : CutoffSample d) :
    switchCubeMatrixShell M lowScale R omega.1 =
      switchCubeMatrix M lowScale R omega :=
  Subtype.coe_injective.extend_apply _ _ omega

/-- Internal.  A function measurable for the cutoff-sample local field extends
along `Subtype.val` to a function measurable for the completed lower-shell local
field.  The completion is what absorbs the null complement of the lower-tail-good
carrier; the value chosen off that carrier is irrelevant. -/
private theorem measurable_lowerShellLocalCompletion_extend {beta : Type*}
    [MeasurableSpace beta] (M : ABKModel d) (lowScale : ℤ) (U : Set (Vec d))
    {f : CutoffSample d → beta}
    (hf : Measurable[cutoffSampleLocalSigma M lowScale U] f)
    (e : ShellSeq d → beta) :
    Measurable[lowerShellLocalCompletion M lowScale U]
      (Function.extend (Subtype.val : CutoffSample d → ShellSeq d) f e) := by
  intro s hs
  obtain ⟨t, ht, hvt⟩ := MeasurableSpace.measurableSet_comap.1 (hf hs)
  obtain ⟨t0, ht0, htt0⟩ := ht
  refine ⟨t0, ht0, Filter.EventuallyEq.trans ?_ htt0⟩
  filter_upwards [ae_lowerTailGood M] with omega homega
  have hext : Function.extend (Subtype.val : CutoffSample d → ShellSeq d) f e omega =
      f ⟨omega, homega⟩ :=
    Subtype.coe_injective.extend_apply f e ⟨omega, homega⟩
  have hval : ((⟨omega, homega⟩ : CutoffSample d) ∈ f ⁻¹' s) ↔ omega ∈ t := by
    rw [← hvt]
    exact Iff.rfl
  refine propext ?_
  rw [Set.mem_preimage, hext]
  exact hval

/-- Internal.  Every entry of the private witness is measurable for
`Cutoff.lowerShellLocalCompletion M lowScale U`, the completed lower-shell local
field of any observation set `U` containing `cubeSet R`.

: this statement holds under its binders, here the geometric inclusion `hRU`. -/
private theorem measurable_lowerShellLocalCompletion_blockMatEntry_switchCubeMatrixShell
    [NeZero d] (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d)
    {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (alpha beta : BlockCoord d) :
    Measurable[lowerShellLocalCompletion M lowScale U]
      fun omega : ShellSeq d =>
        blockMatEntry (switchCubeMatrixShell M lowScale R omega) alpha beta := by
  have hbase : Measurable[lowerShellLocalCompletion M lowScale U]
      (Function.extend (Subtype.val : CutoffSample d → ShellSeq d)
        (fun w : CutoffSample d =>
          blockMatEntry (switchCubeMatrix M lowScale R w) alpha beta)
        fun _ => (0 : ℝ)) :=
    measurable_lowerShellLocalCompletion_extend M lowScale U
      (measurable_cutoffSampleLocalSigma_blockMatEntry_switchCubeMatrix
        M lowScale R hRU alpha beta) _
  refine measurable_lowerShellLocalCompletion_of_ae_eq_completion hbase ?_
  filter_upwards [ae_lowerTailGood M] with omega homega
  have hshell : switchCubeMatrixShell M lowScale R omega =
      switchCubeMatrix M lowScale R ⟨omega, homega⟩ :=
    switchCubeMatrixShell_val M lowScale R ⟨omega, homega⟩
  have hext : Function.extend (Subtype.val : CutoffSample d → ShellSeq d)
      (fun w : CutoffSample d =>
        blockMatEntry (switchCubeMatrix M lowScale R w) alpha beta)
      (fun _ => (0 : ℝ)) omega =
      blockMatEntry (switchCubeMatrix M lowScale R ⟨omega, homega⟩) alpha beta :=
    Subtype.coe_injective.extend_apply _ _ ⟨omega, homega⟩
  rw [hshell, hext]

/-! ## The public representative interface -/

/-- **The `hBmeas` input of `integral_blockQuadratic_shellSplit_eq`, at the
exact matrix, in representative form.**

There is a function `B` on the shell-sequence carrier `Cutoff.ShellSeq d` with
two properties:

* every entry of `B` is measurable for
  `Cutoff.lowerShellLocalCompletion M lowScale U`, the completed lower-shell
  local field of any observation set `U` containing `cubeSet R` -- this is
  literally the `hBmeas` binder shape of
  `ApproximateRecurrence.PrincipalResponseLegsIndep`
  `integral_blockQuadratic_shellSplit_eq`;
* `B` agrees with `PrincipalResponseIndepWire.switchCubeMatrix` almost
  everywhere under the actual pushforward law `Cutoff.cutoffSampleLaw M`, i.e.
  at almost every genuine cutoff sample.

The first property is's description of `bfA_{m-h}` -- that it is built from the
shells at or below `m - h` -- at the matrix the display actually carries; the
second says that the object so described is the display's own matrix, up to a
null set of the sample law.

Nothing is asserted about the value of a representative away from the
lower-tail-good carrier, and no consumer of this statement can read such a
value: the witness produced in the proof is `private` to this module, and the
statement quantifies over `B` existentially.

: this statement holds under its binders, here the geometric inclusion `hRU`.  It
is a provider A, not a source-facing frozen declaration. -/
theorem exists_measurable_representative_switchCubeMatrix [NeZero d]
    (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d) {U : Set (Vec d)}
    (hRU : cubeSet R ⊆ U) :
    ∃ B : ShellSeq d → BlockMat d,
      (∀ alpha beta : BlockCoord d,
          Measurable[lowerShellLocalCompletion M lowScale U]
            fun omega : ShellSeq d => blockMatEntry (B omega) alpha beta) ∧
        ∀ᵐ w ∂(cutoffSampleLaw M).toMeasure,
          B w.val = switchCubeMatrix M lowScale R w :=
  ⟨switchCubeMatrixShell M lowScale R,
    fun alpha beta =>
      measurable_lowerShellLocalCompletion_blockMatEntry_switchCubeMatrixShell
        M lowScale R hRU alpha beta,
    Filter.Eventually.of_forall (switchCubeMatrixShell_val M lowScale R)⟩

/-! ## The entrywise expectation, transported to the shell carrier -/

/-- Internal.  The shell-carrier expectation of an entry of **any**
representative is the cutoff-sample expectation of the corresponding entry of
`switchCubeMatrix`.  The transport is `Cutoff.map_cutoffSampleLaw_val` together
with `MeasureTheory.integral_map`, followed by
`MeasureTheory.integral_congr_ae` at the representative's own a.e. agreement;
the a.e.-strong measurability it needs is exactly the content of the `hB` binder
of the consumer below.

Conditional on its binders `hBrep` (the a.e. agreement) and `hmeas`. -/
private theorem integral_blockMatEntry_eq_of_representative
    (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d)
    {B : ShellSeq d → BlockMat d}
    (hBrep : ∀ᵐ w ∂(cutoffSampleLaw M).toMeasure,
      B w.val = switchCubeMatrix M lowScale R w)
    (alpha beta : BlockCoord d)
    (hmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => blockMatEntry (B omega) alpha beta)
      M.P.toMeasure) :
    (∫ omega : ShellSeq d, blockMatEntry (B omega) alpha beta
        ∂M.P.toMeasure) =
      ∫ omega : CutoffSample d,
        blockMatEntry (switchCubeMatrix M lowScale R omega) alpha beta
        ∂(cutoffSampleLaw M).toMeasure := by
  have hmap := map_cutoffSampleLaw_val M
  calc
    (∫ omega : ShellSeq d, blockMatEntry (B omega) alpha beta
        ∂M.P.toMeasure) =
        ∫ omega : ShellSeq d, blockMatEntry (B omega) alpha beta
          ∂(Measure.map (Subtype.val : CutoffSample d → ShellSeq d)
            (cutoffSampleLaw M).toMeasure) := by
      rw [hmap]
    _ = ∫ w : CutoffSample d, blockMatEntry (B w.1) alpha beta
          ∂(cutoffSampleLaw M).toMeasure :=
      MeasureTheory.integral_map measurable_subtype_coe.aemeasurable
        (by rw [hmap]; exact hmeas)
    _ = ∫ w : CutoffSample d,
          blockMatEntry (switchCubeMatrix M lowScale R w) alpha beta
          ∂(cutoffSampleLaw M).toMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hBrep] with w hw
      exact congrArg (fun A => blockMatEntry A alpha beta) hw

/-! ## The consumer -/

/-- **The independence factorization at the exact matrix, with `hBbar` supplied,
at an arbitrary representative.**

The matrix is not a concrete term of this file: it is an arbitrary
`B : Cutoff.ShellSeq d → BlockMat d` carrying the two properties that
`exists_measurable_representative_switchCubeMatrix` produces, namely the
`hBmeas` measurability and the almost-everywhere agreement with
`PrincipalResponseIndepWire.switchCubeMatrix` under `Cutoff.cutoffSampleLaw M`.
Both are binders here.  Consequently no value of `B` off the lower-tail-good
carrier is read: `hBrep` enters only through
`MeasureTheory.integral_congr_ae`, and both sides of the conclusion are
integrals of `B`.

Relative to `ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq`, exactly one of the five inputs is
gone: `hBbar` is now
`PrincipalResponseIndepWire.blockMatEntry_annealedBlockMatrixAtScale_eq_integral_switchCubeMatrix`
transported to the shell carrier along `hBrep`, and in its place stands only the
geometric membership `hR`, which also fixes the scale of the annealed matrix to
the manuscript's mesoscale `(originCube d K).scale - j`.

The independence binder `hindep` of the downstream budget wire is likewise
untouched.

: this statement holds only under the propositions supplied by its binders.  It
is a provider A, not a source-facing frozen declaration. -/
theorem integral_blockQuadratic_shellSplit_eq_of_representative [NeZero d]
    (M : ABKModel d) {L n m : ℤ} (hLn : L ≤ n) {U : Set (Vec d)}
    {K : ℤ} {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d K) j)
    {B : ShellSeq d → BlockMat d}
    (hBmeas : ∀ alpha beta : BlockCoord d,
      Measurable[lowerShellLocalCompletion M L U]
        fun omega : ShellSeq d => blockMatEntry (B omega) alpha beta)
    (hBrep : ∀ᵐ w ∂(cutoffSampleLaw M).toMeasure,
      B w.val = switchCubeMatrix M L R w)
    {W : ShellSeq d → BlockVec d}
    (hWmeas : Measurable[shellIndexSigma (Set.Ioc n m)] W)
    (hB : ∀ alpha beta : BlockCoord d,
      Integrable
        (fun omega => blockMatEntry (B omega) alpha beta)
        M.P.toMeasure)
    (hW : ∀ alpha beta : BlockCoord d,
      Integrable
        (fun omega =>
          toFullBlockVec (W omega) alpha * toFullBlockVec (W omega) beta)
        M.P.toMeasure) :
    (∫ omega, blockVecDot (W omega)
        (blockMatVecMul (B omega) (W omega))
        ∂M.P.toMeasure) =
      ∫ omega, blockVecDot (W omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M L)
            (((originCube d K).scale : ℤ) - (j : ℤ)))
          (W omega))
        ∂M.P.toMeasure :=
  integral_blockQuadratic_shellSplit_eq M hLn U hBmeas hWmeas hB hW
    (fun alpha beta => by
      rw [integral_blockMatEntry_eq_of_representative M L R hBrep alpha beta
        (hB alpha beta).aestronglyMeasurable]
      exact blockMatEntry_annealedBlockMatrixAtScale_eq_integral_switchCubeMatrix
        M L hR alpha beta)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
