/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationJointComponents
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMuMeasCell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableGradient

/-!
# LocalizationFluctuationBackgroundClass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 background's `L^2` class is measurable in the sample

ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`, the
background display.

## The obligation this module discharges

`LocalizationFluctuationJointBackground` reduced the whole `hcomp`/`hbg`
measurability front of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'` to
the single proposition

```
  omega |->  [ meshCellBackground M n h Kc e e' wD wN R omega ]
```

is measurable into `L^2(z + cu_n; R^{2d})`.  This module proves it.

## Method: the cube average cancels

The Step-2 background is `P_z + bfF_z`, and both summands carry the cube average
`(grad w)_{z+cu_n}`: `P_z` with a `+` sign (`e.Pz.def`) and `bfF_z` with a `-`
sign (`e.Fz.def`).  In the *sum* the average cancels, and
`PrincipalResponsePz.principalPz_add_principalFz` records exactly that:

```
  P_z + bfF_z(x) = bfAhom^{-1/2} ( e' + grad w_D(x); e + grad w_N(x) + shom^{-1} h e' ) .
```

So the background is `LocalizationActualBackground.localizationBackground`,
which does **not** depend on the localization cube at all, and no measurability
of any cube average is needed.

The class of that field is then built on the localization cube `cu_K`, where
the proved measurability lives, and restricted to the mesoscopic cell:

* `principalLoad_add` splits off the constant `bfAhom^{-1/2}(e'; e)`, whose class
  is the continuous linear `blockVecToHilbertBlockL2Const`
  (`LocalizationFluctuationJointComponents.toHilbertBlockL2OfBlockField_const`),
  and adding it back translates the class by that constant, which preserves
  measurability
  (`LocalizationFluctuationJointBackground.measurable_toHilbertBlockL2OfBlockField_add_const`);
* what is left is the doubled class of the pair of *scaled* corrector gradients,
  assembled by
  `LocalizationFluctuationJointComponents.measurable_toHilbertBlockL2OfComponents`
  from its two vector legs;
* each leg is a fixed scalar multiple of a proved measurable class:
  `Corrector.measurable_freshShellDirichletGradL2` for the potential leg, and
  the difference `grad w_N - (-streamForcing)` of
  `Corrector.measurable_freshShellNeumannGradL2` and
  `Corrector.measurable_freshShellForcingL2` for the flux leg;
* the passage from `cu_K` to `z + cu_n` is
  `LocalizationFluctuationJointRestrict.measurable_toHilbertBlockL2OfBlockField_of_subset`;
* the sample carrier changes from `ShellSeq d` to `CutoffSample d` along
  `measurable_subtype_coe`.

**No measurable selection occurs**: the corrector families `wD`, `wN` are
arbitrary families of weak solutions of `e.def.w`, exactly as in
`Corrector.CorrectorMeasurableGradient`, and only their gradient classes are
read.

## Main results

* `toHilbertBlockL2OfBlockField_congr`, `toHilbertVectorL2OfVecField_grad`,
  `toHilbertVectorL2OfVecField_const_smul` --- the class-algebra bookkeeping.
* `memVectorL2_meshCellBackground_potential`, `..._flux` --- the two typing
  properties, so that a consumer never has to produce them by hand.
* `measurable_toHilbertBlockL2OfBlockField_meshCellBackground` --- the class
  measurability itself, the exact statement `LocalizationFluctuationJointBackground`
  asks for.
* `measurable_doubledMuValue_meshCellBackground` (the measurability half of
  `hbg`) and `aemeasurable_doubledMuValue_meshCellBackground_add_testField`
  (`hcomp`), both in the binder shape
  `LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`
  consumes.

## Binders

Beyond the typing binders: `[NeZero d]`; the two `MeasurableSpace`/`BorelSpace`
pairs on the doubled `L^2` carriers (which every consumer in this cone carries,
`HilbertBlockL2` having no global Borel instance); the geometric membership of
the cell in the mesh below the localization cube; and the two weak-solution
properties of `e.def.w` for the corrector families.  No integrability, no
estimate, no smallness, no ellipticity and no selection occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`, the
  background display, `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## Class-algebra bookkeeping -/

/-- Two block fields that agree everywhere have the same `L^2` class. -/
theorem toHilbertBlockL2OfBlockField_congr {U : Set (Vec d)}
    {F G : Vec d → BlockVec d} (hF : MemBlockL2 U F) (hG : MemBlockL2 U G)
    (hpt : ∀ x, F x = G x) :
    toHilbertBlockL2OfBlockField hF = toHilbertBlockL2OfBlockField hG := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField hF,
    coeFn_toHilbertBlockL2OfBlockField hG] with x h1 h2
  rw [h1, h2]
  simp only [hilbertifyBlockField, hpt x]

/-- The `L^2` class of the gradient field of an `H^1` function is the proved
`gradToHilbertVectorL2`. -/
theorem toHilbertVectorL2OfVecField_grad {U : Set (Vec d)} (u : H1Function U)
    (hf : MemVectorL2 U u.grad) :
    toHilbertVectorL2OfVecField hf = u.gradToHilbertVectorL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hf,
    u.coeFn_gradToHilbertVectorL2] with x h1 h2
  rw [h1, h2]

/-- The class map commutes with a fixed scalar dilation. -/
theorem toHilbertVectorL2OfVecField_const_smul {U : Set (Vec d)} (c : ℝ)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (hcf : MemVectorL2 U (fun x => c • f x)) :
    toHilbertVectorL2OfVecField hcf = c • toHilbertVectorL2OfVecField hf := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hcf,
    MeasureTheory.Lp.coeFn_smul c (toHilbertVectorL2OfVecField hf),
    coeFn_toHilbertVectorL2OfVecField hf] with x h1 h2 h3
  rw [h1, h2]
  simp only [Pi.smul_apply]
  rw [h3]
  simp [hilbertifyVecField]

/-- A measurable family of classes stays measurable under a fixed scalar
dilation. -/
theorem measurable_toHilbertVectorL2OfVecField_const_smul {Omega : Type*}
    [MeasurableSpace Omega] {U : Set (Vec d)} (c : ℝ)
    {f : Omega → Vec d → Vec d} (hf : ∀ omega, MemVectorL2 U (f omega))
    (hcf : ∀ omega, MemVectorL2 U (fun x => c • f omega x))
    (hmeas : Measurable fun omega => toHilbertVectorL2OfVecField (hf omega)) :
    Measurable fun omega => toHilbertVectorL2OfVecField (hcf omega) := by
  have hrw : (fun omega => toHilbertVectorL2OfVecField (hcf omega))
      = fun omega => c • toHilbertVectorL2OfVecField (hf omega) := by
    funext omega
    exact toHilbertVectorL2OfVecField_const_smul c (hf omega) (hcf omega)
  rw [hrw]
  exact (continuous_const_smul c).measurable.comp hmeas

/-! ## The two legs of the background, as measurable classes on the large cube -/

/-- The potential leg of the background is the corrector gradient itself, so its
class is the proved measurable Dirichlet gradient class. -/
theorem measurable_toHilbertVectorL2OfVecField_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (eD : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -Corrector.streamForcing sigmaInv omega n m eD x))
    (hmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wD omega).toH1Function.grad) :
    Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hmem omega) := by
  have hrw : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hmem omega))
      = fun omega : ShellSeq d => (wD omega).toH1Function.gradToHilbertVectorL2 := by
    funext omega
    exact toHilbertVectorL2OfVecField_grad (wD omega).toH1Function (hmem omega)
  rw [hrw]
  exact Corrector.measurable_freshShellDirichletGradL2 Q sigmaInv n m eD wD hwD

/-- The flux leg of `e.Pz.def`/`e.Fz.def` is `grad w_N + shom^{-1} h e'`, whose
class is the difference of the proved Neumann gradient class and the proved
forcing class. -/
theorem toHilbertVectorL2OfVecField_neumannFluxField {Q : TriadicCube d}
    (sigma : PositiveScalar) (omega : ShellSeq d) (n m : ℤ) (e' : Vec d)
    (wN : H1MeanZeroFunction (openCubeSet Q))
    (hmem : MemVectorL2 (openCubeSet Q)
      (neumannFluxField sigma omega n m e' wN)) :
    toHilbertVectorL2OfVecField hmem =
      wN.toH1Function.gradToHilbertVectorL2 -
        Corrector.freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega := by
  have hforc : ((Corrector.freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d)
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        hilbertifyVecField
          (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega n m e' x) :=
    coeFn_toHilbertVectorL2OfVecField (U := openCubeSet Q)
      (Corrector.memVectorL2_openCubeSet_of_continuous Q
        (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega n m e').neg)
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hmem,
    MeasureTheory.Lp.coeFn_sub (wN.toH1Function.gradToHilbertVectorL2)
      (Corrector.freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega),
    wN.toH1Function.coeFn_gradToHilbertVectorL2, hforc]
    with x h1 h2 h3 h4
  rw [h1, h2]
  simp only [Pi.sub_apply]
  rw [h3, h4]
  apply HilbertVec.ext
  intro i
  simp [hilbertifyVecField, neumannFluxField]

/-- The flux leg's class is measurable in the sample. -/
theorem measurable_toHilbertVectorL2OfVecField_neumannFluxField
    (Q : TriadicCube d) (sigma : PositiveScalar) (sigmaInv : ℝ) (n m : ℤ)
    (eN e' : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwN : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -Corrector.streamForcing sigmaInv omega n m eN x))
    (hmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (neumannFluxField sigma omega n m e' (wN omega))) :
    Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hmem omega) := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have : SecondCountableTopology (HilbertVectorL2 (openCubeSet Q)) := inferInstance
  have hrw : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hmem omega))
      = fun omega : ShellSeq d =>
        (wN omega).toH1Function.gradToHilbertVectorL2 -
          Corrector.freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e' omega := by
    funext omega
    exact toHilbertVectorL2OfVecField_neumannFluxField sigma omega n m e' (wN omega)
      (hmem omega)
  rw [hrw]
  exact (Corrector.measurable_freshShellNeumannGradL2 Q sigmaInv n m eN wN hwN).sub
    (Corrector.measurable_freshShellForcingL2 Q ((sigma : ℝ))⁻¹ n m e')

/-! ## The background is cube-average free -/

/-- **The Step-2 background of the field-slope problem is the affine background.**
The localization cube's average enters `e.Pz.def` with a `+` and `e.Fz.def`
with a `-`, so it cancels in `P_z + bfF_z`; the resulting field does not depend
on the cell at all.  Unconditional. -/
theorem meshCellBackground_eval (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) (x : Vec d) :
    (meshCellBackground M n h Kc e e' wD wN R omega).eval x =
      principalLoad (Annealed.sigmaBar M n)
        (e' + (wD omega.val).toH1Function.grad x,
          e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
            (wN omega.val) x) := by
  change meshCellLoad M n h Kc e e' wD wN R omega +
      principalFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
        (wD omega.val) (wN omega.val) x = _
  exact principalPz_add_principalFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ))
    e e' R (wD omega.val) (wN omega.val) x

/-- The potential leg of the background, in closed form. -/
theorem meshCellBackground_potential (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    (meshCellBackground M n h Kc e e' wD wN R omega).potential =
      fun x => inverseSqrtLoad (Annealed.sigmaBar M n)
        (e' + (wD omega.val).toH1Function.grad x) := by
  funext x
  have hx := congrArg Prod.fst (meshCellBackground_eval M n h Kc e e' wD wN R omega x)
  rw [principalLoad_fst] at hx
  exact hx

/-- The flux leg of the background, in closed form. -/
theorem meshCellBackground_flux (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) :
    (meshCellBackground M n h Kc e e' wD wN R omega).flux =
      fun x => sqrtLoad (Annealed.sigmaBar M n)
        (e + neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (wN omega.val) x) := by
  funext x
  have hx := congrArg Prod.snd (meshCellBackground_eval M n h Kc e e' wD wN R omega x)
  rw [principalLoad_snd] at hx
  exact hx

/-! ## The typing properties of the background on a cell -/

/-- The affine background is vector-`L^2` on the localization cube, leg by leg.
Unconditional. -/
theorem memVectorL2_localizationBackgroundLeg (Q : TriadicCube d)
    (sigma : PositiveScalar) (omega : ShellSeq d) (n m : ℤ) (e e' : Vec d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q)
        (fun x => inverseSqrtLoad sigma (e' + wD.toH1Function.grad x)) ∧
      MemVectorL2 (openCubeSet Q)
        (fun x => sqrtLoad sigma (e + neumannFluxField sigma omega n m e' wN x)) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hD : MemVectorL2 (openCubeSet Q) (fun x => e' + wD.toH1Function.grad x) :=
    (memLp_const e').add wD.toH1Function.grad_memVectorL2
  have hflux : MemVectorL2 (openCubeSet Q) (neumannFluxField sigma omega n m e' wN) :=
    wN.toH1Function.grad_memVectorL2.add
      (Corrector.memVectorL2_openCubeSet_of_continuous Q
        (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega n m e'))
  have hN : MemVectorL2 (openCubeSet Q)
      (fun x => e + neumannFluxField sigma omega n m e' wN x) :=
    (memLp_const e).add hflux
  exact ⟨hD.const_smul ((Real.sqrt ((sigma : ℝ)))⁻¹),
    hN.const_smul (Real.sqrt ((sigma : ℝ)))⟩

/-- **The `hpot` binder of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`, as
a theorem.**  Conditional only on the geometric membership of the cell. -/
theorem memVectorL2_meshCellBackground_potential (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {jd : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) jd)
    (omega : CutoffSample d) :
    MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (meshCellBackground M n h Kc e e' wD wN R omega).potential := by
  have hTS : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      openCubeSet (originCube d Kc) := by
    rw [cubeDomain_coe]
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hbig := (memVectorL2_localizationBackgroundLeg (originCube d Kc)
    (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' (wD omega.val)
    (wN omega.val)).1
  rw [meshCellBackground_potential]
  exact hbig.mono_measure (volumeMeasureOn_mono hTS)

/-- **The `hflux` binder of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`, as
a theorem.** -/
theorem memVectorL2_meshCellBackground_flux (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Kc : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {jd : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) jd)
    (omega : CutoffSample d) :
    MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (meshCellBackground M n h Kc e e' wD wN R omega).flux := by
  have hTS : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      openCubeSet (originCube d Kc) := by
    rw [cubeDomain_coe]
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hbig := (memVectorL2_localizationBackgroundLeg (originCube d Kc)
    (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' (wD omega.val)
    (wN omega.val)).2
  rw [meshCellBackground_flux]
  exact hbig.mono_measure (volumeMeasureOn_mono hTS)

/-! ## The background's class on the localization cube -/

/-- **The affine background's `L^2` class on the localization cube is a
measurable function of the sample.**

The constant `bfAhom^{-1/2}(e'; e)` is split off by `principalLoad_add`; what
is left is the doubled class of the two *scaled* corrector gradients, whose
legs are the proved `Corrector.measurable_freshShell{Dirichlet,Neumann}GradL2`
and `Corrector.measurable_freshShellForcingL2`.

only on the two weak-solution properties of `e.def.w`; the corrector families
are otherwise arbitrary. -/
theorem measurable_toHilbertBlockL2OfBlockField_localizationBackground [NeZero d]
    (Q : TriadicCube d) (sigma : PositiveScalar) (sigmaInvD sigmaInvN : ℝ) (n m : ℤ)
    (eD eN e e' : Vec d)
    [MeasurableSpace (HilbertBlockL2 (openCubeSet Q))]
    [BorelSpace (HilbertBlockL2 (openCubeSet Q))]
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -Corrector.streamForcing sigmaInvD omega n m eD x))
    (hwN : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -Corrector.streamForcing sigmaInvN omega n m eN x))
    (hmem : ∀ omega : ShellSeq d, MemBlockL2 (openCubeSet Q)
      (blockField
        (fun x => inverseSqrtLoad sigma (e' + (wD omega).toH1Function.grad x))
        (fun x => sqrtLoad sigma
          (e + neumannFluxField sigma omega n m e' (wN omega) x)))) :
    Measurable fun omega : ShellSeq d => toHilbertBlockL2OfBlockField (hmem omega) := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have : SecondCountableTopology (HilbertVectorL2 (openCubeSet Q)) := inferInstance
  have : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  -- the two unscaled legs
  have hgD : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wD omega).toH1Function.grad :=
    fun omega => (wD omega).toH1Function.grad_memVectorL2
  have hgN : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (neumannFluxField sigma omega n m e' (wN omega)) := fun omega =>
    (wN omega).toH1Function.grad_memVectorL2.add
      (Corrector.memVectorL2_openCubeSet_of_continuous Q
        (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega n m e'))
  -- the two scaled legs
  have hpotLeg : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (fun x => (Real.sqrt ((sigma : ℝ)))⁻¹ • (wD omega).toH1Function.grad x) :=
    fun omega => (hgD omega).const_smul ((Real.sqrt ((sigma : ℝ)))⁻¹)
  have hfluxLeg : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (fun x => Real.sqrt ((sigma : ℝ)) •
        neumannFluxField sigma omega n m e' (wN omega) x) :=
    fun omega => (hgN omega).const_smul (Real.sqrt ((sigma : ℝ)))
  have hmeasPot : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hpotLeg omega) :=
    measurable_toHilbertVectorL2OfVecField_const_smul _ hgD hpotLeg
      (measurable_toHilbertVectorL2OfVecField_freshShellDirichletGrad Q sigmaInvD n m eD
        wD hwD hgD)
  have hmeasFlux : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hfluxLeg omega) :=
    measurable_toHilbertVectorL2OfVecField_const_smul _ hgN hfluxLeg
      (measurable_toHilbertVectorL2OfVecField_neumannFluxField Q sigma sigmaInvN n m eN e'
        wN hwN hgN)
  have hpair : Measurable fun omega : ShellSeq d =>
      toHilbertBlockL2OfComponents (hpotLeg omega) (hfluxLeg omega) :=
    measurable_toHilbertBlockL2OfComponents hpotLeg hfluxLeg hmeasPot hmeasFlux
  have hconst : MemBlockL2 (openCubeSet Q)
      (fun _ : Vec d => principalLoad sigma (e', e)) := memLp_const _
  have hsplit : ∀ omega : ShellSeq d, toHilbertBlockL2OfBlockField (hmem omega)
      = blockVecToHilbertBlockL2Const (U := openCubeSet Q) (principalLoad sigma (e', e))
        + toHilbertBlockL2OfComponents (hpotLeg omega) (hfluxLeg omega) := by
    intro omega
    have hpt : ∀ x : Vec d,
        blockField
            (fun y => inverseSqrtLoad sigma (e' + (wD omega).toH1Function.grad y))
            (fun y => sqrtLoad sigma
              (e + neumannFluxField sigma omega n m e' (wN omega) y)) x
          = (fun _ : Vec d => principalLoad sigma (e', e)) x +
            blockField
              (fun y => (Real.sqrt ((sigma : ℝ)))⁻¹ • (wD omega).toH1Function.grad y)
              (fun y => Real.sqrt ((sigma : ℝ)) •
                neumannFluxField sigma omega n m e' (wN omega) y) x := by
      intro x
      rw [principalLoad_eq]
      refine Prod.ext ?_ ?_ <;>
        simp only [blockField, Prod.fst_add, Prod.snd_add, inverseSqrtLoad, sqrtLoad,
          smul_add]
    rw [toHilbertBlockL2OfBlockField_add hconst
      (memBlockL2_blockField (hpotLeg omega) (hfluxLeg omega)) (hmem omega) hpt,
      toHilbertBlockL2OfBlockField_const]
    rfl
  have hrw : (fun omega : ShellSeq d => toHilbertBlockL2OfBlockField (hmem omega))
      = fun omega : ShellSeq d =>
        blockVecToHilbertBlockL2Const (U := openCubeSet Q) (principalLoad sigma (e', e))
          + toHilbertBlockL2OfComponents (hpotLeg omega) (hfluxLeg omega) :=
    funext hsplit
  rw [hrw]
  exact ((continuous_const.add continuous_id).measurable).comp hpair

/-! ## The class on a mesoscopic cell -/

/-- **The remaining obligation of `LocalizationFluctuationJointBackground`,
discharged.**

The `L^2` class of the Step-2 background `P_z + bfF_z` on the mesoscopic cell
`z + cu_n` is a measurable function of the sample.

No measurability, continuity or selection property of the correctors is
assumed, and no minimizer is chosen. -/
theorem measurable_toHilbertBlockL2OfBlockField_meshCellBackground [NeZero d]
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
    (hpot : ∀ omega : CutoffSample d,
      MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).potential)
    (hflux : ∀ omega : CutoffSample d,
      MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
        (meshCellBackground M n h Kc e e' wD wN R omega).flux) :
    Measurable fun omega : CutoffSample d =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega)) := by
  have hTS : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      openCubeSet (originCube d Kc) := by
    rw [cubeDomain_coe]
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hlegs := fun omega : ShellSeq d =>
    memVectorL2_localizationBackgroundLeg (originCube d Kc) (Annealed.sigmaBar M n)
      omega n (n + (h : ℤ)) e e' (wD omega) (wN omega)
  have hbig : ∀ omega : ShellSeq d, MemBlockL2 (openCubeSet (originCube d Kc))
      (blockField
        (fun x => inverseSqrtLoad (Annealed.sigmaBar M n)
          (e' + (wD omega).toH1Function.grad x))
        (fun x => sqrtLoad (Annealed.sigmaBar M n)
          (e + neumannFluxField (Annealed.sigmaBar M n) omega n (n + (h : ℤ)) e'
            (wN omega) x))) :=
    fun omega => memBlockL2_blockField (hlegs omega).1 (hlegs omega).2
  have hclass := measurable_toHilbertBlockL2OfBlockField_localizationBackground
    (originCube d Kc) (Annealed.sigmaBar M n) ((Annealed.sigmaBar M n : ℝ))⁻¹
    ((Annealed.sigmaBar M n : ℝ))⁻¹ n (n + (h : ℤ)) e e' e e' wD wN hwD hwN hbig
  have hrestr := measurable_toHilbertBlockL2OfBlockField_of_subset hTS hbig hclass
  have hval : Measurable (Subtype.val : CutoffSample d → ShellSeq d) :=
    measurable_subtype_coe
  have hcarrier := hrestr.comp hval
  have hcongr : (fun omega : CutoffSample d =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega)))
      = fun omega : CutoffSample d =>
        toHilbertBlockL2OfBlockField
          ((hbig omega.val).mono_measure (volumeMeasureOn_mono hTS)) := by
    funext omega
    refine toHilbertBlockL2OfBlockField_congr _ _ fun x => ?_
    refine Prod.ext ?_ ?_
    · change (meshCellBackground M n h Kc e e' wD wN R omega).potential x = _
      rw [meshCellBackground_potential]
      rfl
    · change (meshCellBackground M n h Kc e e' wD wN R omega).flux x = _
      rw [meshCellBackground_flux]
      rfl
  rw [hcongr]
  exact hcarrier

/-! ## The two consumers -/

/-- **The measurability half of the `hbg` binder of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`.**

only on the geometric membership of the cell and the two weak-solution
properties of `e.def.w`. -/
theorem measurable_doubledMuValue_meshCellBackground [NeZero d]
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
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))] :
    Measurable fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
        (meshCellBackground M n h Kc e e' wD wN R omega) :=
  measurable_doubledMuValue_meshCellCoeff_background M (n + (h : ℤ)) R
    (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR)
    (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR)
    (measurable_toHilbertBlockL2OfBlockField_meshCellBackground M n h Kc e e' wD wN
      hwD hwN hR (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR)
      (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR))

/-- **The `hcomp` binder of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`,
discharged.**  Every doubled test field on the cell is admissible at once, and no
competitor is selected. -/
theorem aemeasurable_doubledMuValue_meshCellBackground_add_testField [NeZero d]
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
    (mu : Measure (CutoffSample d)) :
    ∀ Y : DoubledField d, IsDoubledTestField (cubeDomain R) Y → AEMeasurable
      (fun omega : CutoffSample d =>
        doubledMuValue (cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h Kc e e' wD wN R omega + Y)) mu :=
  aemeasurable_doubledMuValue_meshCellCoeff_background_add_testField M (n + (h : ℤ)) R
    (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR)
    (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR)
    (measurable_toHilbertBlockL2OfBlockField_meshCellBackground M n h Kc e e' wD wN
      hwD hwN hR (memVectorL2_meshCellBackground_potential M n h Kc e e' wD wN hR)
      (memVectorL2_meshCellBackground_flux M n h Kc e e' wD wN hR)) mu

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
