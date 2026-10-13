/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.FreshShellSumWeakBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCorrectorLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence

/-!
# ShellSumConsumerTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shell-sum corrector limit at the recurrence consumer's data

ABK26, `e.def.w` and `e.perturb.assumption`.

`Algsuperdiff/Section3/Provider/Corrector/ShellSumCorrectorLimit.lean` proves the
corrector limit at the shell-sum law `shellSumValuePathLaw M.P n m` on the
compact-open carrier, in the *Helmholtz* shape
(`IsPotentialZeroTraceOn` / `IsSolenoidalOn` and the Neumann pair), at the
forcing `realize (valuePathForcing e)`.

The recurrence consumer
(`Provider/Diffusivity/ApproximateRecurrence/LocalizationRecurrenceMesh.lean`)
presents the same data in three different shapes:

* it forces with `Corrector.streamForcing σ⁻¹ ω.val (m−h) m e`, a function of a
  *shell sequence*, not of a continuous path;
* it works with `ω : CutoffSample d`, the **subtype** of lower-tail-good
  sequences, under `cutoffSampleLaw M`, not with `M.P` and not with the path
  law;
* it states the two corrector equations in the *weak-solution* shape
  `IsZeroTraceDirichletRhsWeakSolution` / `IsMeanZeroNeumannRhsWeakSolution`.

This module removes all three differences.

## What is supplied

* `toVec_realize_valuePathForcing_shellSumValuePath` — the **forcing
  identification**: the realization of the path forcing at the increment path is
  literally the consumer's `streamForcing`, with the gauge `σ⁻¹` carried by the
  direction.  Both sides are `matVecMul (finiteShellIncrement ω n m (x + ·)) e`,
  so the proof is a normalization of `matVecMul` in the second argument.
* `map_shellSumValuePath_cutoffSampleLaw` — the **law transport**: the law of the
  increment path under the *subtype* law `cutoffSampleLaw M` is the shell-sum
  law `shellSumValuePathLaw M.P n m`.  The subtype inclusion is null-conull for
  `M.P` (`Cutoff.map_cutoffSampleLaw_val`), so the two laws coincide; no new
  assumption enters.
* `tendsto_integral_cutoffSample_cubeAverage_dirichlet_neumann_shellSum` — the
  corrector limit with the sample integral taken over `CutoffSample d` against
  `cutoffSampleLaw M`, i.e. at the consumer's carrier.
* `tendsto_integral_cutoffSample_cubeAverage_of_weakSolutions` — the same, with
  the two corrector equations entered in the consumer's *weak-solution* shape
  and the consumer's own forcing `streamForcing σ⁻¹ ω.val n m e`.

## The shape of the corrector families

The corrector families below are indexed by the **increment path**, not by the
sample: `wD : ℕ → C(Vec d, Mat d) → H10Function …`.  That is the honest reading
of `e.def.w`, whose right-hand side depends on the sample only through
`k_m − k_{m−h}`; it is also what makes the sample integral computable, since the
integrand is then a pullback along `shellSumValuePath n m ∘ Subtype.val` and
`map_shellSumValuePath_cutoffSampleLaw` applies.  No uniqueness or solvability
theorem is used or needed.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The forcing identification -/

private theorem matVecMul_smul_right (A : Mat d) (c : ℝ) (e : Vec d) :
    matVecMul A (c • e) = c • matVecMul A e := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The recurrence consumer's forcing is the realization of the path
forcing.**

`Corrector.streamForcing c ω n m e` is `c • (k_m − k_n)(·) e`, and the
realization of `valuePathForcing (c • e)` at the increment path is
`(k_m − k_n)(· + 0) (c • e)`; the two agree because `matVecMul` is linear in its
vector argument.  The gauge `σ_{m−h}^{-1}` of the consumer is therefore carried
by the *direction*, at no cost. -/
theorem toVec_realize_valuePathForcing_shellSumValuePath (c : ℝ) (e : Vec d)
    (n m : ℤ) (omega : ShellSeq d) (x : Vec d) :
    (realize (valuePathForcing (c • e)) (shellSumValuePath n m omega) x).toVec
      = Algsuperdiff.Section3.Provider.Diffusivity.Corrector.streamForcing
          c omega n m e x := by
  show HilbertVec.toVec (HilbertVec.ofVec
      (matVecMul (((x +ᵥ shellSumValuePath n m omega) : C(Vec d, Mat d)) 0) (c • e)))
    = c • matVecMul (finiteShellIncrement omega n m x) e
  rw [HilbertVec.toVec_ofVec, ShellField.vadd_apply, zero_add,
    shellSumValuePath_apply, matVecMul_smul_right]

/-- The realization of the path forcing is continuous in space, at every path.
This discharges the `MemVectorL2` binder of the weak/Helmholtz bridge. -/
theorem continuous_toVec_realize_valuePathForcing (e : Vec d)
    (f : C(Vec d, Mat d)) :
    Continuous fun x : Vec d =>
      (realize (valuePathForcing e) f x).toVec := by
  have hvadd : Continuous fun x : Vec d => (x +ᵥ f : C(Vec d, Mat d)) :=
    ShellField.continuous_vadd_joint.comp (continuous_id.prodMk continuous_const)
  exact (HilbertVec.continuousLinearEquivVec d).continuous.comp
    ((continuous_valuePathForcing e).comp hvadd)

/-! ### The subtype law transports to the shell-sum law -/

/-- **The `CutoffSample`/`ShellSeq` law transport.**

The law of the finite shell increment, read on the *subtype* of lower-tail-good
sequences under `cutoffSampleLaw M`, is the shell-sum law of
`ShellSumCarrierLaw.lean`.  The only input is
`Cutoff.map_cutoffSampleLaw_val`, i.e. that the good set is conull for `M.P`. -/
theorem map_shellSumValuePath_cutoffSampleLaw (M : ABKModel d) (n m : ℤ) :
    Measure.map (fun omega : CutoffSample d => shellSumValuePath n m omega.val)
        (cutoffSampleLaw M).toMeasure
      = (shellSumValuePathLaw M.P n m).toMeasure := by
  rw [shellSumValuePathLaw_toMeasure, ← map_cutoffSampleLaw_val M,
    Measure.map_map (measurable_shellSumValuePath n m) measurable_subtype_coe]
  rfl

/-- The measure-preserving form of the law transport. -/
theorem measurePreserving_shellSumValuePath_cutoffSample (M : ABKModel d) (n m : ℤ) :
    MeasurePreserving (fun omega : CutoffSample d => shellSumValuePath n m omega.val)
      (cutoffSampleLaw M).toMeasure (shellSumValuePathLaw M.P n m).toMeasure :=
  ⟨(measurable_shellSumValuePath n m).comp measurable_subtype_coe,
    map_shellSumValuePath_cutoffSampleLaw M n m⟩

/-- Integrals of pullbacks along the increment path are computed at the
shell-sum law. -/
theorem integral_cutoffSample_comp_shellSumValuePath (M : ABKModel d) (n m : ℤ)
    {G : C(Vec d, Mat d) → ℝ} (hG : AEStronglyMeasurable G
      (shellSumValuePathLaw M.P n m).toMeasure) :
    ∫ omega : CutoffSample d, G (shellSumValuePath n m omega.val)
        ∂(cutoffSampleLaw M).toMeasure
      = ∫ f, G f ∂(shellSumValuePathLaw M.P n m).toMeasure := by
  rw [← map_shellSumValuePath_cutoffSampleLaw M n m] at hG ⊢
  exact (integral_map
    ((measurable_shellSumValuePath n m).comp measurable_subtype_coe).aemeasurable hG).symm

/-! ### The corrector limit at the consumer's carrier -/

/-- **`l.corrector.limit` at the shell-sum forcing, with the sample integral
taken over the consumer's carrier.**

Same statement as
`tendsto_integral_cubeAverage_dirichlet_neumann_shellSum`, with the ambient
sample space `C(Vec d, Mat d)` replaced by `CutoffSample d` under
`cutoffSampleLaw M` — the carrier the recurrence consumer integrates over.  The
corrector families are indexed by the increment path, which is what `e.def.w`
gives. -/
theorem tendsto_integral_cutoffSample_cubeAverage_dirichlet_neumann_shellSum
    (M : ABKModel d) (e : Vec d) (n m : ℤ)
    {Dfam Nfam : ℕ → C(Vec d, Mat d) → (Vec d → Vec d)}
    (hDm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot (Dfam K f x) (Dfam K f x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hNm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot (Nfam K f x) (Nfam K f x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hDpot : ∀ K : ℕ, ∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsPotentialZeroTraceOn (openCubeSet (originCube d (K : ℤ))) (Dfam K f))
    (hDsol : ∀ K : ℕ, ∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsSolenoidalOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Dfam K f x + (realize (valuePathForcing e) f x).toVec)
    (hNpot : ∀ K : ℕ, ∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsPotentialOn (openCubeSet (originCube d (K : ℤ))) (Nfam K f))
    (hNsol : ∀ K : ℕ, ∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Nfam K f x + (realize (valuePathForcing e) f x).toVec) :
    Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
        cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot (Dfam K (shellSumValuePath n m omega.val) x)
            (Dfam K (shellSumValuePath n m omega.val) x))
        ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
        (nhds (∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure))
      ∧ Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
          cubeAverage (originCube d (K : ℤ))
            (fun x => vecDot (Nfam K (shellSumValuePath n m omega.val) x)
              (Nfam K (shellSumValuePath n m omega.val) x))
          ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
          (nhds (∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
            ∂(shellSumValuePathLaw M.P n m).toMeasure)) := by
  obtain ⟨hD, hN⟩ := tendsto_integral_cubeAverage_dirichlet_neumann_shellSum M e n m
    hDpot hDsol hNpot hNsol
  refine ⟨?_, ?_⟩
  · refine hD.congr fun K => ?_
    exact (integral_cutoffSample_comp_shellSumValuePath
      (G := fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot (Dfam K f x) (Dfam K f x)) M n m (hDm K)).symm
  · refine hN.congr fun K => ?_
    exact (integral_cutoffSample_comp_shellSumValuePath
      (G := fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot (Nfam K f x) (Nfam K f x)) M n m (hNm K)).symm

/-- **The corrector limit at the consumer's weak-solution data.**

The corrector equations are entered in the shape the recurrence consumer
produces — `IsZeroTraceDirichletRhsWeakSolution 1 (openCubeSet □_K) (wD K f) (−𝐟)`
and its mean-zero Neumann counterpart — rather than in the Helmholtz shape; the
translation is `FreshShellSumWeakBridge`.  At an increment path the forcing `𝐟`
here *is* the consumer's `Corrector.streamForcing c ω n m e`, by
`toVec_realize_valuePathForcing_shellSumValuePath`, so the consumer's gauge
`σ_{m−h}^{-1}` enters as the scalar `c` and needs no separate step. -/
theorem tendsto_integral_cutoffSample_cubeAverage_of_weakSolutions
    (M : ABKModel d) (c : ℝ) (e : Vec d) (n m : ℤ)
    (wD : ∀ K : ℕ, C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : ∀ K : ℕ,
      C(Vec d, Mat d) → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hDm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot ((wD K f).toH1Function.grad x) ((wD K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hNm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot ((wN K f).toH1Function.grad x) ((wN K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hD : ∀ (K : ℕ) (f : C(Vec d, Mat d)),
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (wD K f)
        (fun x => -(realize (valuePathForcing (c • e)) f x).toVec))
    (hN : ∀ (K : ℕ) (f : C(Vec d, Mat d)),
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (wN K f)
        (fun x => -(realize (valuePathForcing (c • e)) f x).toVec)) :
    Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
        cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot
            ((wD K (shellSumValuePath n m omega.val)).toH1Function.grad x)
            ((wD K (shellSumValuePath n m omega.val)).toH1Function.grad x))
        ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
        (nhds (∫ f, ‖shellSumCorrectorRepr M (c • e) n m f‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure))
      ∧ Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
          cubeAverage (originCube d (K : ℤ))
            (fun x => vecDot
              ((wN K (shellSumValuePath n m omega.val)).toH1Function.grad x)
              ((wN K (shellSumValuePath n m omega.val)).toH1Function.grad x))
          ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
          (nhds (∫ f, ‖shellSumCorrectorRepr M (c • e) n m f‖ ^ 2
            ∂(shellSumValuePathLaw M.P n m).toMeasure)) := by
  have hmem : ∀ (K : ℕ) (f : C(Vec d, Mat d)),
      MemVectorL2 (openCubeSet (originCube d (K : ℤ)))
        (fun x => (realize (valuePathForcing (c • e)) f x).toVec) := fun K f =>
    Algsuperdiff.Section3.Provider.Diffusivity.Corrector.memVectorL2_openCubeSet_of_continuous
      (originCube d (K : ℤ)) (continuous_toVec_realize_valuePathForcing (c • e) f)
  refine tendsto_integral_cutoffSample_cubeAverage_dirichlet_neumann_shellSum M
    (c • e) n m (Dfam := fun K f => (wD K f).toH1Function.grad)
    (Nfam := fun K f => (wN K f).toH1Function.grad)
    hDm hNm (fun K => Filter.Eventually.of_forall fun f => ?_)
    (fun K => Filter.Eventually.of_forall fun f => ?_)
    (fun K => Filter.Eventually.of_forall fun f => ?_)
    (fun K => Filter.Eventually.of_forall fun f => ?_)
  · exact (wD K f).isPotentialZeroTraceOn
  · exact isSolenoidalOn_grad_add_of_isZeroTraceDirichletRhsWeakSolution_one
      (hmem K f) (hD K f)
  · exact (wN K f).toH1Function.isPotentialOn
  · have :=
      Algsuperdiff.Section3.Provider.Diffusivity.Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet
        (originCube d (K : ℤ))
    exact isSolenoidalZeroNormalTraceOn_grad_add_of_isMeanZeroNeumannRhsWeakSolution_one
      (hmem K f) (hN K f)

end

end Algsuperdiff.Section3.Provider.Corrector
