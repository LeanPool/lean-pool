/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.Mollification
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.PotentialApproximation

/-!
# MollifiedPrimitive

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: mollified fields carry smooth stationary primitives

The cutoff core of part (i) of `l.approximation.stationary.by.local`
(`Algsuperdiff/Section3/Provider/Corrector/PotentialApproximation.lean`,
`exists_isPotentialZeroTraceOn_limsup_le`, ABK26) is stated on the class of
stationary fields possessing a stationary square-integrable primitive with
**smooth** spatial realizations:

`∀ᵐ ω, ContDiff ℝ ⊤ (realize φ ω) ∧ ∀ x i, ∂ᵢ (realize φ ω) x = (realize p ω x)ᵢ`.

This file shows that mollification produces members of that class outright.
For a smooth compactly supported kernel `κ` and any stationary `φ ∈ L²(Ω)`,

* `mollify κ φ` is a stationary `L²` field with `C^∞` realizations, and
* its spatial gradient is again a stationary `L²` field, namely
  `mollifyGrad κ φ`, whose `i`th component is the mollification of `φ` by the
  `i`th partial derivative `∂ᵢκ` of the kernel.

The gradient identity is the convolution derivative `∂ᵢ(κ ⋆ u) = (∂ᵢκ) ⋆ u`,
which holds at *every* point, so no almost-everywhere upgrade in the space
variable is needed.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### Partial derivatives of a smoothing kernel -/

section Kernel

variable {d : ℕ}

/-- The `i`th partial derivative of a smoothing kernel. -/
def kernelDeriv (κ : Vec d → ℝ) (i : Fin d) : Vec d → ℝ :=
  fun y => fderiv ℝ κ y (basisVec i)

theorem continuous_kernelDeriv {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) :
    Continuous (kernelDeriv κ i) :=
  (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
    (hκ.continuous_fderiv (by simp))

theorem hasCompactSupport_kernelDeriv {κ : Vec d → ℝ} (hκc : HasCompactSupport κ) (i : Fin d) :
    HasCompactSupport (kernelDeriv κ i) :=
  (hκc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) rfl

theorem integrable_kernelDeriv {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) :
    Integrable (kernelDeriv κ i) volume :=
  (continuous_kernelDeriv hκ i).integrable_of_hasCompactSupport
    (hasCompactSupport_kernelDeriv hκc i)

/-- **The directional derivative of a convolution falls on the kernel.**  This is
Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right` transported through
`convolution_flip` and `convolution_precompR_apply`. -/
theorem fderiv_convolution_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {u : Vec d → E} (hu : LocallyIntegrable u volume)
    (x : Vec d) (i : Fin d) :
    fderiv ℝ (convolution κ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (basisVec i)
      = convolution (kernelDeriv κ i) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  set L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have hflip : convolution κ u L volume = convolution u κ L.flip volume :=
    (convolution_flip (L := L) (f := κ) (g := u) (μ := volume)).symm
  have hderiv : HasFDerivAt (convolution u κ L.flip volume)
      ((convolution u (fderiv ℝ κ) (L.flip.precompR (Vec d)) volume) x) x :=
    hκc.hasFDerivAt_convolution_right L.flip hu (hκ.of_le (by simp)) x
  have hfd : fderiv ℝ (convolution κ u L volume) x
      = (convolution u (fderiv ℝ κ) (L.flip.precompR (Vec d)) volume) x := by
    rw [hflip]
    exact hderiv.fderiv
  rw [hfd]
  rw [convolution_precompR_apply (L := L.flip) hu (hκc.fderiv ℝ)
    (hκ.continuous_fderiv (by simp)) x (basisVec i)]
  exact congrFun (convolution_flip (L := L) (f := kernelDeriv κ i) (g := u) (μ := volume)) x

end Kernel

/-! ### The mollified gradient -/

section Grad

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The spatial gradient of a mollified scalar field, as a stationary field:
its `i`th component is the mollification of `φ` by `∂ᵢκ`. -/
def mollifyGrad (κ : Vec d → ℝ) (φ : Ω → ℝ) (ω : Ω) : HilbertVec d :=
  HilbertVec.ofVec fun i => mollify (kernelDeriv κ i) φ ω

theorem mollifyGrad_toVec (κ : Vec d → ℝ) (φ : Ω → ℝ) (ω : Ω) (i : Fin d) :
    (mollifyGrad κ φ ω).toVec i = mollify (kernelDeriv κ i) φ ω := rfl

theorem realize_mollifyGrad_toVec (κ : Vec d → ℝ) (φ : Ω → ℝ) (ω : Ω) (x : Vec d) (i : Fin d) :
    (realize (d := d) (mollifyGrad κ φ) ω x).toVec i
      = realize (d := d) (mollify (kernelDeriv κ i) φ) ω x := rfl

/-- **The gradient identity for a mollified field.**  At every point of space,
the `i`th partial derivative of the realization of `mollify κ φ` is the
realization of the `i`th component of `mollifyGrad κ φ`. -/
theorem fderiv_realize_mollify {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ} {ω : Ω}
    (hloc : LocallyIntegrable (realize (d := d) φ ω) volume) (x : Vec d) (i : Fin d) :
    fderiv ℝ (realize (d := d) (mollify κ φ) ω) x (basisVec i)
      = (realize (d := d) (mollifyGrad κ φ) ω x).toVec i := by
  rw [realize_mollifyGrad_toVec, realize_mollify, realize_mollify]
  exact fderiv_convolution_apply hκc hκ hloc x i

end Grad

/-! ### The dense class: mollified fields satisfy the primitive hypothesis -/

section DenseClass

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
/-- The mollified gradient is a measurable field. -/
theorem stronglyMeasurable_mollifyGrad {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) :
    StronglyMeasurable (mollifyGrad (Ω := Ω) κ φ) := by
  have hcomp : ∀ i : Fin d, StronglyMeasurable (mollify (Ω := Ω) (kernelDeriv κ i) φ) :=
    fun i => stronglyMeasurable_mollify (continuous_kernelDeriv hκ i) hφm
  have hvec : Measurable fun ω : Ω => (fun i => mollify (kernelDeriv κ i) φ ω : Vec d) :=
    Measurable.of_eval fun i => (hcomp i).measurable
  exact ((HilbertVec.continuousLinearEquivVec d).symm.continuous).comp_stronglyMeasurable
    hvec.stronglyMeasurable

/-- The mollified gradient stays in the stationary `L²` layer. -/
theorem memLp_two_mollifyGrad {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ 2 μ) :
    MemLp (mollifyGrad (Ω := Ω) κ φ) 2 μ := by
  have hcomp : ∀ i : Fin d, MemLp (mollify (Ω := Ω) (kernelDeriv κ i) φ) 2 μ :=
    fun i => memLp_two_mollify (continuous_kernelDeriv hκ i)
      (integrable_kernelDeriv hκc hκ i) hφm hφ
  have hmeas := stronglyMeasurable_mollifyGrad (Ω := Ω) hκ hφm
  refine (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 ?_
  have hsum : Integrable
      (fun ω => ∑ i : Fin d, (mollify (Ω := Ω) (kernelDeriv κ i) φ ω) ^ 2) μ :=
    integrable_finsetSum _ fun i _ =>
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_mollify (continuous_kernelDeriv hκ i) hφm).aestronglyMeasurable).1
        (hcomp i) |>.congr (Filter.Eventually.of_forall fun ω => by
          change ‖mollify (kernelDeriv κ i) φ ω‖ ^ 2 = mollify (kernelDeriv κ i) φ ω ^ 2
          rw [Real.norm_eq_abs, sq_abs])
  refine hsum.congr (Filter.Eventually.of_forall fun ω => ?_)
  change (∑ i : Fin d, mollify (kernelDeriv κ i) φ ω ^ 2) = ‖mollifyGrad κ φ ω‖ ^ 2
  rw [HilbertVec.norm_sq_eq_sum_sq]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The dense class of part (i).**  Every mollification of a stationary `L²`
scalar field is a stationary `L²` field whose realizations are smooth and whose
spatial gradient is the stationary `L²` field `mollifyGrad κ φ`.  This is
exactly the hypothesis package `hprim` of
`exists_isPotentialZeroTraceOn_limsup_le`. -/
theorem ae_smooth_primitive_mollify {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ 2 μ) :
    ∀ᵐ ω ∂μ, ContDiff ℝ (⊤ : ℕ∞) (realize (d := d) (mollify κ φ) ω) ∧
      ∀ (x : Vec d) (i : Fin d),
        fderiv ℝ (realize (d := d) (mollify κ φ) ω) x (basisVec i)
          = (realize (d := d) (mollifyGrad κ φ) ω x).toVec i := by
  filter_upwards [ae_locallyIntegrable_realize (d := d) (μ := μ) hφm hφ] with ω hloc
  refine ⟨?_, fun x i => fderiv_realize_mollify hκc hκ hloc x i⟩
  rw [realize_mollify]
  exact hκc.contDiff_convolution_left _ hκ hloc

end DenseClass

end

end Algsuperdiff.Section3.Provider.Corrector
