/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionState
public import LeanPool.LiebThirring.Fourier.Functoriality
public import LeanPool.LiebThirring.Fourier.IntegralL2

/-!
# Fourier factorization on particle tensors

The insertion phase splits into the selected and remaining spatial phases.

The literal full-state representative of a separated particle tensor.
-/

public section

open MeasureTheory WithLp
open scoped FourierTransform SchwartzMap

namespace LiebThirring

/-- The insertion phase splits into the selected and remaining spatial phases. -/
theorem inner_insertParticle {N : ℕ} (i : Fin N) (x ξ : Position)
    (y η : OtherConfiguration i) :
    inner ℝ (insertParticle i x y) (insertParticle i ξ η) =
      inner ℝ x ξ + inner ℝ y η := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← (insertionIndexEquiv i).symm.sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    simp [insertionIndexEquiv, insertParticle]
  · apply Finset.sum_congr rfl
    rintro ⟨j, a⟩ _
    simp [insertionIndexEquiv, insertParticle, j.property]

/-- The literal full-state representative of a separated particle tensor. -/
@[expose] noncomputable def particleTensorFunction {N q : ℕ} (i : Fin N)
    (f : Position → EuclideanSpace ℂ (Fin q))
    (v : OtherConfiguration i → EuclideanSpace ℂ (OtherSpinLabels i q))
    (X : Configuration N) : SpinAmplitudes N q :=
  (spinCurryingLinearIsometryEquiv i).symm
    (tensorInsertionBilinear
      (v ((insertionMeasurableEquiv i).symm X).2)
      (f ((insertionMeasurableEquiv i).symm X).1))

/-- Exact regrouped tensor evaluation on inserted spatial coordinates. -/
theorem particleTensorFunction_insert {N q : ℕ} (i : Fin N)
    (f : Position → EuclideanSpace ℂ (Fin q))
    (v : OtherConfiguration i → EuclideanSpace ℂ (OtherSpinLabels i q))
    (x : Position) (y : OtherConfiguration i) (s : Fin q) (t : OtherSpinLabels i q) :
    particleTensorFunction i f v (insertParticle i x y) (insertSpin i s t) = f x s * v y t := by
  have he := congrArg (fun a : PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)) =>
    a s t)
    ((spinCurryingLinearIsometryEquiv (q := q) i).apply_symm_apply
      (tensorInsertionBilinear (v y) (f x)))
  rw [spinCurryingLinearIsometryEquiv_apply] at he
  unfold particleTensorFunction
  rw [← insertionMeasurableEquiv_apply i (x, y), MeasurableEquiv.symm_apply_apply]
  exact he

/-- A product of integrable spatial factors gives an integrable full tensor. -/
theorem integrable_particleTensorFunction {N q : ℕ} (i : Fin N)
    {f : Position → EuclideanSpace ℂ (Fin q)}
    {v : OtherConfiguration i → EuclideanSpace ℂ (OtherSpinLabels i q)}
    (hf : Integrable f) (hv : Integrable v) : Integrable (particleTensorFunction i f v) := by
  have hi : Integrable (fun z : Position × OtherConfiguration i =>
      tensorInsertionBilinear (v z.2) (f z.1)) := by
    exact hf.op_fst_snd (by fun_prop)
      ⟨‖(tensorInsertionBilinear (ι := Fin q) (H := EuclideanSpace ℂ (OtherSpinLabels i q))).flip‖,
        (tensorInsertionBilinear (ι := Fin q) (H := EuclideanSpace ℂ (OtherSpinLabels i
          q))).flip.le_opNorm₂⟩ hv
  have hm := (spinCurryingLinearIsometryEquiv (q := q)
    i).symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hi
  exact ((MeasurePreserving.symm (insertionMeasurableEquiv i)
    (measurePreserving_insertion i)).integrable_comp
      hm.aestronglyMeasurable).mpr hm

/-- The full Fourier integral of a separated particle tensor is the tensor of
its two Fourier integrals. -/
theorem fourier_particleTensorFunction {N q : ℕ} (i : Fin N)
    {f : Position → EuclideanSpace ℂ (Fin q)}
    {v : OtherConfiguration i → EuclideanSpace ℂ (OtherSpinLabels i q)}
    (hf : Integrable f) (hv : Integrable v) (ξ : Position) (η : OtherConfiguration i) :
    (𝓕 (particleTensorFunction i f v)) (insertParticle i ξ η) =
      particleTensorFunction i (𝓕 f) (𝓕 v) (insertParticle i ξ η) := by
  apply (spinCurryingLinearIsometryEquiv i).injective
  rw [Real.fourier_eq]
  let A := (spinCurryingLinearIsometryEquiv (q := q) i).toLinearIsometry
  change A (∫ X : Configuration N, Real.fourierChar (-inner ℝ X (insertParticle i ξ η)) •
    particleTensorFunction i f v X) = _
  rw [← A.integral_comp_comm]
  rw [← (measurePreserving_insertion i).integral_comp
    (insertionMeasurableEquiv i).measurableEmbedding]
  have heq : (fun z : Position × OtherConfiguration i =>
      A (Real.fourierChar (-inner ℝ (insertionMeasurableEquiv i z) (insertParticle i ξ η)) •
        particleTensorFunction i f v (insertionMeasurableEquiv i z))) =
      (fun z : Position × OtherConfiguration i => tensorInsertionBilinear
        (Real.fourierChar (-inner ℝ z.2 η) • v z.2)
        (Real.fourierChar (-inner ℝ z.1 ξ) • f z.1)) := by
    funext z
    change (spinCurryingLinearIsometryEquiv i)
      (Real.fourierChar (-inner ℝ (insertionMeasurableEquiv i z) (insertParticle i ξ η)) •
        particleTensorFunction i f v (insertionMeasurableEquiv i z)) = _
    simp only [Circle.smul_def]
    rw [map_smul, insertionMeasurableEquiv_apply, inner_insertParticle]
    unfold particleTensorFunction
    rw [← insertionMeasurableEquiv_apply i z, MeasurableEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    simp only [neg_add, Real.fourierChar.map_add_eq_mul,
      Circle.coe_mul, map_smul, smul_apply, smul_smul]
  rw [heq]
  change (∫ z : Position × OtherConfiguration i,
    (tensorInsertionBilinear (ι := Fin q) (H := EuclideanSpace ℂ (OtherSpinLabels i q))).flip
      (Real.fourierChar (-inner ℝ z.1 ξ) • f z.1)
      (Real.fourierChar (-inner ℝ z.2 η) • v z.2) ∂volume.prod volume) = _
  rw [integral_prod_bilin (tensorInsertionBilinear (ι := Fin q)
      (H := EuclideanSpace ℂ (OtherSpinLabels i q))).flip
    ((Real.fourierIntegral_convergent_iff ξ).mpr hf)
    ((Real.fourierIntegral_convergent_iff η).mpr hv)]
  unfold particleTensorFunction
  rw [← insertionMeasurableEquiv_apply i (ξ, η), MeasurableEquiv.symm_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Smooth factors give a strongly measurable literal tensor representative. -/
theorem stronglyMeasurable_particleTensorFunction {N q : ℕ} (i : Fin N)
    (f : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))) :
    StronglyMeasurable (particleTensorFunction i f v) := by
  have hf := f.continuous.stronglyMeasurable.comp_measurable
    (measurable_fst.comp (insertionMeasurableEquiv i).symm.measurable)
  have hv := v.continuous.stronglyMeasurable.comp_measurable
    (measurable_snd.comp (insertionMeasurableEquiv i).symm.measurable)
  exact (spinCurryingLinearIsometryEquiv (q := q) i).symm.continuous.comp_stronglyMeasurable
    ((tensorInsertionBilinear (ι := Fin q) (H := EuclideanSpace ℂ (OtherSpinLabels i
      q))).continuous₂.comp_stronglyMeasurable (hv.prodMk hf))

/-- The concrete State insertion is the literal smooth tensor almost everywhere. -/
theorem oneParticleInsertion_toLp_ae {N q : ℕ} (i : Fin N)
    (f : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))) :
    (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume) :
      Configuration N → SpinAmplitudes N q) =ᵐ[volume] particleTensorFunction i f v := by
  let ψ := oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume)
  have hnested : ∀ᵐ x : Position, ∀ᵐ y : OtherConfiguration i,
      ψ (insertParticle i x y) = particleTensorFunction i f v (insertParticle i x y) := by
    filter_upwards [oneParticleInsertion_ae i (f.toLp 2 volume) (v.toLp 2 volume),
      f.coeFn_toLp 2 volume] with x hx hf
    filter_upwards [ae_all_iff.mpr hx, v.coeFn_toLp 2 volume] with y hy hv
    apply (spinCurryingLinearIsometryEquiv i).injective
    ext s t
    rw [spinCurryingLinearIsometryEquiv_apply, spinCurryingLinearIsometryEquiv_apply,
      particleTensorFunction_insert, hy s t, hf, hv]
  have hψ := (Lp.stronglyMeasurable ψ).measurable.comp
    (measurePreserving_insertParticle i).measurable
  have hF := (stronglyMeasurable_particleTensorFunction i f v).measurable.comp
    (measurePreserving_insertParticle i).measurable
  have hprod := (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hψ hF)).mpr hnested
  have h := (MeasurePreserving.symm (insertionMeasurableEquiv i)
    (measurePreserving_insertion i)).quasiMeasurePreserving.ae hprod
  filter_upwards [h] with X hX
  simpa only [Function.comp_apply, ← insertionMeasurableEquiv_apply,
    MeasurableEquiv.apply_symm_apply] using hX

/-- Full L² Fourier carries a smooth inserted tensor to the Fourier-factor tensor. -/
theorem fourier_oneParticleInsertion_toLp {N q : ℕ} (i : Fin N)
    (f : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))) :
    𝓕 (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume)) =
      oneParticleInsertion i ((𝓕 f).toLp 2 volume) ((𝓕 v).toLp 2 volume) := by
  let ψ := oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume)
  have hψ := oneParticleInsertion_toLp_ae i f v
  have hmem : MemLp (particleTensorFunction i f v) 2 volume := (Lp.memLp ψ).ae_eq hψ
  have hclass : hmem.toLp (particleTensorFunction i f v) = ψ := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans hψ.symm
  have hfourier := Fourier.fourier_toLp_ae_eq
    (integrable_particleTensorFunction i (f.integrable (μ := volume)) (v.integrable (μ := volume)))
      hmem
  rw [hclass] at hfourier
  have hm : (𝓕 (particleTensorFunction i f v) : Configuration N → SpinAmplitudes N q) =ᵐ[volume]
      particleTensorFunction i (𝓕 f : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
        (𝓕 v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))) := by
    apply Filter.Eventually.of_forall
    intro X
    obtain ⟨z, rfl⟩ := (insertionMeasurableEquiv i).surjective X
    rw [insertionMeasurableEquiv_apply]
    exact fourier_particleTensorFunction i (f.integrable (μ := volume))
      (v.integrable (μ := volume)) z.1 z.2
  apply Lp.ext
  exact hfourier.trans (hm.trans (oneParticleInsertion_toLp_ae i (𝓕 f) (𝓕 v)).symm)

end LiebThirring
end
