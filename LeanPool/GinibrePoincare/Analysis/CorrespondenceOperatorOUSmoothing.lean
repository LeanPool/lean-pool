/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorOUSmoothing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorKilledAbsoluteContinuity
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianCoordinateLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUFunctional
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Correspondence operator OU smoothing

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_original_endpoint_absolutelyContinuous_volume`.
-/

@[expose] public section
open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem correspondenceOperator_OUVariance_pos (rate t : ℝ≥0) (hr : 0 < rate) (ht : 0 < t) :
    0<ginibreOUVariance rate t := by
  have hdec : ginibreOUDecay rate t<1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (show 0<(rate : ℝ) from hr)) ht
  have hnon := ginibreOUDecay_nonneg rate t
  have hh : 0<(ginibreOUVariance rate t : ℝ) := by rw [ginibreOUVariance_coe]; nlinarith
  exact hh

/-- Normalizing the actual scalar OU convolution gives its actual variance-one-half
Gaussian law; independence is subsequently obtained from the original path family. -/
theorem correspondenceOperator_normalized_OU_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (hr : 0 < rate) (ht : 0 < t) :
    HasLaw (fun ω => (Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹ *
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t ω) (gaussianReal 0 (1/2)) P := by
  have hv := correspondenceOperator_OUVariance_pos rate t hr ht
  have hvR : 0<(ginibreOUVariance rate t : ℝ) := hv
  have hs : Real.sqrt (2*(ginibreOUVariance rate t : ℝ))≠0 :=
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) hvR)).ne'
  have h0 := ginibreBrownianOU_zero_hasLaw B P hB rate t
  simp only [ginibreOUTransition] at h0
  have h := gaussianReal_const_mul h0 (Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹
  have he : (NNReal.mk (((Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹)^2) (sq_nonneg _))*
      ginibreOUVariance rate t = 1/2 := by
    apply NNReal.eq
    change ((Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹)^2*(ginibreOUVariance rate t : ℝ)=1/2
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  simpa only [mul_zero, he] using h

/-- The genuine independent normalized scalar OU endpoints have the full
configuration Gaussian reference law after coordinate assembly. -/
theorem correspondenceOperator_normalized_OU_configuration_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (rate t : ℝ≥0) (hr : 0 < rate) (ht : 0 < t) :
    HasLaw (fun ω => ginibreHamiltonianOUCoordinateAssembly n (fun i =>
      (Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹ *
        ginibreBrownianOU (B i) rate (Real.sqrt (rate : ℝ)) 0 t ω))
      (complexGaussianMeasure n) P := by
  let c := (Real.sqrt (2*(ginibreOUVariance rate t : ℝ)))⁻¹
  have hi := hind.comp (fun _ p => c*ginibreOUConvolutionFunctional rate t p)
    (fun _ => (ginibreOUConvolutionFunctional_measurable rate t).const_mul c)
  have hae : ∀ i, (fun ω => c*ginibreOUConvolutionFunctional rate t (fun s => B i s ω))=ᵐ[P]
      (fun ω => c*ginibreBrownianOU (B i) rate (Real.sqrt (rate : ℝ)) 0 t ω) := by
    intro i
    filter_upwards [ginibreOUConvolutionFunctional_ae_eq (B i) P (hB i) rate t] with ω hω
    rw [hω]
  have hi' := hi.congr hae
  have hl := hi'.hasLaw_pi (fun i => correspondenceOperator_normalized_OU_hasLaw
    (B i) P (hB i) rate t hr ht)
  have hm := HasLaw.comp
    (show HasLaw (ginibreHamiltonianOUCoordinateAssembly n)
      (complexGaussianMeasure n) (Measure.pi (fun _ : Fin n×Fin 2 => gaussianReal 0 (1/2))) from
      ⟨(ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.aemeasurable,
        ginibreGaussian_coordinate_assembly_law hn⟩) hl
  exact hm
/-- The literal deterministic-initial configuration OU endpoint has a translated,
nondegenerate dilation of the actual configuration Gaussian reference law. -/
theorem correspondenceOperator_OU_configuration_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (z : Configuration n) (t : ℝ≥0) (ht : 0 < t) :
    HasLaw (ginibreHamiltonianOUReferenceProcess n α z B t)
      ((complexGaussianMeasure n).map (fun x =>
        ginibreOUDecay (2*α/(n : ℝ)).toNNReal t • z +
          Real.sqrt (2*(ginibreOUVariance (2*α/(n : ℝ)).toNNReal t : ℝ)) • x)) P := by
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  have hrR : 0<2*(α : ℝ)/(n : ℝ) := by positivity
  let rate : ℝ≥0 := (2*α/(n : ℝ)).toNNReal
  have hr : 0<rate := by dsimp [rate]; exact Real.toNNReal_pos.mpr hrR
  have heRate : (rate : ℝ)=2*α/(n : ℝ) := Real.coe_toNNReal _ hrR.le
  let s := Real.sqrt (2*(ginibreOUVariance rate t : ℝ))
  have hs : s≠0 := (Real.sqrt_pos.mpr (by
    have hv : 0<(ginibreOUVariance rate t : ℝ) := correspondenceOperator_OUVariance_pos rate t hr ht
    positivity)).ne'
  let Z : (Fin n×Fin 2)→ℝ := fun p => Real.sqrt (n : ℝ)*
    (if p.2=0 then (z p.1).re else (z p.1).im)
  have hZ : ginibreHamiltonianOUCoordinateAssembly n Z=z := by
    ext j
    simp only [ginibreHamiltonianOUCoordinateAssembly, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk,
      AddHom.coe_mk, Z, show (1 : Fin 2)≠0 by decide, ite_true, ite_false]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    have hsN : (Real.sqrt (n : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hnR).ne'
    field_simp
    simpa only [mul_comm] using Complex.re_add_im (z j)
  have hl := correspondenceOperator_normalized_OU_configuration_hasLaw hn B P hB hind rate t hr ht
  let U := fun ω => ginibreHamiltonianOUCoordinateAssembly n (fun i =>
    s⁻¹*ginibreBrownianOU (B i) rate (Real.sqrt (rate : ℝ)) 0 t ω)
  let F : Configuration n→Configuration n := fun x => ginibreOUDecay rate t • z+s • x
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hmap : HasLaw F ((complexGaussianMeasure n).map F) (complexGaussianMeasure n) :=
    ⟨hF.aemeasurable, rfl⟩
  have hf := HasLaw.comp hmap hl
  apply hf.congr
  have ha := ginibreHamiltonianOUReferenceProcess_scalar_assembly hn α α.property B P hB (fun _ =>
      Z)
  filter_upwards [ha] with ω hω
  have hh := hω t
  rw [hZ] at hh
  rw [hh]
  change ginibreHamiltonianOUCoordinateAssembly n (fun i =>
    ginibreBrownianOU (B i) (2*α/(n : ℝ)) (Real.sqrt (2*α/(n : ℝ))) (Z i) (t : ℝ) ω)=F (U ω)
  have hzscalar : (fun i => ginibreBrownianOU (B i) (2*α/(n : ℝ))
      (Real.sqrt (2*α/(n : ℝ))) (Z i) (t : ℝ) ω)=
      ginibreOUDecay rate t • Z + s • (fun i =>
        s⁻¹*ginibreBrownianOU (B i) rate (Real.sqrt (rate : ℝ)) 0 t ω) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ginibreBrownianOU, drivenOUPath,
      drivenOUCorrection, ginibreOUDecay, heRate]
    field_simp
    ring
  rw [hzscalar, map_add, map_smul, map_smul, hZ]

/-- Positive-time OU endpoints are genuinely absolutely continuous with respect
to configuration Lebesgue measure, for every deterministic initial state. -/
theorem correspondenceOperator_OU_endpoint_absolutelyContinuous_volume {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (z : Configuration n) (t : ℝ≥0) (ht : 0 < t) :
    P.map (ginibreHamiltonianOUReferenceProcess n α z B t) ≪ volume := by
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  let rate : ℝ≥0 := (2*α/(n : ℝ)).toNNReal
  have hr : 0<rate := by dsimp [rate]; apply Real.toNNReal_pos.mpr; positivity
  let s := Real.sqrt (2*(ginibreOUVariance rate t : ℝ))
  have hs : s≠0 := (Real.sqrt_pos.mpr (by
    have hv : 0<(ginibreOUVariance rate t : ℝ) := correspondenceOperator_OUVariance_pos rate t hr ht
    positivity)).ne'
  let F : Configuration n→Configuration n := fun x => ginibreOUDecay rate t • z+s • x
  have hq : QuasiMeasurePreserving F (volume : Measure (Configuration n)) volume :=
    (quasiMeasurePreserving_add_left volume (ginibreOUDecay rate t • z)).comp
      (quasiMeasurePreserving_smul volume hs)
  have hgauss : complexGaussianMeasure n ≪ (volume : Measure (Configuration n)) := by
    rw [complexGaussianDensityIdentification n hn]
    exact withDensity_absolutelyContinuous _ _
  rw [(correspondenceOperator_OU_configuration_hasLaw hn α hα B P hB hind z t ht).map_eq]
  exact (hgauss.map hq.measurable).trans hq.absolutelyContinuous

/-- Every strictly positive-time actual original Ginibre transition from a
collision-free deterministic state has a Lebesgue density. -/
theorem correspondenceOperator_original_endpoint_absolutelyContinuous_volume {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (z : Configuration n) (hz : CollisionFree z) (t : ℝ≥0) (ht : 0 < t) :
    P.map (ginibreBrownianMaximalProcess n α z B t) ≪ volume := by
  have hc := correspondenceOperator_endpoint_absolutelyContinuous_OU hn B P hB hind α z hz t ht
  have hOU : (fun ω => ginibreHamiltonianOUReferenceHorizon n α z B t ω
      ⟨t, ⟨t.property, le_rfl⟩⟩) = ginibreHamiltonianOUReferenceProcess n α z B t := by
    funext ω
    change ginibreHamiltonianOUValue n α z ((t : ℝ).toNNReal)
      (ginibreBrownianFullContinuousNoise n B α ω) = _
    rw [Real.toNNReal_coe]
    rfl
  rw [hOU] at hc
  have ha : (fun ω => ginibreCanonicalJointHorizonPath α t
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω) ⟨t, ⟨t.property, le_rfl⟩⟩) =ᵐ[P]
      ginibreBrownianMaximalProcess n α z B t := by
    filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
    simpa only [Real.toNNReal_coe, ginibreBrownianMaximalProcess] using
      ginibreCanonicalJointHorizonPath_apply_of_global α t
        (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω) hω ⟨t, ⟨t.property, le_rfl⟩⟩
  rw [Measure.map_congr ha] at hc
  exact hc.trans
    (correspondenceOperator_OU_endpoint_absolutelyContinuous_volume hn α hα B P hB hind z t ht)
end
end GinibrePoincare
