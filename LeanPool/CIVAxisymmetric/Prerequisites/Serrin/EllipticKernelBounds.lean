/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Ball integral of the Newtonian kernel gradient

The gradient `∂ₗN` of the Newtonian kernel is bounded by `(4π)⁻¹` times the Euclidean-norm
power `|z|^{-2}`, so its integral over the Euclidean ball `{y : |y - x| ≤ ρ}` is absolutely
convergent and scales linearly in `ρ`: `∫_{|y-x|≤ρ} |∂ₗN(x - y)| ≤ Cρ`. The scaling identity
`∫_{|z|≤ρ} |z|^{-2} = ρ · ∫_{|z|≤1} |z|^{-2}` is obtained from the Haar-measure scaling formula
`∫ f(c • z) dz = |c|^{-n} ∫ f(z) dz` applied to the indicator of the unit ball. This is an elliptic
kernel estimate of the interior estimates of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section

namespace CIV



private theorem abs_neg_mul_rpow_nonneg (a b : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    |(-a * b * X)| = |a| * |b| * X := by
  rw [show -a * b * X = -(a * b * X) from by ring, abs_neg, abs_mul, abs_mul, abs_of_nonneg hX]

private theorem abs_spatialDeriv_newtonianKernel_le_euclidean {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |spatialDeriv newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
  rw [newtonianKernel_spatialDeriv_formula hz i]
  have hqi : q z ^ (-(3 : ℝ) / 2) = vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
    rw [q_eq_vec3Norm_sq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) from by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) from by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  rw [hqi]
  have hzpos : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hz0
    exact hz ((WithLp.toLp_eq_zero 2).mp hz0)
  have hnn3 : 0 ≤ vec3EuclideanNorm z ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg (vec3EuclideanNorm_nonneg z) _
  rw [abs_neg_mul_rpow_nonneg (4 * Real.pi)⁻¹ (z i) hnn3]
  have hcoord : |z i| ≤ vec3EuclideanNorm z := abs_apply_le_vec3EuclideanNorm z i
  have hstep : vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
      vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    have h1 : vec3EuclideanNorm z ^ (1 : ℝ) * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
        vec3EuclideanNorm z ^ ((1 : ℝ) + -(3 : ℝ)) := (Real.rpow_add hzpos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    norm_num
  calc |(4 * Real.pi)⁻¹| * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
      |(4 * Real.pi)⁻¹| * vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)) hnn3
    _ = (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
        ring
    _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by rw [hstep]

/-! ## Part 2: integrability and the scaling identity on the Euclidean ball -/

private theorem isCompact_euclideanClosedBall {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
  rw [← closure_vec3Ball hρ]
  exact isCompact_closure_vec3Ball hρ

private theorem vec3EuclideanNorm_rpow_neg_two_eq (z : Vec3) :
    vec3EuclideanNorm z ^ (-(2 : ℝ)) = (vec3EuclideanNorm z ^ 2)⁻¹ := by
  rw [Real.rpow_neg (vec3EuclideanNorm_nonneg z),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

private theorem locallyIntegrable_vec3EuclideanNorm_rpow_neg_two :
    LocallyIntegrable (fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ))) volume := by
  have hbound : ∀ᵐ z : Vec3 ∂volume, ‖vec3EuclideanNorm z ^ (-(2 : ℝ))‖ ≤ 1 * ‖z‖ ^ (-(2 : ℝ)) := by
    filter_upwards [Measure.ae_ne volume (0 : Vec3)] with z hz
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (vec3EuclideanNorm_nonneg z) _)]
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (space_norm_le_euclideanNorm z)
      (by norm_num)
  have hmeas : AEStronglyMeasurable (fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ))) volume := by
    have heq : (fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ))) =
        fun z : Vec3 => (vec3EuclideanNorm z ^ 2)⁻¹ :=
      funext vec3EuclideanNorm_rpow_neg_two_eq
    rw [heq]
    have hcont : Continuous (fun z : Vec3 => vec3EuclideanNorm z) := by
      unfold vec3EuclideanNorm; fun_prop
    exact (hcont.measurable.pow_const 2 |>.inv).aestronglyMeasurable
  exact locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
    (by norm_num) hbound hmeas

private theorem integrableOn_vec3EuclideanNorm_rpow_neg_two {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ)))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
  have hshift : IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} :=
    isCompact_euclideanClosedBall hρ
  exact locallyIntegrable_vec3EuclideanNorm_rpow_neg_two.integrableOn_isCompact hshift

private theorem isCompact_euclideanClosedBall₀ {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact {z : Vec3 | vec3EuclideanNorm z ≤ ρ} := by
  have h := isCompact_euclideanClosedBall (x := (0 : Vec3)) hρ
  simpa using h

private theorem integral_euclideanBall_rpow_scale {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ ρ}, vec3EuclideanNorm z ^ (-(2 : ℝ)) =
      ρ * ∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ 1}, vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
  set f : Vec3 → ℝ := {w : Vec3 | vec3EuclideanNorm w ≤ 1}.indicator
    (fun w => vec3EuclideanNorm w ^ (-(2 : ℝ))) with hfdef
  have hpt : ∀ z : Vec3, f (ρ⁻¹ • z) =
      ρ ^ 2 * {w : Vec3 | vec3EuclideanNorm w ≤ ρ}.indicator
        (fun w => vec3EuclideanNorm w ^ (-(2 : ℝ))) z := by
    intro z
    have hnormeq : vec3EuclideanNorm (ρ⁻¹ • z) = ρ⁻¹ * vec3EuclideanNorm z := by
      rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
    have hmemiff : vec3EuclideanNorm (ρ⁻¹ • z) ≤ 1 ↔ vec3EuclideanNorm z ≤ ρ := by
      rw [hnormeq, inv_mul_le_iff₀ hρ, mul_one]
    by_cases hz : vec3EuclideanNorm z ≤ ρ
    · have hz1 : ρ⁻¹ • z ∈ {w : Vec3 | vec3EuclideanNorm w ≤ 1} := hmemiff.mpr hz
      have hz' : z ∈ {w : Vec3 | vec3EuclideanNorm w ≤ ρ} := hz
      have hval : vec3EuclideanNorm (ρ⁻¹ • z) ^ (-(2 : ℝ)) =
          ρ ^ 2 * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
        rw [hnormeq, Real.mul_rpow (by positivity) (vec3EuclideanNorm_nonneg z)]
        have hρrpow : (ρ⁻¹ : ℝ) ^ (-(2 : ℝ)) = ρ ^ (2 : ℝ) := by
          rw [Real.inv_rpow hρ.le, Real.rpow_neg hρ.le, inv_inv]
        rw [hρrpow, show (ρ : ℝ) ^ (2 : ℝ) = ρ ^ 2 from by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]]
      rw [hfdef, Set.indicator_of_mem hz1, Set.indicator_of_mem hz', hval]
    · have hz1 : ρ⁻¹ • z ∉ {w : Vec3 | vec3EuclideanNorm w ≤ 1} := fun h => hz (hmemiff.mp h)
      have hz' : z ∉ {w : Vec3 | vec3EuclideanNorm w ≤ ρ} := hz
      rw [hfdef, Set.indicator_of_notMem hz1, Set.indicator_of_notMem hz', mul_zero]
  have hcomp := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure Vec3)) f ρ⁻¹
  rw [show ((ρ⁻¹ : ℝ) ^ Module.finrank ℝ Vec3)⁻¹ = ρ ^ (3 : ℕ) from by
    rw [show Module.finrank ℝ Vec3 = 3 from by
      change Module.finrank ℝ (Fin 3 → ℝ) = 3; rw [Module.finrank_fin_fun],
      inv_pow, inv_inv]] at hcomp
  simp only [hpt] at hcomp
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ ^ 3)] at hcomp
  have hlhs : (∫ z : Vec3, ρ ^ 2 * {w : Vec3 | vec3EuclideanNorm w ≤ ρ}.indicator
      (fun w => vec3EuclideanNorm w ^ (-(2 : ℝ))) z) =
      ρ ^ 2 * ∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ ρ}, vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    rw [integral_const_mul,
      MeasureTheory.integral_indicator (isCompact_euclideanClosedBall₀ hρ).measurableSet]
  rw [hlhs] at hcomp
  have hrhs : (∫ z : Vec3, f z) =
      ∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ 1}, vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    rw [hfdef,
      MeasureTheory.integral_indicator (isCompact_euclideanClosedBall₀ one_pos).measurableSet]
  rw [hrhs] at hcomp
  have hfinal : ρ ^ 2 * (∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ ρ},
      vec3EuclideanNorm z ^ (-(2 : ℝ))) =
      ρ ^ 2 * (ρ * ∫ z : Vec3 in {z | vec3EuclideanNorm z ≤ 1},
        vec3EuclideanNorm z ^ (-(2 : ℝ))) := by
    rw [hcomp]; ring
  exact mul_left_cancel₀ (by positivity : (ρ : ℝ) ^ 2 ≠ 0) hfinal

/-! ## Part 3: the translation identity and ELb -/

private theorem preimage_sub_left_euclideanBall (x : Vec3) (ρ : ℝ) :
    (fun y : Vec3 => x - y) ⁻¹' {z : Vec3 | vec3EuclideanNorm z ≤ ρ} =
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
  ext y
  change vec3EuclideanNorm (x - y) ≤ ρ ↔ vec3EuclideanNorm (y - x) ≤ ρ
  rw [show x - y = -(y - x) from by ring, vec3EuclideanNorm_neg]

private theorem integral_sub_left_euclideanBall (x : Vec3) (ρ : ℝ) (g : Vec3 → ℝ) :
    ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}, g (x - y) =
      ∫ z in {z : Vec3 | vec3EuclideanNorm z ≤ ρ}, g z := by
  have hmp : MeasurePreserving (fun y : Vec3 => x - y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hemb : MeasurableEmbedding (fun y : Vec3 => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb g {z : Vec3 | vec3EuclideanNorm z ≤ ρ}
  rwa [preimage_sub_left_euclideanBall x ρ] at h

private theorem integrableOn_vec3EuclideanNorm_rpow_neg_two₀ {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ)))
      {z : Vec3 | vec3EuclideanNorm z ≤ ρ} := by
  have h := integrableOn_vec3EuclideanNorm_rpow_neg_two (x := (0 : Vec3)) hρ
  simpa using h

theorem ELb_kernel_ball_integral : ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ l : Fin 3,
    IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ∧
    ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}, |spatialDeriv newtonianKernel l (x - y)| ≤
      C * ρ := by
  set C₀ : ℝ := ∫ z in {z : Vec3 | vec3EuclideanNorm z ≤ 1}, vec3EuclideanNorm z ^ (-(2 : ℝ))
    with hC0def
  have hC0nonneg : 0 ≤ C₀ := by
    rw [hC0def]
    apply MeasureTheory.setIntegral_nonneg (isCompact_euclideanClosedBall₀ one_pos).measurableSet
    intro z _
    exact Real.rpow_nonneg (vec3EuclideanNorm_nonneg z) _
  refine ⟨(4 * Real.pi)⁻¹ * C₀ + 1, by positivity, ?_⟩
  intro x ρ hρ l
  have hmp : MeasurePreserving (fun y : Vec3 => x - y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hemb : MeasurableEmbedding (fun y : Vec3 => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have hshiftint : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (x - y) ^ (-(2 : ℝ)))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
    have hiff := hmp.integrableOn_comp_preimage hemb
      (f := fun z : Vec3 => vec3EuclideanNorm z ^ (-(2 : ℝ)))
      (s := {z : Vec3 | vec3EuclideanNorm z ≤ ρ})
    rw [preimage_sub_left_euclideanBall x ρ] at hiff
    exact hiff.mpr (integrableOn_vec3EuclideanNorm_rpow_neg_two₀ hρ)
  have hdombound : (fun y : Vec3 => |spatialDeriv newtonianKernel l (x - y)|) ≤ᵐ[volume.restrict
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}]
      (fun y : Vec3 => (4 * Real.pi)⁻¹ * vec3EuclideanNorm (x - y) ^ (-(2 : ℝ))) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume x)] with y hy
    exact abs_spatialDeriv_newtonianKernel_le_euclidean (sub_ne_zero.mpr (Ne.symm hy)) l
  have hmeasAE : AEStronglyMeasurable (fun y : Vec3 => spatialDeriv newtonianKernel l (x - y))
      (volume.restrict {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}) := by
    have hm : Measurable (fun y : Vec3 => spatialDeriv newtonianKernel l (x - y)) :=
      (measurable_fderiv_apply_const ℝ newtonianKernel (basisVec l)).comp
        (measurable_const.sub measurable_id)
    exact hm.aestronglyMeasurable
  have hboundInt : IntegrableOn (fun y : Vec3 => (4 * Real.pi)⁻¹ * vec3EuclideanNorm (x - y) ^
      (-(2 : ℝ))) {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} :=
    hshiftint.const_mul (4 * Real.pi)⁻¹
  have hInt : IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
    have hdombound' : ∀ᵐ y ∂(volume.restrict {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}),
        ‖spatialDeriv newtonianKernel l (x - y)‖ ≤
          (4 * Real.pi)⁻¹ * vec3EuclideanNorm (x - y) ^ (-(2 : ℝ)) := by
      filter_upwards [hdombound] with y hy
      rwa [Real.norm_eq_abs]
    exact Integrable.mono' hboundInt hmeasAE hdombound'
  refine ⟨hInt, ?_⟩
  calc ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}, |spatialDeriv newtonianKernel l (x - y)|
      ≤ ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
        (4 * Real.pi)⁻¹ * vec3EuclideanNorm (x - y) ^ (-(2 : ℝ)) :=
        setIntegral_mono_ae_restrict hInt.abs hboundInt hdombound
    _ = (4 * Real.pi)⁻¹ * ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
        vec3EuclideanNorm (x - y) ^ (-(2 : ℝ)) := integral_const_mul _ _
    _ = (4 * Real.pi)⁻¹ * ∫ z in {z : Vec3 | vec3EuclideanNorm z ≤ ρ},
        vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
        rw [integral_sub_left_euclideanBall x ρ (fun z => vec3EuclideanNorm z ^ (-(2 : ℝ)))]
    _ = (4 * Real.pi)⁻¹ * (ρ * C₀) := by rw [integral_euclideanBall_rpow_scale hρ]
    _ ≤ ((4 * Real.pi)⁻¹ * C₀ + 1) * ρ := by nlinarith only [hC0nonneg, hρ.le, hρ]

end CIV
