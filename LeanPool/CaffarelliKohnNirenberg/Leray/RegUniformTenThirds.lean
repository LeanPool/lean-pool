/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spatial interpolation for regularized velocities

The whole-space Gagliardo–Nirenberg estimate applies to almost every
positive-time slice of a regularized velocity.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regUniform_eLpNorm_two_sq_eq_lintegral
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

private theorem regUniform_memLp_of_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hlt : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) < ⊤) :
    MemLp f (ENNReal.ofReal p) μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne

private theorem regUniform_component_gradient_sq_le
    {u : ParabolicPoint → Vec3} (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (i : Fin 3) :
    vec3EuclideanNorm (Du z i) ^ (2 : ℕ) ≤ CKN.spatialGradientSq
      u Du z := by
  rw [vec3EuclideanNorm, Real.sq_sqrt
    (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (Du z i j)),
    CKN.spatialGradientSq]
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (Du z k j))
    (Finset.mem_univ i)

private theorem regUniform_component_gradient_enorm_sq_le
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (z : ParabolicPoint) (i : Fin 3) :
    ‖vec3EuclideanNorm (Du z i)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
  have hnorm : ‖vec3EuclideanNorm (Du z i)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (vec3EuclideanNorm (Du z i) ^ (2 : ℕ)) := by
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg (Du z i)),
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg (Du z i))
        (by norm_num)]
    norm_num [Real.rpow_natCast]
  rw [hnorm]
  exact ENNReal.ofReal_le_ofReal (by
    simpa [CKN.spatialGradientSq] using
      regUniform_component_gradient_sq_le (u := u) Du z i)

private theorem regUniform_gn_power_bound
    {B K U A G : ℝ≥0∞}
    (hGN : B ≤ K * U ^ (2 / 5 : ℝ) * G ^ (3 / 5 : ℝ))
    (hU : U ≤ A) :
    B ^ (10 / 3 : ℝ) ≤
      K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * G ^ (2 : ℝ) := by
  calc
    B ^ (10 / 3 : ℝ) ≤
        (K * U ^ (2 / 5 : ℝ) * G ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hGN (by norm_num)
    _ = K ^ (10 / 3 : ℝ) * U ^ (4 / 3 : ℝ) * G ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10 / 3)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10 / 3)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 2 <;> norm_num
    _ ≤ K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * G ^ (2 : ℝ) := by
      gcongr

/-- The spatial `L^{10/3}` Gagliardo–Nirenberg estimate holds on almost every
positive-time slice, component by component. -/
theorem regUniform_spatial_slice_tenThirds
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hSlices : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Du (x, t) i j)) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
        CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
          eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ^ (2 / 5 : ℝ) *
            eLpNorm (fun x : Vec3 =>
              vec3EuclideanNorm (Du (x, t) i)) 2 volume ^ (3 / 5 : ℝ) := by
  filter_upwards [hSlices] with t hH1
  rcases hH1 with ⟨h, hvalues, hgradients⟩
  intro i
  have hGN := CKN.h1_gagliardoNirenberg_tenThirds (h i)
  have hvalue :
      (fun x : Vec3 => (h i).toFun x) = fun x => u (x, t) i := by
    funext x
    exact hvalues i x
  have hgradient :
      (fun x : Vec3 => vec3EuclideanNorm ((h i).grad x)) =
        fun x => vec3EuclideanNorm (Du (x, t) i) := by
    funext x
    congr 1
    funext j
    exact hgradients i x j
  simpa [hvalue, hgradient] using hGN

/-- Energy and dissipation bounds integrate the slice interpolation estimate to
space-time `L^{10/3}`, component by component. -/
theorem regUniform_component_memLp_tenThirds
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (A D : ℝ≥0∞)
    (hSlices : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Du (x, t) i j))
    (hSliceBound : ∀ t, 0 < t → ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ≤ A)
    (hUmeasurable : Measurable u) (hDumeasurable : Measurable Du)
    (hGradientEnergyBound :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume ∂volume) ≤ D)
    (hAfinite : A < ⊤) (hDfinite : D < ⊤) (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (CKN.spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      eLpNorm (fun z : ParabolicPoint => u z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (CKN.spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ^
            (10 / 3 : ℝ) ≤
        (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^
            (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * D := by
  classical
  let μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let μ : Measure ParabolicPoint :=
    (volume : Measure ParabolicPoint).restrict
      (CKN.spaceTimeSet Set.univ (Ioi (0 : ℝ)))
  let f : ParabolicPoint → ℝ := fun z => u z i
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let K : ℝ≥0∞ := CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)
  let C : ℝ≥0∞ := K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ)
  have hfmeas : Measurable f := by
    exact (measurable_pi_apply i).comp hUmeasurable
  have hfjoint : AEMeasurable f μ := by
    exact hfmeas.aemeasurable
  have hfdensity : AEMeasurable
      (fun z : ParabolicPoint => ‖f z‖ₑ ^ (10 / 3 : ℝ)) μ := by
    exact hfjoint.enorm.pow_const (10 / 3 : ℝ)
  have hfdensityProduct : AEMeasurable
      (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (10 / 3 : ℝ))
      ((volume : Measure Vec3).prod μt) := by
    exact (hfmeas.enorm.pow_const (10 / 3 : ℝ)).aemeasurable
  have hspatialDensityMeas : Measurable
      (fun z : ParabolicPoint => CKN.spatialGradientSq u Du z) := by
    unfold CKN.spatialGradientSq
    fun_prop
  have hgradientDensityMeas : Measurable
      (fun z : ParabolicPoint => ENNReal.ofReal (CKN.spatialGradientSq u Du z)) :=
    ENNReal.measurable_ofReal.comp hspatialDensityMeas
  have hgradientIterMeas : AEMeasurable
      (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) μt := by
    have hprodDensity : Measurable
        (fun z : Vec3 × ℝ => ENNReal.ofReal (CKN.spatialGradientSq u Du z)) :=
      hgradientDensityMeas
    exact (hprodDensity.lintegral_prod_left').aemeasurable.mono_measure
      Measure.restrict_le_self
  have hGNae : ∀ᵐ t ∂μt, ∀ j : Fin 3,
      eLpNorm (fun x : Vec3 => u (x, t) j) q volume ≤
        K * eLpNorm (fun x => u (x, t) j) 2 volume ^ (2 / 5 : ℝ) *
          eLpNorm (fun x => vec3EuclideanNorm (Du (x, t) j)) 2 volume ^
            (3 / 5 : ℝ) := by
    simpa [K, q, μt] using regUniform_spatial_slice_tenThirds u Du hSlices
  have hSliceIntegrand : ∀ᵐ t ∂μt,
      (∫⁻ x : Vec3, ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ) ∂volume) ≤
        C * (∫⁻ x : Vec3,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
    filter_upwards [hGNae, ae_restrict_mem measurableSet_Ioi] with t hGN htmem
    have ht : 0 < t := htmem
    have hGN_i := hGN i
    have hpow := regUniform_gn_power_bound hGN_i (hSliceBound t ht i)
    have hgradMeas : AEStronglyMeasurable
        (fun x : Vec3 => vec3EuclideanNorm (Du (x, t) i)) volume := by
      exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        ((measurable_pi_apply i).comp
          (hDumeasurable.comp measurable_prodMk_right)).aestronglyMeasurable
    have hgradIntegral := regUniform_eLpNorm_two_sq_eq_lintegral hgradMeas
    have hgradLe :
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Du (x, t) i))
          2 volume ^ (2 : ℝ) ≤
          ∫⁻ x : Vec3,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume := by
      rw [hgradIntegral]
      exact lintegral_mono fun x =>
        regUniform_component_gradient_enorm_sq_le (x, t) i
    have hfSliceMeas : AEStronglyMeasurable
        (fun x : Vec3 => f (x, t)) volume := by
      exact (hfmeas.comp measurable_prodMk_right).aestronglyMeasurable
    have hLpIdentity :
        eLpNorm (fun x : Vec3 => f (x, t))
            (ENNReal.ofReal (10 / 3 : ℝ)) volume ^ (10 / 3 : ℝ) =
          ∫⁻ x : Vec3, ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ) ∂volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : ENNReal.ofReal (10 / 3 : ℝ) ≠ 0)
          ENNReal.ofReal_ne_top hfSliceMeas,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
        ← ENNReal.rpow_mul]
      norm_num
    rw [← hLpIdentity]
    calc
      _ ≤ K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) *
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Du (x, t) i))
            2 volume ^ (2 : ℝ) := hpow
      _ ≤ C * (∫⁻ x : Vec3,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_left hgradLe (by positivity)
  have hIterBound :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ) ∂volume ∂volume) ≤ C * D := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), C *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) ∂volume :=
        lintegral_mono_ae hSliceIntegrand
      _ = C * (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume ∂volume) := by
        rw [lintegral_const_mul'' _ hgradientIterMeas]
      _ ≤ C * D := mul_le_mul_of_nonneg_left hGradientEnergyBound (by positivity)
  have hMeasure :
      μ = (volume : Measure Vec3).prod μt := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) =
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hJointBound :
      (∫⁻ z : ParabolicPoint, ‖f z‖ₑ ^ (10 / 3 : ℝ) ∂μ) ≤ C * D := by
    calc
      (∫⁻ z : ParabolicPoint, ‖f z‖ₑ ^ (10 / 3 : ℝ) ∂μ) =
          ∫⁻ x : Vec3, ∫⁻ t : ℝ, ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ) ∂μt ∂volume := by
        rw [hMeasure]
        exact MeasureTheory.lintegral_prod _ hfdensityProduct
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3,
          ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ) ∂volume ∂μt :=
        MeasureTheory.lintegral_lintegral_swap
          (μ := (volume : Measure Vec3)) (ν := μt)
          (f := fun x t => ‖f (x, t)‖ₑ ^ (10 / 3 : ℝ)) hfdensityProduct
      _ ≤ C * D := by
        simpa [μt] using hIterBound
  have hfinite : C * D < ⊤ := by
    have hKfinite : K < ⊤ := by
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (Classical.choose_spec CKN.sobolev_L6_global).1
    have hKpow : K ^ (10 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfinite.ne
    have hApow : A ^ (4 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAfinite.ne
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hKpow hApow) hDfinite
  have hfstrong : AEStronglyMeasurable f μ := hfmeas.aestronglyMeasurable
  have hmem : MemLp f q μ :=
    regUniform_memLp_of_lintegral_lt_top (by norm_num) hfstrong
      (lt_of_le_of_lt hJointBound hfinite)
  refine ⟨hmem, ?_⟩
  change eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) ≤ C * D
  have hLpIdentity :
      eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) =
        ∫⁻ z : ParabolicPoint, ‖f z‖ₑ ^ (10 / 3 : ℝ) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : ENNReal.ofReal (10 / 3 : ℝ) ≠ 0)
        ENNReal.ofReal_ne_top hfstrong,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
      ← ENNReal.rpow_mul]
    norm_num
  rw [hLpIdentity]
  exact hJointBound

end CKN.Leray

end
