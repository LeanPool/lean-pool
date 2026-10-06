/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.EnergyClassInterpolation
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSerrin
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormProductMoment
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# Coordinate mixed norms for finite Serrin comparison

The scalar Serrin norm and the energy-class interpolation give the coordinate
mixed moments used in the finite cross-density limit.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Each velocity coordinate inherits the distinguished field's finite
Serrin mixed norm. -/
theorem lps_finite_coordinate_mixed_data
    {T s : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    ∀ k : Fin 3,
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => u (x,t) k) (ENNReal.ofReal s) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => u (x,t) k) (ENNReal.ofReal s) volume ^
          (2 * s / (s - 3))) < ⊤ := by
  let ell : ℝ := 2 * s / (s - 3)
  have hs0 : 0 < s := by linarith only [hs]
  have hNormSlice := lps_finite_branch_slice_memLp_ae hU.meas_u hs hmix
  have hNormMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t)))
        (ENNReal.ofReal s) volume ^ ell) < ⊤ := by
    have hformula : (fun t : ℝ =>
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t)))
          (ENNReal.ofReal s) volume ^ ell) =ᵐ[volume.restrict (Ioo 0 T)]
        (fun t =>
          (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x,t))‖ₑ ^ s ∂volume) ^
            (ell / s)) := by
      filter_upwards [hNormSlice] with t ht
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top
          ht.aestronglyMeasurable,
        ENNReal.toReal_ofReal hs0.le, ← ENNReal.rpow_mul]
      congr 1
      field_simp [ne_of_gt hs0]
    rw [lintegral_congr_ae hformula]
    have hraw (t : ℝ) :
        (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x,t))‖ₑ ^ s ∂volume) =
        ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ s ∂volume := by
      apply lintegral_congr
      intro x
      rw [← Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    have hEq : (∫⁻ t in Ioo 0 T,
        (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x,t))‖ₑ ^ s ∂volume) ^
          (ell / s)) =
        (∫⁻ t in Ioo 0 T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ s ∂volume) ^
              ((2 * s / (s - 3)) / s)) := by
      apply lintegral_congr
      intro t
      rw [hraw]
    rw [hEq]
    simpa [ell] using hmix
  have hGood := serrinWeak_slices_ae hU
  intro k
  constructor
  · filter_upwards [hNormSlice, hGood] with t ht hn
    have hcoord := (hn.1.eval k).aestronglyMeasurable
    apply ht.of_le hcoord
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg (u (x,t)))] using
        (abs_apply_le_vec3EuclideanNorm (u (x,t)) k)
  · have hbound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        eLpNorm (fun x : Vec3 => u (x,t) k) (ENNReal.ofReal s) volume ≤
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t)))
            (ENNReal.ofReal s) volume := by
      filter_upwards [hGood] with t ht
      exact eLpNorm_mono_ae_real ((ht.1.eval k).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs,
            abs_of_nonneg (vec3EuclideanNorm_nonneg (u (x,t)))] using
              (abs_apply_le_vec3EuclideanNorm (u (x,t)) k))
    have hpow := lintegral_mono_ae (by
      filter_upwards [hbound] with t ht
      exact ENNReal.rpow_le_rpow ht (by positivity : 0 ≤ ell))
    simpa [ell] using lt_of_le_of_lt hpow hNormMoment

/-- The Leray--Hopf energy class supplies a finite mixed moment and a.e.
slicewise membership for every velocity coordinate at the energy interpolation
exponents. -/
theorem lps_energy_coordinate_mixed_data
    {T s : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du)
    (hU : IsSerrinWeakSolution T a u Du p) (hs : 3 < s) :
    ∀ k : Fin 3,
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => u (x,t) k)
          (ENNReal.ofReal (2 * s / (s - 2))) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => u (x,t) k)
          (ENNReal.ofReal (2 * s / (s - 2))) volume ^ (2 * s / 3)) < ⊤ := by
  let q : ℝ := 2 * s / (s - 2)
  let m : ℝ := 2 * s / 3
  have hs0 : 0 < s := by linarith only [hs]
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hq : 0 < q := by dsimp [q]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hRaw := lps_energy_class_mixed_moment hLH hs
  have hRaw' : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ‖u (x,t)‖ₑ ^ q ∂volume) ^ (m / q)) < ⊤ := by
    simpa [q, m] using hRaw
  have hSlice := lps_vector_mixed_slice_memLp_of_raw hm hq hU.meas_u hRaw'
  have hMoment := lps_vector_mixed_moment_of_raw hq hSlice hRaw'
  have hComponent := lps_vector_component_mixed_moment
    (p := m) (q := q) (by positivity) hSlice hMoment
  intro k
  simpa [q, m] using hComponent k

end ESS

end
