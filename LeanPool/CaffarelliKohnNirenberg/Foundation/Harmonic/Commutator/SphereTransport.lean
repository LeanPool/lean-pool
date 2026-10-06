/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Sphere Transport

Supporting estimates for the Navier–Stokes development.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

/-- The Euclidean three-vector space equipped with the transported `L²` norm. -/
abbrev E := WithLp 2 (CKN.Vec 3)

/-- The native Euclidean length agrees with the transported \`L²\` norm. -/
lemma vecEuclideanNorm_eq_l2 (z : CKN.Vec 3) :
    CKN.vecEuclideanNorm z = ‖WithLp.toLp 2 z‖ := by
  rw [show CKN.vecEuclideanNorm z =
      (∑ i, z i * z i) ^ ((1 : ℝ) / 2) by
        rw [← Real.sqrt_eq_rpow]
        simp [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot]
      ]
  simp [PiLp.norm_eq_sum, Real.norm_eq_abs, pow_two]

/-- Radial integration on the native three-dimensional carrier. -/
theorem integral_vecEuclideanNorm_radial (f : ℝ → ℝ) :
    ∫ z : CKN.Vec 3, f (CKN.vecEuclideanNorm z) =
      4 * Real.pi * ∫ y in Set.Ioi (0 : ℝ),
        y ^ (2 : ℝ) * f y := by
  have hmeasure :
      MeasurePreserving (WithLp.toLp 2 : CKN.Vec 3 → WithLp 2 (CKN.Vec 3))
        volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hcomp := hmeasure.integral_comp
    (MeasurableEquiv.toLp 2 (CKN.Vec 3)).measurableEmbedding
    (fun w : WithLp 2 (CKN.Vec 3) =>
      f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)))
  rw [show (∫ z : CKN.Vec 3, f (CKN.vecEuclideanNorm z)) =
      ∫ w : WithLp 2 (CKN.Vec 3),
        f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)) by
      convert hcomp using 1
      · simp]
  rw [show (fun w : WithLp 2 (CKN.Vec 3) =>
      f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))) =
      fun w => f ‖w‖ by
        funext w
        rw [← vecEuclideanNorm_eq_l2]
        rfl]
  rw [MeasureTheory.integral_fun_norm_addHaar volume f]
  have hdim : Module.finrank ℝ (WithLp 2 (CKN.Vec 3)) = 3 := by simp
  rw [hdim]
  have hball : (volume : Measure (WithLp 2 (CKN.Vec 3))).real
      (Metric.ball 0 1) = 4 * Real.pi / 3 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal =
      4 * Real.pi / 3
    rw [EuclideanSpace.volume_ball_fin_three]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
    norm_num
    ring
  rw [hball]
  simp only [smul_eq_mul]
  norm_num
  simp only [← Real.rpow_natCast]
  ring

/-- Integrability of a native radial function is equivalent to its polar radial
integrability. -/
theorem integrable_vecEuclideanNorm_radial_iff {f : ℝ → ℝ} :
    Integrable (fun z : CKN.Vec 3 => f (CKN.vecEuclideanNorm z)) volume ↔
      IntegrableOn (fun y : ℝ => y ^ (2 : ℕ) * f y)
        (Set.Ioi (0 : ℝ)) volume := by
  have hmeasure :
      MeasurePreserving (WithLp.toLp 2 : CKN.Vec 3 → WithLp 2 (CKN.Vec 3))
        volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hcomp := hmeasure.integrable_comp_emb
    (MeasurableEquiv.toLp 2 (CKN.Vec 3)).measurableEmbedding
    (g := fun w : WithLp 2 (CKN.Vec 3) =>
      f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)))
  rw [show Integrable (fun z : CKN.Vec 3 => f (CKN.vecEuclideanNorm z)) volume ↔
      Integrable (fun w : WithLp 2 (CKN.Vec 3) =>
        f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))) volume by
      constructor
      · intro h
        exact hcomp.mp h
      · intro h
        exact hcomp.mpr h]
  rw [show (fun w : WithLp 2 (CKN.Vec 3) =>
      f (CKN.vecEuclideanNorm ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))) =
      fun w => f ‖w‖ by
        funext w
        rw [← vecEuclideanNorm_eq_l2]
        rfl]
  rw [MeasureTheory.integrable_fun_norm_addHaar volume]
  have hdim : Module.finrank ℝ (WithLp 2 (CKN.Vec 3)) = 3 := by simp
  rw [hdim]
  norm_num

/-- The map that represents points of the transported unit sphere as native three-vectors. -/
@[expose]
def sphereToVec (w : Metric.sphere (0 : E) 1) : CKN.Vec 3 :=
  (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w.1

/-- The unit-sphere measure transported back to the native three-dimensional carrier. -/
@[expose]
def vecEuclideanSphereMeasure : Measure (CKN.Vec 3) :=
  Measure.map sphereToVec (Measure.toSphere (volume : Measure E))

/-- A homogeneous degree-four Gaussian integral factors through the transported sphere. -/
theorem integral_vec_gaussian_homogeneous
    (F : CKN.Vec 3 → ℝ)
    (hF : AEStronglyMeasurable F vecEuclideanSphereMeasure)
    (hhom : ∀ r : ℝ, 0 < r → ∀ z, F (r • z) = r ^ (4 : ℕ) * F z) :
    (∫ z : CKN.Vec 3, F z * Real.exp (-(CKN.vecNormSq z))) =
      (∫ z : CKN.Vec 3, F z ∂vecEuclideanSphereMeasure) *
        ∫ r : Set.Ioi (0 : ℝ), r.1 ^ (4 : ℕ) * Real.exp (-r.1 ^ 2)
          ∂(Measure.volumeIoiPow 2) := by
  have hmeasure :
      MeasurePreserving (WithLp.toLp 2 : CKN.Vec 3 → E) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hpolar := (Measure.measurePreserving_homeomorphUnitSphereProd
    (E := E) (volume : Measure E))
  have hmap : AEMeasurable sphereToVec (Measure.toSphere (volume : Measure E)) := by
    unfold sphereToVec
    fun_prop
  have hFmap : AEStronglyMeasurable F
      (Measure.map sphereToVec (Measure.toSphere (volume : Measure E))) := hF
  calc
    (∫ z : CKN.Vec 3, F z * Real.exp (-(CKN.vecNormSq z))) =
        ∫ w : E, F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w) *
          Real.exp (-(CKN.vecNormSq
            ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))) := by
      have hcomp := hmeasure.integral_comp
        (MeasurableEquiv.toLp 2 (CKN.Vec 3)).measurableEmbedding
        (fun w : E => F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w) *
          Real.exp (-(CKN.vecNormSq
            ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))))
      simpa [MeasurableEquiv.toLp_symm_apply] using hcomp
    _ = ∫ w : ({0}ᶜ : Set E),
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w.1) *
            Real.exp (-(CKN.vecNormSq
              ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w.1)))
          ∂(Measure.comap Subtype.val (volume : Measure E)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun w : E => F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w) *
          Real.exp (-(CKN.vecNormSq
            ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)))),
        restrict_compl_singleton]
    _ = ∫ q : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
            ((homeomorphUnitSphereProd E).symm q).1) *
            Real.exp (-(CKN.vecNormSq
              ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
                ((homeomorphUnitSphereProd E).symm q).1)))
          ∂((Measure.toSphere (volume : Measure E)).prod
            (Measure.volumeIoiPow 2)) := by
      simpa using hpolar.integral_comp
        (Homeomorph.measurableEmbedding _) (fun q =>
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
            ((homeomorphUnitSphereProd E).symm q).1) *
            Real.exp (-(CKN.vecNormSq
              ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
                ((homeomorphUnitSphereProd E).symm q).1)))
        )
    _ = ∫ q : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
          F (q.2.1 • (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1) *
            Real.exp (-(q.2.1 ^ 2))
          ∂((Measure.toSphere (volume : Measure E)).prod
            (Measure.volumeIoiPow 2)) := by
      congr 1
      funext q
      rw [homeomorphUnitSphereProd_symm_apply_coe]
      change F (q.2.1 • (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1) *
        Real.exp (-(CKN.vecNormSq
          ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
            (q.2.1 • q.1)))) = _
      rw [show (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm
          (q.2.1 • q.1) = q.2.1 •
            (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1 by rfl]
      rw [show CKN.vecNormSq (q.2.1 •
          (MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1) = q.2.1 ^ 2 by
        rw [← CKN.vecEuclideanNorm_sq, CKN.vecEuclideanNorm_smul]
        rw [abs_of_pos q.2.2]
        have hsphere : CKN.vecEuclideanNorm
            ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1) = 1 := by
          rw [vecEuclideanNorm_eq_l2]
          simp
        rw [hsphere]
        ring]
    _ = ∫ q : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1) *
            (q.2.1 ^ (4 : ℕ) * Real.exp (-q.2.1 ^ 2))
          ∂((Measure.toSphere (volume : Measure E)).prod
            (Measure.volumeIoiPow 2)) := by
      congr 1
      funext q
      rw [hhom q.2.1 q.2.2
        ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm q.1)]
      ring_nf
    _ = (∫ w : Metric.sphere (0 : E) 1,
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)
            ∂(Measure.toSphere (volume : Measure E))) *
          ∫ r : Set.Ioi (0 : ℝ), r.1 ^ (4 : ℕ) * Real.exp (-r.1 ^ 2)
            ∂(Measure.volumeIoiPow 2) := by
      simpa using (integral_prod_mul
        (μ := Measure.toSphere (volume : Measure E))
        (ν := Measure.volumeIoiPow 2)
        (fun w : Metric.sphere (0 : E) 1 =>
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w))
        (fun r : Set.Ioi (0 : ℝ) =>
          r.1 ^ (4 : ℕ) * Real.exp (-r.1 ^ 2)))
    _ = (∫ z : CKN.Vec 3, F z ∂vecEuclideanSphereMeasure) *
          ∫ r : Set.Ioi (0 : ℝ), r.1 ^ (4 : ℕ) * Real.exp (-r.1 ^ 2)
            ∂(Measure.volumeIoiPow 2) := by
      have hFmap' := integral_map hmap hFmap
      rw [show (∫ w : Metric.sphere (0 : E) 1,
          F ((MeasurableEquiv.toLp 2 (CKN.Vec 3)).symm w)
            ∂(Measure.toSphere (volume : Measure E))) =
          ∫ z : CKN.Vec 3, F z ∂vecEuclideanSphereMeasure by
        simpa [vecEuclideanSphereMeasure, sphereToVec] using hFmap'.symm]

end
end CKN.Foundation.Harmonic.Commutator
