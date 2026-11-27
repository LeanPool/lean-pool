/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt imports and rework the local continuity proof. -/

module

public import LeanPool.VenNullClockRoundRates.RoundAreaBridge
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Area density for the upper - hemisphere graph
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal Pointwise

namespace VenRateUpper

/-- Domain of the Cartesian graph of the upper open hemisphere. -/
def graphDisk : Set (ℝ × ℝ) := {p | 0 < 1 - p.1 ^ 2 - p.2 ^ 2}

theorem isOpen_graphDisk : IsOpen graphDisk :=
  isOpen_lt continuous_const (by fun_prop)

/-- The nonnegative sphere height over the unit disk. -/
def graphHeight (p : ℝ × ℝ) : ℝ := Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)

theorem graphHeight_pos {p : ℝ × ℝ} (hp : p ∈ graphDisk) : 0 < graphHeight p :=
  Real.sqrt_pos.2 hp

theorem graphHeight_sq {p : ℝ × ℝ} (hp : p ∈ graphDisk) :
    graphHeight p ^ 2 = 1 - p.1 ^ 2 - p.2 ^ 2 :=
  Real.sq_sqrt (le_of_lt hp)

theorem contDiffOn_graphHeight : ContDiffOn ℝ ⊤ graphHeight graphDisk :=
  ((by fun_prop : ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ 1 - p.1 ^ 2 - p.2 ^ 2)).contDiffOn).sqrt
    fun _ hp ↦ ne_of_gt hp

/-- Embed the open disk as the sphere's upper hemisphere. -/
def upperGraph (p : graphDisk) : VenMask.UnitSphere :=
  ⟨(p.1.1, p.1.2, graphHeight p.1), by rw [graphHeight_sq p.property]; ring⟩

/-- Euclidean surface Jacobian of the Cartesian graph. -/
def graphAreaDensity (p : ℝ × ℝ) : ℝ := (graphHeight p)⁻¹

theorem graphAreaDensity_pos {p : ℝ × ℝ} (hp : p ∈ graphDisk) : 0 < graphAreaDensity p :=
  inv_pos.2 (graphHeight_pos hp)

theorem contDiffOn_graphAreaDensity : ContDiffOn ℝ ⊤ graphAreaDensity graphDisk :=
  contDiffOn_graphHeight.inv fun _ hp ↦ (graphHeight_pos hp).ne'

/-- Scale a lifted disk point by the third coordinate to parametrize its radial cone. -/
def coneGraph (p : RoundAmbient) : RoundAmbient :=
  WithLp.toLp 2 ![p 2 * p 0, p 2 * p 1, p 2 * graphHeight (p 0, p 1)]

private abbrev coorBasis := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private def coneDerivativeMatrix (p : RoundAmbient) : Matrix (Fin 3) (Fin 3) ℝ :=
  let z := graphHeight (p 0, p 1)
  !![p 2, 0, p 0; 0, p 2, p 1; -(p 2 * p 0) / z, -(p 2 * p 1) / z, z]

private def coneDerivative (p : RoundAmbient) : RoundAmbient →L[ℝ] RoundAmbient :=
  (Matrix.toLin coorBasis coorBasis (coneDerivativeMatrix p)).toContinuousLinearMap

private lemma coneDerivative_apply (p v : RoundAmbient) (i : Fin 3) :
    coneDerivative p v i =
      (![p 2 * v 0 + p 0 * v 2, p 2 * v 1 + p 1 * v 2,
        (-(p 2 * p 0) / graphHeight (p 0, p 1)) * v 0 +
        (-(p 2 * p 1) / graphHeight (p 0, p 1)) * v 1 +
        graphHeight (p 0, p 1) * v 2] : Fin 3 → ℝ) i := by
  change coorBasis.repr ((Matrix.toLin coorBasis coorBasis (coneDerivativeMatrix p)) v) i = _
  rw [Matrix.repr_toLin]
  fin_cases i <;>
    simp [coneDerivativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

private theorem hasFDerivAt_coneGraph {p : RoundAmbient}
    (hp : (p 0, p 1) ∈ graphDisk) : HasFDerivAt coneGraph (coneDerivative p) p := by
  have hx := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (0 : Fin 3)
  have hy := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (1 : Fin 3)
  have hr := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (2 : Fin 3)
  have hz := (((hasFDerivAt_const (1 : ℝ) p).sub (hx.pow 2)).sub (hy.pow 2)).sqrt
    (show 1 - p 0 ^ 2 - p 1 ^ 2 ≠ 0 from ne_of_gt hp)
  have hProj (i : Fin 3) (v : RoundAmbient) :
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i) v = v i := rfl
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp 2]
  intro i
  apply HasFDerivAt.hasFDerivWithinAt
  fin_cases i
  · convert hr.mul hx using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [coneDerivative_apply, hProj]
  · convert hr.mul hy using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [coneDerivative_apply, hProj]
  · convert hr.mul hz using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      have hZ : graphHeight (p 0, p 1) ≠ 0 := (graphHeight_pos hp).ne'
      simp [coneDerivative_apply, hProj, graphHeight]
      unfold graphHeight at hZ
      field_simp
      ring

private theorem det_coneDerivative {p : RoundAmbient}
    (hp : (p 0, p 1) ∈ graphDisk) :
    (coneDerivative p).det = (p 2) ^ 2 * graphAreaDensity (p 0, p 1) := by
  unfold coneDerivative coneDerivativeMatrix graphAreaDensity
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul, add_zero, sub_zero]
  have hz := graphHeight_pos hp
  have hunit := graphHeight_sq hp
  field_simp
  linear_combination (p 2) ^ 2 * hunit


/-- Sphere points with positive third coordinate. -/
def upperHemisphere : Set VenMask.UnitSphere := {q | 0 < q.val.2.2}

/-- Project a sphere point onto its first two coordinates. -/
def graphProjection (q : VenMask.UnitSphere) : ℝ × ℝ := (q.val.1, q.val.2.1)

theorem continuous_graphProjection : Continuous graphProjection := by
  have hc : Continuous (fun q : VenMask.UnitSphere ↦ q.val) := continuous_subtype_val
  exact hc.fst.prodMk hc.snd.fst

/-- The image of a measurable subpatch is its inverse image under the coordinate projection,
intersected with the upper hemisphere. -/
theorem upperGraph_image (U : Set (ℝ × ℝ)) :
    upperGraph '' (Subtype.val ⁻¹' U) = upperHemisphere ∩ graphProjection ⁻¹' U := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨graphHeight_pos p.property, hp⟩
  · rintro ⟨hq, hU⟩
    have hsub : 1 - q.val.1 ^ 2 - q.val.2.1 ^ 2 = q.val.2.2 ^ 2 := by
      linarith [q.property]
    have hd : graphProjection q ∈ graphDisk := by
      change 0 < 1 - q.val.1 ^ 2 - q.val.2.1 ^ 2
      rw [hsub]
      exact sq_pos_of_pos hq
    refine ⟨⟨graphProjection q, hd⟩, hU, ?_⟩
    apply Subtype.ext
    have hz : graphHeight (graphProjection q) = q.val.2.2 := by
      unfold graphHeight graphProjection
      simp only
      rw [hsub, Real.sqrt_sq hq.le]
    change (q.val.1, q.val.2.1, graphHeight (graphProjection q)) = q.val
    rw [hz]

theorem measurableSet_upperGraph_image {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) :
    MeasurableSet (upperGraph '' (Subtype.val ⁻¹' U)) := by
  rw [upperGraph_image]
  have hc : Continuous (fun q : VenMask.UnitSphere ↦ q.val) := continuous_subtype_val
  exact (isOpen_lt continuous_const hc.snd.snd).measurableSet.inter
    (continuous_graphProjection.measurable hU)

private def radialCoordinates : RoundAmbient ≃ᵐ ℝ × (ℝ × ℝ) :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) (Fin.last 2))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)))

private lemma radialCoordinates_apply (p : RoundAmbient) :
    radialCoordinates p = (p 2, p 0, p 1) := rfl

private lemma measurePreserving_radialCoordinates : MeasurePreserving radialCoordinates := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have he : MeasurePreserving e := volume_preserving_piFinTwo _
  have h₁ := (volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 ↦ ℝ) (Fin.last 2)).comp (PiLp.volume_preserving_ofLp (Fin 3))
  have h₂ : MeasurePreserving (fun p : ℝ × (Fin 2 → ℝ) ↦ (p.1, e p.2)) volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun (_ : ℝ) x ↦ e x) (e.measurable.comp measurable_snd) (ae_of_all _ fun _ ↦ he.map_eq)
  exact h₂.comp h₁

private lemma coneGraph_eq_smul {p : RoundAmbient} (hp : (p 0, p 1) ∈ graphDisk) :
    coneGraph p = (p 2) • (toMetricSphere (upperGraph ⟨(p 0, p 1), hp⟩)).val := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private def graphSector (U : Set (ℝ × ℝ)) : Set RoundAmbient :=
  radialCoordinates ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ U)

private lemma coneGraph_injOn {U : Set (ℝ × ℝ)} (hUD : U ⊆ graphDisk) :
    InjOn coneGraph (graphSector U) := by
  intro p hp q hq h
  rw [graphSector, mem_preimage, radialCoordinates_apply, mem_prod] at hp hq
  have hp' := hUD hp.2
  have hq' := hUD hq.2
  have hpNorm : ‖coneGraph p‖ = p 2 := by
    rw [coneGraph_eq_smul hp', norm_smul, mem_sphere_zero_iff_norm.mp (Subtype.prop _),
      mul_one, Real.norm_eq_abs, abs_of_pos hp.1.1]
  have hqNorm : ‖coneGraph q‖ = q 2 := by
    rw [coneGraph_eq_smul hq', norm_smul, mem_sphere_zero_iff_norm.mp (Subtype.prop _),
      mul_one, Real.norm_eq_abs, abs_of_pos hq.1.1]
  have hr : p 2 = q 2 := by rw [← hpNorm, h, hqNorm]
  have hx : p 0 = q 0 := by
    have hh : p 2 * p 0 = q 2 * q 0 := congrArg (fun u : RoundAmbient ↦ u 0) h
    rw [← hr] at hh
    exact mul_left_cancel₀ hp.1.1.ne' hh
  have hy : p 1 = q 1 := by
    have hh : p 2 * p 1 = q 2 * q 1 := congrArg (fun u : RoundAmbient ↦ u 1) h
    rw [← hr] at hh
    exact mul_left_cancel₀ hp.1.1.ne' hh
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hr

private lemma coneGraph_image {U : Set (ℝ × ℝ)} (hUD : U ⊆ graphDisk) :
    coneGraph '' graphSector U =
      Ioo (0 : ℝ) 1 •
        (Subtype.val '' (metricSphereHomeomorph ⁻¹' (upperGraph '' (Subtype.val ⁻¹' U)))) := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [graphSector, mem_preimage, radialCoordinates_apply, mem_prod] at hp
    let q := upperGraph ⟨(p 0, p 1), hUD hp.2⟩
    have hq : q ∈ upperGraph '' (Subtype.val ⁻¹' U) :=
      ⟨⟨(p 0, p 1), hUD hp.2⟩, hp.2, rfl⟩
    refine ⟨p 2, hp.1, (toMetricSphere q).val, ⟨toMetricSphere q, ?_, rfl⟩,
      (coneGraph_eq_smul (hUD hp.2)).symm⟩
    change metricSphereHomeomorph (metricSphereHomeomorph.symm q) ∈
      (upperGraph '' (Subtype.val ⁻¹' U))
    simpa using hq
  · rintro ⟨r, hr, v, ⟨q, hq, rfl⟩, rfl⟩
    rcases hq with ⟨p, hp, heq⟩
    let u : RoundAmbient := WithLp.toLp 2 ![p.val.1, p.val.2, r]
    refine ⟨u, ?_, ?_⟩
    · rw [graphSector, mem_preimage, radialCoordinates_apply, mem_prod]
      exact ⟨hr, hp⟩
    · rw [coneGraph_eq_smul p.property]
      change r • (metricSphereHomeomorph.symm (upperGraph p)).val = _
      rw [heq, metricSphereHomeomorph.symm_apply_apply]

private lemma lintegral_radial_pow :
    (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2)) = ENNReal.ofReal (1 / 3) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow (a := 0) (b := 1) (μ :=
      volume) 2).1,
    ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
  · norm_num
  · exact Eventually.of_forall (fun r ↦ sq_nonneg r)

private lemma lintegral_coneGraph_jacobian {U : Set (ℝ × ℝ)}
    (hU : MeasurableSet U) (hUD : U ⊆ graphDisk) :
    (volume : Measure RoundAmbient) (coneGraph '' graphSector U) =
      ENNReal.ofReal (1 / 3) * ∫⁻ p in U, ENNReal.ofReal (graphAreaDensity p) := by
  have hSet : MeasurableSet (graphSector U) :=
    radialCoordinates.measurable (measurableSet_Ioo.prod hU)
  have hD {p} (hp : p ∈ graphSector U) : (p 0, p 1) ∈ graphDisk := by
    rw [graphSector, mem_preimage, radialCoordinates_apply, mem_prod] at hp
    exact hUD hp.2
  have hJac := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure RoundAmbient) hSet
    (fun _ hp ↦ (hasFDerivAt_coneGraph (hD hp)).hasFDerivWithinAt)
    (coneGraph_injOn hUD) (fun _ ↦ (1 : ℝ≥0∞))
  rw [lintegral_const, one_mul] at hJac
  simp only [Measure.restrict_apply_univ, mul_one] at hJac
  rw [hJac]
  calc
    _ = ∫⁻ p in graphSector U,
        ENNReal.ofReal ((p 2) ^ 2) * ENNReal.ofReal (graphAreaDensity (p 0, p 1)) := by
      refine setLIntegral_congr_fun hSet (fun p hp ↦ ?_)
      rw [det_coneDerivative (hD hp), abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (graphAreaDensity_pos (hD hp)).le), ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ U,
        ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (graphAreaDensity p.2) := by
      simpa only [graphSector, radialCoordinates_apply] using
        (measurePreserving_radialCoordinates.setLIntegral_comp_preimage_emb
          radialCoordinates.measurableEmbedding
          (fun p : ℝ × (ℝ × ℝ) ↦
            ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (graphAreaDensity p.2))
          (Ioo (0 : ℝ) 1 ×ˢ U))
    _ = ENNReal.ofReal (1 / 3) * ∫⁻ p in U, ENNReal.ofReal (graphAreaDensity p) := by
      change (∫⁻ p : ℝ × (ℝ × ℝ), _ ∂
        (((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).restrict
          (Ioo (0 : ℝ) 1 ×ˢ U))) = _
      have hRad : AEMeasurable (fun r : ℝ ↦ ENNReal.ofReal (r ^ 2))
          ((volume : Measure ℝ).restrict (Ioo 0 1)) :=
        ((measurable_id.pow_const _).ennreal_ofReal).aemeasurable
      have hDisk : AEMeasurable (fun p ↦ ENNReal.ofReal (graphAreaDensity p))
          ((volume : Measure (ℝ × ℝ)).restrict U) :=
        by
          have hSqrt : Continuous (fun p : ℝ × ℝ ↦ √(1 - p.1 ^ 2 - p.2 ^ 2)) := by fun_prop
          exact hSqrt.measurable.inv.ennreal_ofReal.aemeasurable
      rw [← Measure.prod_restrict, lintegral_prod_mul hRad hDisk, lintegral_radial_pow]

/-- The upper hemisphere has ordinary Euclidean graph area with density
`1 / sqrt (1 - x ^ 2 - y ^ 2)` in Cartesian coordinates. -/
theorem roundAreaUnnormalized_upperGraph {U : Set (ℝ × ℝ)}
    (hU : MeasurableSet U) (hUD : U ⊆ graphDisk) :
    roundAreaUnnormalized (upperGraph '' (Subtype.val ⁻¹' U)) =
      ∫⁻ p in U, ENNReal.ofReal (graphAreaDensity p) := by
  rw [roundAreaUnnormalized_apply (measurableSet_upperGraph_image hU), ← coneGraph_image hUD,
    lintegral_coneGraph_jacobian hU hUD, ← mul_assoc]
  have h : (3 : ℝ≥0∞) * ENNReal.ofReal (1 / 3) = 1 := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [h, one_mul]

/-- The normalized round law restricted to the chart, expressed on measurable planar patches. -/
theorem roundArea_upperGraph {U : Set (ℝ × ℝ)}
    (hU : MeasurableSet U) (hUD : U ⊆ graphDisk) :
    roundArea (upperGraph '' (Subtype.val ⁻¹' U)) =
      (roundAreaUnnormalized univ)⁻¹ * ∫⁻ p in U, ENNReal.ofReal (graphAreaDensity p) := by
  rw [roundArea, smul_apply, smul_eq_mul, roundAreaUnnormalized_upperGraph hU hUD]

private theorem graphProjection_mem_graphDisk {q : VenMask.UnitSphere}
    (hq : q ∈ upperHemisphere) : graphProjection q ∈ graphDisk := by
  change 0 < 1 - q.val.1 ^ 2 - q.val.2.1 ^ 2
  have hs := q.property
  have hz : 0 < q.val.2.2 := hq
  nlinarith [sq_pos_of_pos hz]

/-- The chart projection pushes the upper-hemisphere restriction to the weighted planar law. -/
theorem map_graphProjection_roundArea :
    Measure.map graphProjection (roundArea.restrict upperHemisphere) =
      (roundAreaUnnormalized univ)⁻¹ •
        ((volume : Measure (ℝ × ℝ)).restrict graphDisk).withDensity
          (fun p ↦ ENNReal.ofReal (graphAreaDensity p)) := by
  ext U hU
  rw [Measure.map_apply continuous_graphProjection.measurable hU,
    Measure.restrict_apply (continuous_graphProjection.measurable hU),
    smul_apply, smul_eq_mul, withDensity_apply _ hU, Measure.restrict_restrict hU]
  have hPatch : MeasurableSet (U ∩ graphDisk) := hU.inter isOpen_graphDisk.measurableSet
  have hEq : graphProjection ⁻¹' U ∩ upperHemisphere =
      upperGraph '' (Subtype.val ⁻¹' (U ∩ graphDisk)) := by
    rw [upperGraph_image]
    ext q
    exact ⟨fun h ↦ ⟨h.2, h.1, graphProjection_mem_graphDisk h.2⟩,
      fun h ↦ ⟨h.2.1, h.1⟩⟩
  rw [hEq, roundArea_upperGraph hPatch inter_subset_right]


/-- The Euclidean cone-area law has total area `4π`. -/
theorem roundAreaUnnormalized_univ :
    roundAreaUnnormalized univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [roundAreaUnnormalized, Measure.map_apply metricSphereHomeomorph.measurable
    MeasurableSet.univ, preimage_univ, Measure.toSphere_apply_univ,
    EuclideanSpace.volume_ball_fin_three]
  have hrank : (Module.finrank ℝ RoundAmbient : ℝ≥0∞) = 3 := by simp
  simp only [hrank, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Bochner integral change of variables for the upper hemisphere. -/
theorem integral_roundArea_upperHemisphere (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (∫ q in upperHemisphere, f (graphProjection q) ∂roundArea) =
      (4 * Real.pi)⁻¹ * ∫ p in graphDisk, graphAreaDensity p * f p := by
  rw [← integral_map continuous_graphProjection.measurable.aemeasurable hf.aestronglyMeasurable,
    map_graphProjection_roundArea, MeasureTheory.integral_smul_measure, roundAreaUnnormalized_univ,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  have hMeas : Measurable graphAreaDensity :=
    ((Real.continuous_sqrt.comp (by fun_prop :
      Continuous (fun p : ℝ × ℝ ↦ 1 - p.1 ^ 2 - p.2 ^ 2))).measurable.inv)
  have hDensity : (fun p ↦ ENNReal.ofReal (graphAreaDensity p)) =
      fun p ↦ (Real.toNNReal (graphAreaDensity p) : ℝ≥0∞) := by
    funext p
    exact (ENNReal.ofNNReal_toNNReal _).symm
  rw [hDensity, integral_withDensity_eq_integral_smul hMeas.real_toNNReal]
  congr 1
  refine setIntegral_congr_fun isOpen_graphDisk.measurableSet (fun p hp ↦ ?_)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (graphAreaDensity_pos hp).le, smul_eq_mul]

end VenRateUpper
