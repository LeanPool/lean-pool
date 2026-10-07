/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorSlab
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofInteriorVorticity
public import LeanPool.EscauriazaSereginSverak.Endpoint.RescalingSuitable

/-!
# Vorticity vanishing near a regular time

Near a time `t₀` at which a whole closed ball times a time interval consists of
regular points (`lem:time-projection`), the velocity is bounded on a compact
slab.  A parabolic rescaling turns that slab into the unit-scale slab of
`essLocal_slabVorticityZero`, and the vanishing of the weak vorticity on an
exterior half-space seeds the continuation argument in the proof of
`thm:ess-local` (time-slice and spatial unique continuation).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak vorticity of the rescaled gradient is the rescaled weak vorticity. -/
theorem essLocal_weakVorticity_parabolicRescale (x₀ : Vec3) (t₀ r : ℝ)
    (DU : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    weakVorticity (parabolicRescaleGradient x₀ t₀ r DU) z =
      r ^ 2 • weakVorticity DU (parabolicTranslate x₀ t₀ (parabolicScale r z)) := by
  funext i
  fin_cases i <;>
    simp [weakVorticity_zero, weakVorticity_one, weakVorticity_two,
      parabolicRescaleGradient, mul_sub]

private theorem parabolicRescale_inverse_cylinder_mem
    {r ρ t₀ : ℝ} (hr : 0 < r) {w : ParabolicPoint}
    (hwspace : vec3EuclideanNorm (w.1 - 0) < ρ)
    (hwlower : t₀ - r ^ 2 < w.2) (hwupper : w.2 < t₀ + r ^ 2) :
    (r⁻¹ • w.1, -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2) ∈
      spaceTimeSet (vec3Ball (0 : Vec3) (ρ / r)) (Ioo (-1 : ℝ) 1) := by
  have hrne : r ≠ 0 := hr.ne'
  have hk : r⁻¹ ^ 2 * r ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hrne, one_pow]
  have hinv2 : 0 < r⁻¹ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · change vec3EuclideanNorm (r⁻¹ • w.1 - 0) < ρ / r
    rw [sub_zero] at hwspace ⊢
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr), div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hwspace (inv_pos.mpr hr)
  · change -1 < -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2
    have hlt : r⁻¹ ^ 2 * (-r ^ 2) < r⁻¹ ^ 2 * (w.2 - t₀) :=
      mul_lt_mul_of_pos_left (by linarith only [hwlower]) hinv2
    linarith only [hlt, hk]
  · change -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2 < 1
    have hlt : r⁻¹ ^ 2 * (w.2 - t₀) < r⁻¹ ^ 2 * r ^ 2 :=
      mul_lt_mul_of_pos_left (by linarith only [hwupper]) hinv2
    linarith only [hlt, hk]

private theorem rescaledPastTime_contains_two_unit_slab
    {t₀ r : ℝ} (ht₀ : t₀ ∈ Ioo (-2 : ℝ) 0)
    (hr1 : r ≤ 1) (hrt : r ≤ -t₀ / 4)
    (hr2r : r ^ 2 ≤ r) :
    Ioo (-2 : ℝ) 2 ⊆ CKN.rescaledTime r t₀ (Ioo (-12 : ℝ) 0) := by
  rintro s ⟨hs1, hs2⟩
  change t₀ + r ^ 2 * s ∈ Ioo (-12 : ℝ) 0
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have h1 : r ^ 2 * s ≤ r ^ 2 * 2 := mul_le_mul_of_nonneg_left hs2.le hr2
  have h2 : r ^ 2 * (-2) ≤ r ^ 2 * s := mul_le_mul_of_nonneg_left hs1.le hr2
  constructor
  · linarith only [h2, hr2r, hr1, ht₀.1]
  · linarith only [h1, hr2r, hrt, ht₀.2]

private theorem exists_regular_slab_rescale_radius
    (t₀ δ : ℝ) (hδ : 0 < δ) (ht₀ : t₀ ∈ Ioo (-2 : ℝ) 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r ≤ δ / 4 ∧ r ≤ -t₀ / 4 ∧
      r ≤ (t₀ + 2) / 4 ∧ 0 < -t₀ ∧ 0 < t₀ + 2 := by
  have hta : 0 < -t₀ := by linarith only [ht₀.2]
  have htb : 0 < t₀ + 2 := by linarith only [ht₀.1]
  let r : ℝ := min 1 (min (δ / 4) (min (-t₀ / 4) ((t₀ + 2) / 4)))
  have hr : 0 < r := lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrt : r ≤ -t₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt' : r ≤ (t₀ + 2) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨r, hr, hr1, hrδ, hrt, hrt', hta, htb⟩

/-- Near a time at which closed balls times short intervals consist of regular
points, the weak vorticity of a global suitable solution vanishes on any ball
of radius larger than `R₂`, provided it vanishes on the half-space
`{x₃ > R₂}` throughout `(-2, 0)`. -/
theorem essLocal_regularSlab_vorticityZero
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3}
    {q : ParabolicPoint → ℝ}
    (hsws : IsSuitableWeakSolution Set.univ (Ioo (-12 : ℝ) 0) 3 U DU q
      (0 : ParabolicPoint → Vec3))
    (R₂ ρ : ℝ) (hR₂ : 0 < R₂) (hρ : R₂ < ρ)
    (hseed : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0))), weakVorticity DU z = 0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-2 : ℝ) 0)
    (hreg : ∀ ρ' : ℝ, 0 < ρ' → ∃ δ > 0,
      closure (vec3Ball (0 : Vec3) ρ') ×ˢ Ioo (t₀ - δ) (t₀ + δ) ⊆
        regularPointLocus (Ioo (-12 : ℝ) 0) U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) ρ) (Ioo (t₀ - ε) (t₀ + ε)))),
      weakVorticity DU z = 0 := by
  have hρpos : 0 < ρ := hR₂.trans hρ
  obtain ⟨δ, hδ, hδreg⟩ := hreg (ρ + 1) (by linarith only [hρpos])
  -- the compact regular slab and its velocity bound
  let K : Set ParabolicPoint :=
    closure (vec3Ball (0 : Vec3) (ρ + 1)) ×ˢ Icc (t₀ - δ / 2) (t₀ + δ / 2)
  have hKcpt : IsCompact K := by
    have hball : IsCompact (closure (vec3Ball (0 : Vec3) (ρ + 1))) := by
      have hbd : Bornology.IsBounded (vec3Ball (0 : Vec3) (ρ + 1)) := by
        refine (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := ρ + 1)).subset ?_
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (norm_le_vec3EuclideanNorm _).trans (le_of_lt hy)
      exact hbd.isCompact_closure
    have hprod := hball.prod (isCompact_Icc (a := t₀ - δ / 2) (b := t₀ + δ / 2))
    exact (parabolicHomeomorph.isCompact_preimage).2 hprod
  have hKreg : K ⊆ regularPointLocus (Ioo (-12 : ℝ) 0) U := by
    rintro z ⟨hz1, hz2, hz3⟩
    exact hδreg ⟨hz1, by linarith only [hz2, hδ], by linarith only [hz3, hδ]⟩
  obtain ⟨M₀, hM₀, hKbd⟩ := essLocal_regularCompact_velocityBound hKcpt hKreg
  have hKmeas : MeasurableSet K := hKcpt.isClosed.measurableSet
  -- the scale
  obtain ⟨r, hr, hr1, hrδ, hrt, hrt', hta, htb⟩ :=
    exists_regular_slab_rescale_radius t₀ δ hδ ht₀
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2r : r ^ 2 ≤ r := by nlinarith only [hr, hr1]
  have hrne : r ≠ 0 := hr.ne'
  -- the change of variables and its inverse
  let z₀ : ParabolicPoint := ((0 : Vec3), t₀)
  let T : ParabolicPoint → ParabolicPoint := CKN.scalingParabolic r z₀
  have hTapply (z : ParabolicPoint) : T z = (r • z.1, t₀ + r ^ 2 * z.2) := by
    change ((0 : Vec3) + r • z.1, t₀ + r ^ 2 * z.2) = _
    rw [zero_add]
  have hTmeas : Measurable T := by
    change Measurable (fun z : Vec3 × ℝ => ((0 : Vec3) + r • z.1, t₀ + r ^ 2 * z.2))
    exact (measurable_const.add (measurable_fst.const_smul r)).prodMk
      (measurable_const.add (measurable_snd.const_mul _))
  have hTqmp : Measure.QuasiMeasurePreserving T (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) :=
    ⟨hTmeas, by
      change Measure.map (CKN.scalingParabolic r z₀) volume ≪ volume
      rw [CKN.map_scalingParabolic r hr]
      exact Measure.smul_absolutelyContinuous⟩
  let z₁ : ParabolicPoint := ((0 : Vec3), -(r⁻¹ ^ 2 * t₀))
  let Tinv : ParabolicPoint → ParabolicPoint := CKN.scalingParabolic r⁻¹ z₁
  have hTinvapply (w : ParabolicPoint) :
      Tinv w = (r⁻¹ • w.1, -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2) := by
    change ((0 : Vec3) + r⁻¹ • w.1, -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2) = _
    rw [zero_add]
  have hTinvmeas : Measurable Tinv := by
    change Measurable (fun z : Vec3 × ℝ =>
      ((0 : Vec3) + r⁻¹ • z.1, -(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * z.2))
    exact (measurable_const.add (measurable_fst.const_smul r⁻¹)).prodMk
      (measurable_const.add (measurable_snd.const_mul _))
  have hTinvqmp : Measure.QuasiMeasurePreserving Tinv (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) :=
    ⟨hTinvmeas, by
      change Measure.map (CKN.scalingParabolic r⁻¹ z₁) volume ≪ volume
      rw [CKN.map_scalingParabolic r⁻¹ (inv_pos.mpr hr)]
      exact Measure.smul_absolutelyContinuous⟩
  have hTTinv (w : ParabolicPoint) : T (Tinv w) = w := by
    rw [hTapply, hTinvapply]
    refine Prod.ext ?_ ?_
    · change r • r⁻¹ • w.1 = w.1
      rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
    · change t₀ + r ^ 2 * (-(r⁻¹ ^ 2 * t₀) + r⁻¹ ^ 2 * w.2) = w.2
      have hk : r ^ 2 * r⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
      linear_combination (w.2 - t₀) * hk
  -- the rescaled solution
  let V := parabolicRescaleVelocity (0 : Vec3) t₀ r U
  let DV := parabolicRescaleGradient (0 : Vec3) t₀ r DU
  let pv := parabolicRescalePressure (0 : Vec3) t₀ r q
  let J : Set ℝ := CKN.rescaledTime r t₀ (Ioo (-12 : ℝ) 0)
  have hVsws : IsSuitableWeakSolution Set.univ J 3 V DV pv (0 : ParabolicPoint → Vec3) := by
    have hscaled := isSuitableWeakSolution_parabolicRescale
      U DU q (0 : ParabolicPoint → Vec3) hsws (0 : Vec3) t₀ r hr
    have hzero :
        (fun z => r ^ 3 • (0 : ParabolicPoint → Vec3)
          (parabolicTranslate (0 : Vec3) t₀ (parabolicScale r z))) =
          (0 : ParabolicPoint → Vec3) := by
      funext z
      simp
    rw [show CKN.rescaledSpace r (0 : Vec3) (Set.univ : Set Vec3) = Set.univ by
      simp [CKN.rescaledSpace], hzero] at hscaled
    exact hscaled
  have hJ : Ioo (-2 : ℝ) 2 ⊆ J := by
    simpa [J] using rescaledPastTime_contains_two_unit_slab ht₀ hr1 hrt hr2r
  -- the velocity bound of the rescaled solution
  have hVbd : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 (ρ / r + 1)) (Ioo (-2 : ℝ) 2))),
      vec3EuclideanNorm (V z) ≤ r * M₀ := by
    have hS : MeasurableSet (spaceTimeSet (vec3Ball (0 : Vec3) (ρ / r + 1)) (Ioo (-2 : ℝ) 2)) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball 0 _) isOpen_Ioo).measurableSet
    have hpull := hTqmp.ae ((ae_restrict_iff' hKmeas).1 hKbd)
    refine (ae_restrict_iff' hS).2 ?_
    filter_upwards [hpull] with z hz hzS
    have hTK : T z ∈ K := by
      rw [hTapply]
      rcases hzS with ⟨hz1, hz2, hz3⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [closure_vec3Ball (by linarith only [hρpos])]
        change vec3EuclideanNorm (r • z.1 - 0) ≤ ρ + 1
        have hz1' : vec3EuclideanNorm (z.1 - 0) < ρ / r + 1 := hz1
        rw [sub_zero] at hz1' ⊢
        rw [vec3EuclideanNorm_smul, abs_of_pos hr]
        have hmul := mul_le_mul_of_nonneg_left hz1'.le hr.le
        have hdiv : r * (ρ / r) = ρ := mul_div_cancel₀ ρ hrne
        nlinarith only [hmul, hdiv, hr1]
      · have h2 : r ^ 2 * (-2) ≤ r ^ 2 * z.2 := mul_le_mul_of_nonneg_left hz2.le hr2.le
        change t₀ - δ / 2 ≤ t₀ + r ^ 2 * z.2
        linarith only [h2, hr2r, hrδ]
      · have h1 : r ^ 2 * z.2 ≤ r ^ 2 * 2 := mul_le_mul_of_nonneg_left hz3.le hr2.le
        change t₀ + r ^ 2 * z.2 ≤ t₀ + δ / 2
        linarith only [h1, hr2r, hrδ]
    have hUb := hz hTK
    change vec3EuclideanNorm (r • U (T z)) ≤ r * M₀
    rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hUb hr.le
  -- the seed of the rescaled solution
  let c : ℝ := (R₂ + ρ) / 2
  let y₀ : Vec3 := fun i => if i = 2 then c else 0
  have hy₀norm : vec3EuclideanNorm y₀ = c := by
    have hc : 0 ≤ c := by positivity
    unfold vec3EuclideanNorm
    rw [Fin.sum_univ_three]
    simp only [y₀, show ((0 : Fin 3) = 2) = False by decide,
      show ((1 : Fin 3) = 2) = False by decide, ite_false, ite_true]
    rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + c ^ 2 = c ^ 2 by ring, Real.sqrt_sq hc]
  let εU : ℝ := (ρ - R₂) / 2
  have hεU : 0 < εU := by
    have : 0 < ρ - R₂ := by linarith only [hρ]
    positivity
  let y₀V : Vec3 := r⁻¹ • y₀
  let εV : ℝ := εU / r
  have hεV : 0 < εV := by positivity
  have hy₀V : y₀V ∈ vec3Ball (0 : Vec3) (ρ / r) := by
    change vec3EuclideanNorm (r⁻¹ • y₀ - 0) < ρ / r
    rw [sub_zero, vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr), hy₀norm,
      div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left (show (R₂ + ρ) / 2 < ρ by linarith only [hρ])
      (inv_pos.mpr hr)
  have hseedV : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball y₀V εV) (Ioo (-1 : ℝ) 1))), weakVorticity DV z = 0 := by
    have hSU : MeasurableSet (spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0)) :=
      (isOpen_spaceTimeSet _ _ (isOpen_lt continuous_const (continuous_apply 2))
        isOpen_Ioo).measurableSet
    have hSV : MeasurableSet (spaceTimeSet (vec3Ball y₀V εV) (Ioo (-1 : ℝ) 1)) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
    have hpull := hTqmp.ae ((ae_restrict_iff' hSU).1 hseed)
    refine (ae_restrict_iff' hSV).2 ?_
    filter_upwards [hpull] with z hz hzS
    have hTS : T z ∈ spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0) := by
      rw [hTapply]
      rcases hzS with ⟨hz1, hz2, hz3⟩
      refine ⟨?_, ?_, ?_⟩
      · change R₂ < (r • z.1) 2
        have hz1' : vec3EuclideanNorm (z.1 - y₀V) < εV := hz1
        have hdiff : r • z.1 - y₀ = r • (z.1 - y₀V) := by
          change r • z.1 - y₀ = r • (z.1 - r⁻¹ • y₀)
          rw [smul_sub, smul_smul, mul_inv_cancel₀ hrne, one_smul]
        have hnorm : vec3EuclideanNorm (r • z.1 - y₀) < εU := by
          rw [hdiff, vec3EuclideanNorm_smul, abs_of_pos hr]
          have hmul := mul_lt_mul_of_pos_left hz1' hr
          have hεeq : r * εV = εU := mul_div_cancel₀ εU hrne
          linarith only [hmul, hεeq]
        have hcoord := abs_apply_le_vec3EuclideanNorm (r • z.1 - y₀) 2
        have hy2 : y₀ 2 = c := by simp [y₀]
        rw [Pi.sub_apply, hy2] at hcoord
        have habs := neg_abs_le ((r • z.1) 2 - c)
        have hceq : c - εU = R₂ := by ring
        linarith only [hcoord, habs, hnorm, hceq]
      · have h2 : r ^ 2 * (-1) ≤ r ^ 2 * z.2 := mul_le_mul_of_nonneg_left hz2.le hr2.le
        change -2 < t₀ + r ^ 2 * z.2
        linarith only [h2, hr2r, hrt', htb]
      · have h1 : r ^ 2 * z.2 ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hz3.le hr2.le
        change t₀ + r ^ 2 * z.2 < 0
        linarith only [h1, hr2r, hrt, hta]
    change weakVorticity (parabolicRescaleGradient (0 : Vec3) t₀ r DU) z = 0
    rw [essLocal_weakVorticity_parabolicRescale]
    change r ^ 2 • weakVorticity DU (T z) = 0
    rw [hz hTS, smul_zero]
  -- continuation on the rescaled slab
  have hslab := essLocal_slabVorticityZero (ρ / r) (r * M₀) (by positivity) hVsws hJ
    hVbd y₀V hy₀V εV hεV hseedV
  -- back to the original variables
  refine ⟨r ^ 2, hr2, ?_⟩
  have hSV : MeasurableSet (spaceTimeSet (vec3Ball (0 : Vec3) (ρ / r)) (Ioo (-1 : ℝ) 1)) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hSU : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) ρ) (Ioo (t₀ - r ^ 2) (t₀ + r ^ 2))) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hpull := hTinvqmp.ae ((ae_restrict_iff' hSV).1 hslab)
  refine (ae_restrict_iff' hSU).2 ?_
  filter_upwards [hpull] with w hw hwS
  have hTinvS : Tinv w ∈ spaceTimeSet (vec3Ball (0 : Vec3) (ρ / r)) (Ioo (-1 : ℝ) 1) := by
    rw [hTinvapply]
    rcases hwS with ⟨hw1, hw2, hw3⟩
    exact parabolicRescale_inverse_cylinder_mem hr hw1 hw2 hw3
  have hzero := hw hTinvS
  change weakVorticity (parabolicRescaleGradient (0 : Vec3) t₀ r DU) (Tinv w) = 0 at hzero
  rw [essLocal_weakVorticity_parabolicRescale] at hzero
  change r ^ 2 • weakVorticity DU (T (Tinv w)) = 0 at hzero
  rw [hTTinv] at hzero
  rcases smul_eq_zero.mp hzero with h | h
  · exact absurd h hr2.ne'
  · exact h

end ESS
