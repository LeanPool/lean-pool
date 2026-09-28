/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Analysis.Foundations.Development005
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Order.Foundations.Development001
public import LeanPool.MovingSofa.Polygon.Applications.Development001


public import LeanPool.MovingSofa.Polygon.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Bounds.Arm.Estimates`.
* `Bounds.WedgeGap.Infimum`.
* `Bounds.WedgeGap.Limit`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Arm / Estimates
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

private def positiveArmKernel (t : ℝ) (u : Real.Angle) : ℝ :=
  if 0 < (u - (t : Real.Angle)).sin ∧ 0 ≤ (u - (t : Real.Angle)).cos then
    (u - (t : Real.Angle)).sin
  else 0

private theorem measurable_positiveArmKernel :
    Measurable (Function.uncurry positiveArmKernel) := by
  have hs : Continuous (fun z : ℝ × Real.Angle ↦
      (z.2 - (z.1 : Real.Angle)).sin) :=
    Real.Angle.continuous_sin.comp
      (continuous_snd.sub (Real.Angle.continuous_coe.comp continuous_fst))
  have hc : Continuous (fun z : ℝ × Real.Angle ↦
      (z.2 - (z.1 : Real.Angle)).cos) :=
    Real.Angle.continuous_cos.comp
      (continuous_snd.sub (Real.Angle.continuous_coe.comp continuous_fst))
  exact hs.measurable.piecewise
    ((measurableSet_lt measurable_const hs.measurable).inter
      (measurableSet_le measurable_const hc.measurable)) measurable_const

private theorem mem_positiveArmArc_iff {t : ℝ} (u : Real.Angle) :
    u ∈ (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2) ↔
      0 < (u - (t : Real.Angle)).sin ∧ 0 ≤ (u - (t : Real.Angle)).cos := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [← Real.Angle.coe_sub, Real.Angle.sin_coe, Real.Angle.cos_coe]
    exact ⟨Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hx.1)
      (by linarith [hx.2, Real.pi_pos]),
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩⟩
  · intro hu
    let d := (u - (t : Real.Angle)).toReal
    have hdpos : 0 < d := by
      have hsign : (u - (t : Real.Angle)).sign = 1 := by
        simpa only [Real.Angle.sign, sign_eq_one_iff] using hu.1
      exact (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hsign).1
    have hdle : d ≤ Real.pi / 2 := by
      have habs := Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two.1 hu.2
      exact (le_abs_self d).trans habs
    refine ⟨t + d, ⟨by linarith, by linarith⟩, ?_⟩
    change (((t + d : ℝ) : Real.Angle)) = u
    calc
      (((t + d : ℝ) : Real.Angle)) = (t : Real.Angle) + (d : Real.Angle) :=
        Real.Angle.coe_add t d
      _ = (t : Real.Angle) + (u - (t : Real.Angle)) := by
        congr 1
        exact Real.Angle.coe_toReal (u - (t : Real.Angle))
      _ = u := by abel

private theorem positiveArmKernel_eq_indicator (t : ℝ) :
    positiveArmKernel t =
      ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)).indicator
        (fun u ↦ (u - (t : Real.Angle)).sin) := by
  classical
  funext u
  rw [Set.indicator_apply]
  simp only [positiveArmKernel, mem_positiveArmArc_iff]

private theorem stronglyMeasurable_integral_positiveArmKernel (μ : Measure Real.Angle)
    [SFinite μ] : StronglyMeasurable (fun t ↦ ∫ u, positiveArmKernel t u ∂μ) := by
  exact measurable_positiveArmKernel.stronglyMeasurable.integral_prod_right

/-- The positive tangent arm length is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_tangentArm_fst (C : RightAngleCapSpace) :
    AEStronglyMeasurable (fun t ↦ (tangentArmLengths C t).2.1)
      (volume.restrict (Ioc 0 (Real.pi / 2))) := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  apply (stronglyMeasurable_integral_positiveArmKernel
    (surfaceAreaMeasure C.val)).aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [tangentArm_convolution C t ⟨ht.1.le, ht.2⟩, positiveArmKernel_eq_indicator]
  exact integral_indicator (μ := surfaceAreaMeasure C.val)
    (f := fun u : Real.Angle ↦ (u - (t : Real.Angle)).sin)
    (Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2))

/-- The positive tangent arm length is nonnegative: it is the integral of the sine of a
quarter-turn of normal directions against the surface area measure. -/
theorem tangentArm_fst_nonneg (C : RightAngleCapSpace) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ (tangentArmLengths C t).2.1 := by
  rw [tangentArm_convolution C t ht]
  refine setIntegral_nonneg (Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2)) ?_
  rintro u ⟨v, hv, rfl⟩
  rw [← Real.Angle.coe_sub, Real.Angle.sin_coe]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hv.1])
    (by linarith [hv.2, Real.pi_pos])

/-- Both right tangent arm lengths of a right-angle cap are nonnegative: the outer corner
realizes the support value in the tangent direction, while the two contacts lie in the cap. -/
theorem tangentArmLengths_right_nonneg (K : RightAngleCapSpace) (t : ℝ) :
    0 ≤ (tangentArmLengths K t).1.1 ∧ 0 ≤ (tangentArmLengths K t).1.2 := by
  have hy : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    change inner ℝ (supportingPlacement (K.val : Set Point) (t : Real.Angle)
      hallwayParts.outerCorner) _ = _
    rw [inner_supportingPlacement_tangentVector]
    simp [hallwayParts]
  have hmem (p : Point) (hp : p ∈ (K.val : Set Point)) :
      inner ℝ p (tangentVector (t : Real.Angle)) ≤
        supportValue K.val ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← normalVector_add_pi_div_two (t : Real.Angle)]
    exact inner_le_supportValue K.val hp _
  simp only [tangentArmLengths, capVertices, inner_sub_left, hy]
  exact ⟨sub_nonneg.mpr (hmem _ (edgeVertices_fst_mem K.val _).1),
    sub_nonneg.mpr (hmem _ (edgeVertices_snd_mem K.val _).1)⟩

/-- The positive tangent arm length is bounded by the total mass of the surface area measure. -/
theorem abs_tangentArm_fst_le (C : RightAngleCapSpace) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |(tangentArmLengths C t).2.1| ≤ (surfaceAreaMeasure C.val).real Set.univ := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  rw [tangentArm_convolution C t ht]
  change ‖∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2),
    (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure C.val‖ ≤ _
  calc
    _ ≤ 1 * (surfaceAreaMeasure C.val).real
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)) := by
      apply norm_setIntegral_le_of_norm_le_const
      · finiteness
      · intro u hu
        simp only [Real.norm_eq_abs]
        rw [← Real.Angle.sin_toReal]
        exact Real.abs_sin_le_one _
    _ ≤ (surfaceAreaMeasure C.val).real Set.univ := by
      simpa only [one_mul] using
        measureReal_mono (μ := surfaceAreaMeasure C.val) (Set.subset_univ _)
          (measure_ne_top _ _)

/-- The positive tangent arm length is bounded by the total surface mass, hence integrable. -/
theorem intervalIntegrable_tangentArm_fst (C : RightAngleCapSpace) :
    IntervalIntegrable (fun t ↦ (tangentArmLengths C t).2.1)
      volume 0 (Real.pi / 2) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).2
  apply (integrableOn_const
    (μ := volume) (s := Ioc 0 (Real.pi / 2)) (measure_Ioc_lt_top.ne)
    (C := (surfaceAreaMeasure C.val).real Set.univ)).mono'
      (aestronglyMeasurable_tangentArm_fst C)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact abs_tangentArm_fst_le C ⟨ht.1.le, ht.2⟩

private theorem maximumPolygonCap_diam_le (n : ℕ) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) : Metric.diam (K.val : Set Point) ≤ 5 := by
  classical
  obtain ⟨hn, ⟨k, hk⟩, P, hPK, hmax⟩ := hK
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hinner : ∀ (p : Point) (s : ℝ),
      inner ℝ p (normalVector (s : Real.Angle)) = p 0 * Real.cos s + p 1 * Real.sin s := by
    intro p s
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.Angle.cos_coe,
      Real.Angle.sin_coe]
    ring
  have hc1 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hsn1 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hc2 : Real.cos (Real.pi / 4 + Real.pi / 2) = -(Real.sqrt 2 / 2) := by
    rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have hsn2 : Real.sin (Real.pi / 4 + Real.pi / 2) = Real.sqrt 2 / 2 := by
    rw [Real.sin_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  set h1 : ℝ := supportValue (K.val : Set Point) ((Real.pi / 4 : ℝ) : Real.Angle)
  set h2 : ℝ := supportValue (K.val : Set Point)
    ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)
  have htop : ∀ p ∈ (K.val : Set Point), p 1 ≤ 1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two, K.property.2.2.2.1] at hle
    linarith
  have hbot : ∀ p ∈ (K.val : Set Point), 0 ≤ p 1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hcc : Real.cos (3 * Real.pi / 2) = 0 := by
      rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add,
        Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hss : Real.sin (3 * Real.pi / 2) = -1 := by
      rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add,
        Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    rw [hinner, hcc, hss, K.property.2.2.2.2.2.1] at hle
    linarith
  have hsupp1 : ∀ p ∈ (K.val : Set Point),
      p 0 * (Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2) ≤ h1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 4 : ℝ) : Real.Angle)
    rwa [hinner, hc1, hsn1] at hle
  have hsupp2 : ∀ p ∈ (K.val : Set Point),
      p 0 * -(Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2) ≤ h2 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)
    rwa [hinner, hc2, hsn2] at hle
  -- the diagonal angle belongs to the dyadic grid
  have hdir : (rightAngleSet n hn).directions =
      (Finset.Ioo 0 n).image (fun i : ℕ ↦ (i : ℝ) / n * (Real.pi / 2)) := rfl
  have hquarter : Real.pi / 4 ∈ (rightAngleSet n hn).directions := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
      cases k with
      | zero => rw [pow_zero] at hk; omega
      | succ m => exact ⟨m, rfl⟩
    rw [hdir]
    refine Finset.mem_image.mpr ⟨2 ^ m, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · positivity
    · rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
    · rw [hk]
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      push_cast
      rw [pow_succ]
      field_simp
      ring
  -- the inner corner at the diagonal angle has height at most one
  have hsum : h1 + h2 ≤ 2 + Real.sqrt 2 := by
    by_contra hcon
    rw [not_le] at hcon
    set e : ℝ := (h1 + h2 - 2 - Real.sqrt 2) / 4 with he
    have hepos : 0 < e := by rw [he]; linarith
    set q : Point := !₂[Real.sqrt 2 / 2 * (h1 - h2),
      Real.sqrt 2 / 2 * (h1 + h2 - 2 - 2 * e)]
    have hq0 : q 0 = Real.sqrt 2 / 2 * (h1 - h2) := rfl
    have hq1 : q 1 = Real.sqrt 2 / 2 * (h1 + h2 - 2 - 2 * e) := rfl
    have hqheight : 1 < q 1 := by
      rw [hq1, he]
      nlinarith
    have hqu : inner ℝ q (normalVector ((Real.pi / 4 : ℝ) : Real.Angle)) = h1 - 1 - e := by
      rw [hinner, hq0, hq1, hc1, hsn1]
      linear_combination ((h1 - 1 - e) / 2) * hs2
    have hqv : inner ℝ q (normalVector ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle))
        = h2 - 1 - e := by
      rw [hinner, hq0, hq1, hc2, hsn2]
      linear_combination ((h2 - 1 - e) / 2) * hs2
    have hqe : inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = q 1 := by
      rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
    have hfan : q ∈ capFan (rightAngleSet n hn).angle := by
      rw [hangle]
      refine ⟨?_, ?_⟩ <;>
        · show (0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          rw [hqe]
          linarith
    have hquad : q ∈ innerQuadrant (P.val.val : Set Point) (Real.pi / 4) := by
      rw [hPK]
      refine ⟨?_, ?_⟩
      · show inner ℝ q (normalVector ((Real.pi / 4 : ℝ) : Real.Angle)) < h1 - 1
        rw [hqu]
        linarith
      · show inner ℝ q (normalVector ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)) < h2 - 1
        rw [hqv]
        linarith
    have hmemniche : q ∈ polygonNiche (rightAngleSet n hn) P.val :=
      ⟨hfan, Set.mem_biUnion hquarter hquad⟩
    have hsub := polygonNiche_subset_of_balanced P (maximumPolygonCap_balanced P hmax)
    have hqK : q ∈ (P.val.val : Set Point) := hsub hmemniche
    rw [hPK] at hqK
    exact absurd (htop q hqK) (not_le.mpr hqheight)
  -- the outer corner height and the trapezoid containing the cap
  set hgt : ℝ := Real.sqrt 2 / 2 * (h1 + h2) with hgtdef
  set ctr : ℝ := Real.sqrt 2 / 2 * (h1 - h2) with hctrdef
  have hgtle : hgt ≤ 1 + Real.sqrt 2 := by
    rw [hgtdef]
    nlinarith
  have hsum1 : hgt + ctr = Real.sqrt 2 * h1 := by rw [hgtdef, hctrdef]; ring
  have hsum2 : hgt - ctr = Real.sqrt 2 * h2 := by rw [hgtdef, hctrdef]; ring
  have htrap1 : ∀ p ∈ (K.val : Set Point), p 0 + p 1 ≤ hgt + ctr := by
    intro p hp
    have hm := mul_le_mul_of_nonneg_left (hsupp1 p hp) hs2pos.le
    have hkey : Real.sqrt 2 * (p 0 * (Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2))
        = p 0 + p 1 := by linear_combination (p 0 / 2 + p 1 / 2) * hs2
    rw [hkey] at hm
    linarith
  have htrap2 : ∀ p ∈ (K.val : Set Point), p 1 - p 0 ≤ hgt - ctr := by
    intro p hp
    have hm := mul_le_mul_of_nonneg_left (hsupp2 p hp) hs2pos.le
    have hkey : Real.sqrt 2 * (p 0 * -(Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2))
        = p 1 - p 0 := by linear_combination (p 1 / 2 - p 0 / 2) * hs2
    rw [hkey] at hm
    linarith
  have hgtge : 1 ≤ hgt := by
    have hle : supportValue (K.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) ≤ hgt := by
      apply csSup_le (K.val.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      show inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ hgt
      rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two]
      have h1p := htrap1 p hp
      have h2p := htrap2 p hp
      linarith
    rw [K.property.2.2.2.1] at hle
    exact hle
  -- every distance inside the trapezoid is at most the length of its bottom side
  have hdiam : Metric.diam (K.val : Set Point) ≤ 2 * hgt := by
    refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
    intro p hp q hq
    have hp1 := htrap1 p hp
    have hp2 := htrap2 p hp
    have hq1 := htrap1 q hq
    have hq2 := htrap2 q hq
    have hpt := htop p hp
    have hpb := hbot p hp
    have hqt := htop q hq
    have hqb := hbot q hq
    have hd : dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp [Real.dist_eq, sq_abs]
    rw [hd, show (2 : ℝ) * hgt = Real.sqrt ((2 * hgt) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    have kx : (p 0 - q 0) ^ 2 ≤ (2 * hgt - p 1 - q 1) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * hgt - p 1 - q 1 - (p 0 - q 0))
        (by linarith : (0 : ℝ) ≤ 2 * hgt - p 1 - q 1 + (p 0 - q 0))]
    nlinarith [kx, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * hgt - 2)
      (by linarith : (0 : ℝ) ≤ p 1 + q 1),
      mul_nonneg hpb (by linarith : (0 : ℝ) ≤ 1 - p 1),
      mul_nonneg hqb (by linarith : (0 : ℝ) ≤ 1 - q 1)]
  have hdiam5 : Metric.diam (K.val : Set Point) ≤ 5 := by linarith
  exact hdiam5

private theorem tangentArmLengths_le_of_diam (K : RightAngleCapSpace)
    (hdiam5 : Metric.diam (K.val : Set Point) ≤ 5) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (tangentArmLengths K t).1.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).1.2 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.2 ∈ Set.Icc (0 : ℝ) 5 := by
  intro t ht
  obtain ⟨hAp, hAm, hCp, hCm⟩ := capTangentArm_identities K t ht
  have huu : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 :=
    inner_normalVector_self t
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have huv : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 :=
    inner_normalVector_tangentVector t
  have hvu : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, huv]
  have hnu : ‖normalVector (t : Real.Angle)‖ = 1 := norm_normalVector_real t
  have hvn : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (t : Real.Angle) := by
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  have hnv : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    rw [← hvn]
    exact norm_normalVector_real _
  have hyu : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (normalVector (t : Real.Angle)) = supportValue (K.val : Set Point) (t : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      huu, hvu]
    ring
  have hyv : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      huv, hvv]
    ring
  have hApmem : (capVertices K t).1.1 ∈ (K.val : Set Point) :=
    (edgeVertices_fst_mem K.val (t : Real.Angle)).1
  have hAmmem : (capVertices K t).1.2 ∈ (K.val : Set Point) :=
    (edgeVertices_snd_mem K.val (t : Real.Angle)).1
  have hCpmem : (capVertices K t).2.1 ∈ (K.val : Set Point) :=
    (edgeVertices_fst_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hCmmem : (capVertices K t).2.2 ∈ (K.val : Set Point) :=
    (edgeVertices_snd_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hsupv : ∀ p ∈ (K.val : Set Point),
      inner ℝ p (tangentVector (t : Real.Angle)) ≤
        supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
    rwa [hvn] at hle
  have hsupu : ∀ p ∈ (K.val : Set Point),
      inner ℝ p (normalVector (t : Real.Angle)) ≤
        supportValue (K.val : Set Point) (t : Real.Angle) :=
    fun p hp ↦ inner_le_supportValue K.val hp (t : Real.Angle)
  -- the arm identities in projected form
  have harm : ∀ (A C : Point) (f g : ℝ),
      (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
        A + f • tangentVector (t : Real.Angle) →
      (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
        C + g • normalVector (t : Real.Angle) →
      A ∈ (K.val : Set Point) → C ∈ (K.val : Set Point) →
      (f ∈ Set.Icc (0 : ℝ) 5 ∧ g ∈ Set.Icc (0 : ℝ) 5) := by
    intro A C f g hfA hgC hAmem hCmem
    have hfv : inner ℝ A (tangentVector (t : Real.Angle)) + f =
        supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← hyv, hfA, inner_add_left, real_inner_smul_left, hvv]
      ring
    have hgu : inner ℝ C (normalVector (t : Real.Angle)) + g =
        supportValue (K.val : Set Point) (t : Real.Angle) := by
      rw [← hyu, hgC, inner_add_left, real_inner_smul_left, huu]
      ring
    have hAC : A + f • tangentVector (t : Real.Angle) = C + g • normalVector (t : Real.Angle) :=
      hfA ▸ hgC
    have hprojv := congrArg (fun z : Point ↦ inner ℝ z (tangentVector (t : Real.Angle))) hAC
    have hproju := congrArg (fun z : Point ↦ inner ℝ z (normalVector (t : Real.Angle))) hAC
    simp only [inner_add_left, real_inner_smul_left, hvv, hvu, huu, huv, mul_one,
      mul_zero, add_zero] at hprojv hproju
    have hdist : dist A C ≤ Metric.diam (K.val : Set Point) :=
      Metric.dist_le_diam_of_mem K.val.isCompact.isBounded hAmem hCmem
    have hfeq : f = inner ℝ (C - A) (tangentVector (t : Real.Angle)) := by
      rw [inner_sub_left]
      linarith
    have hgeq : g = inner ℝ (A - C) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left]
      linarith
    constructor
    · refine ⟨by linarith [hsupv A hAmem], ?_⟩
      have hb : inner ℝ (C - A) (tangentVector (t : Real.Angle)) ≤
          ‖C - A‖ * ‖tangentVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      rw [hnv, mul_one, norm_sub_rev, ← dist_eq_norm] at hb
      rw [hfeq]
      linarith
    · refine ⟨by linarith [hsupu C hCmem], ?_⟩
      have hb : inner ℝ (A - C) (normalVector (t : Real.Angle)) ≤
          ‖A - C‖ * ‖normalVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      rw [hnu, mul_one, ← dist_eq_norm] at hb
      rw [hgeq]
      linarith
  obtain ⟨hf1, hg1⟩ := harm (capVertices K t).1.1 (capVertices K t).2.1
    (tangentArmLengths K t).1.1 (tangentArmLengths K t).2.1 hAp hCp hApmem hCpmem
  obtain ⟨hf2, hg2⟩ := harm (capVertices K t).1.2 (capVertices K t).2.2
    (tangentArmLengths K t).1.2 (tangentArmLengths K t).2.2 hAm hCm hAmmem hCmmem
  exact ⟨hf1, hf2, hg1, hg2⟩


theorem maximumPolygonCap_arm_bound (n : ℕ) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) :
    Metric.diam (K.val : Set Point) ≤ 5 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (tangentArmLengths K t).1.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).1.2 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.2 ∈ Set.Icc (0 : ℝ) 5 := by
  have hdiam := maximumPolygonCap_diam_le n K hK
  exact ⟨hdiam, tangentArmLengths_le_of_diam K hdiam⟩

/-! ### Helpers for the discrete arm bound -/

/-- Two representatives of the same angle in one turn agree. -/
private theorem coe_angle_inj_Ioc {x y : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi))
    (hy : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)) (h : (x : Real.Angle) = (y : Real.Angle)) :
    x = y :=
  Real.Angle.injOn_coe_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) hx hy h

/-- Between consecutive grid normals a right-angle polygon cap has no exposed edge, both at
the direction itself and at the direction shifted by a right angle. -/
private theorem rightAnglePolygonCap_edgeVertices_eq (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hgrid : s ∉ (rightAngleSet n hn).directions) :
    (edgeVertices K.val.val (s : Real.Angle)).1 =
        (edgeVertices K.val.val (s : Real.Angle)).2 ∧
      (edgeVertices K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  have hdirI : ∀ r ∈ (rightAngleSet n hn).directions, r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun r hr ↦ (rightAngleSet n hn).interior r hr
  -- the possible normals of a nondegenerate exposed edge in the upper half turn
  have hkey : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) Real.pi →
      (edgeVertices K.val.val (x : Real.Angle)).1 ≠
        (edgeVertices K.val.val (x : Real.Angle)).2 →
      x ∈ (rightAngleSet n hn).directions ∨
        (∃ r ∈ (rightAngleSet n hn).directions, x = r + Real.pi / 2) ∨
        x = Real.pi / 2 := by
    intro x hx hne
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := ⟨hx.1, by linarith [hx.2]⟩
    have hlow : ∀ z : Real.Angle, z ∈ capLowerNormals (rightAngleSet n hn).angle →
        z = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      intro z hz
      rcases hz with hz | hz
      · rw [hz]
        congr 1
        show (rightAngleSet n hn).angle + Real.pi = 3 * Real.pi / 2
        show Real.pi / 2 + Real.pi = 3 * Real.pi / 2
        ring
      · exact hz
    rcases K.properEdgeNormal_mem_allowed_or_antipodal (x : Real.Angle) hne with
      (⟨r, hr, hrx⟩ | hlowx) | ⟨z, hz, hzx⟩
    · have hrI := angleDomain_subset_Ioo (rightAngleSet n hn) hr
      have hxr : x = r := coe_angle_inj_Ioc hxIoc ⟨hrI.1, by linarith [hrI.2]⟩ hrx.symm
      subst hxr
      rcases hr with (hr | ⟨r, hr, hrx⟩) | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inl ⟨r, hr, hrx.symm⟩)
      · rcases hr with hr | hr
        · exact Or.inr (Or.inr hr)
        · exact Or.inr (Or.inr hr)
    · exfalso
      have hx3 : x = 3 * Real.pi / 2 :=
        coe_angle_inj_Ioc hxIoc ⟨by linarith, by linarith⟩ (hlow _ hlowx)
      linarith [hx.2]
    · rcases hz with ⟨r, hr, rfl⟩ | hz
      · exfalso
        have hrI := angleDomain_subset_Ioo (rightAngleSet n hn) hr
        have hxr : x = r + Real.pi := by
          refine coe_angle_inj_Ioc hxIoc ⟨by linarith [hrI.1], by linarith [hrI.2]⟩ ?_
          rw [Real.Angle.coe_add]
          exact hzx.symm
        linarith [hx.2, hrI.1]
      · right; right
        refine coe_angle_inj_Ioc hxIoc ⟨by linarith, by linarith⟩ ?_
        have hxz : (x : Real.Angle) =
            ((3 * Real.pi / 2 : ℝ) : Real.Angle) + (Real.pi : Real.Angle) := by
          rw [← hzx, hlow _ hz]
        rw [hxz, ← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
        exact ⟨1, by push_cast; ring⟩
  constructor
  · by_contra hne
    rcases hkey s ⟨hs.1, by linarith [hs.2]⟩ hne with h | ⟨r, hr, hrs⟩ | h
    · exact hgrid h
    · linarith [(hdirI r hr).1, hs.2]
    · linarith [hs.2]
  · by_contra hne
    rcases hkey (s + Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ hne with
      h | ⟨r, hr, hrs⟩ | h
    · linarith [(hdirI _ h).2, hs.1]
    · exact hgrid (by rwa [show s = r by linarith])
    · linarith [hs.1]

/-- On a cell of degenerate exposed edges whose contacts lie in a finite set, the contact point
is constant and agrees with both endpoint conventions. -/
private theorem exists_edgeVertices_const_of_degenerate (K : ConvexBody Point)
    {S : Set Point} (hS : S.Finite) {a b : ℝ} (hab : a < b)
    (hdeg : ∀ s ∈ Set.Ioo a b,
      (edgeVertices K (s : Real.Angle)).1 = (edgeVertices K (s : Real.Angle)).2)
    (hmem : ∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 ∈ S) :
    ∃ A : Point, (∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 = A) ∧
      (edgeVertices K (a : Real.Angle)).1 = A ∧
      (edgeVertices K (b : Real.Angle)).2 = A := by
  classical
  have hloc : ∀ u ∈ Set.Ioo a b, ∀ᶠ r : ℝ in 𝓝 u,
      (edgeVertices K (r : Real.Angle)).1 = (edgeVertices K (u : Real.Angle)).1 := by
    intro u hu
    have hIoo : Set.Ioo a b ∈ 𝓝 u := isOpen_Ioo.mem_nhds hu
    have hnbhd : (S \ {(edgeVertices K (u : Real.Angle)).1})ᶜ ∈
        𝓝 (edgeVertices K (u : Real.Angle)).1 :=
      (hS.sdiff (t := {(edgeVertices K (u : Real.Angle)).1})).isClosed.isOpen_compl.mem_nhds
        (by simp)
    have hright := (contact_oneSided_limits K u).1 hnbhd
    have hleft := (contact_oneSided_limits K u).2.2.2.1
    rw [← hdeg u hu] at hleft
    have hleft' := hleft hnbhd
    have hfin : ∀ᶠ r : ℝ in 𝓝[≠] u,
        (edgeVertices K (r : Real.Angle)).1 = (edgeVertices K (u : Real.Angle)).1 := by
      rw [← nhdsLT_sup_nhdsGT]
      refine Filter.eventually_sup.mpr ⟨?_, ?_⟩
      · filter_upwards [hleft', nhdsWithin_le_nhds hIoo] with r hr hrI
        by_contra hcon
        exact hr ⟨hmem r hrI, hcon⟩
      · filter_upwards [hright, nhdsWithin_le_nhds hIoo] with r hr hrI
        by_contra hcon
        exact hr ⟨hmem r hrI, hcon⟩
    rw [← nhdsNE_sup_pure u]
    exact Filter.eventually_sup.mpr ⟨hfin, Filter.eventually_pure.mpr rfl⟩
  have hmI : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 =
      (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1 := by
    intro s hs
    by_contra hne
    have hUopen : IsOpen {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 =
        (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} :=
      isOpen_iff_mem_nhds.2 fun r hr ↦ eventually_eventually_nhds.2 hr
    have hVopen : IsOpen {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 ≠
        (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} :=
      isOpen_iff_mem_nhds.2 fun r hr ↦ eventually_eventually_nhds.2 hr
    have hcover : Set.Ioo a b ⊆
        {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 =
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} ∪
        {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 ≠
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} := by
      intro r hr
      by_cases hcase : (edgeVertices K (r : Real.Angle)).1 =
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1
      · exact Or.inl (by filter_upwards [hloc r hr] with x hx; rw [hx, hcase])
      · exact Or.inr (by filter_upwards [hloc r hr] with x hx; rw [hx]; exact hcase)
    obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_Ioo _ _ hUopen hVopen hcover
      ⟨(a + b) / 2, hmI, hloc _ hmI⟩
      ⟨s, hs, by filter_upwards [hloc s hs] with x hx; rw [hx]; exact hne⟩
    obtain ⟨y, hy1, hy2⟩ := (hxU.and hxV).exists
    exact hy2 hy1
  refine ⟨(edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1, hconst, ?_, ?_⟩
  · refine tendsto_nhds_unique (contact_oneSided_limits K a).1
      (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsGT hab] with r hr
    exact (hconst r hr).symm
  · refine tendsto_nhds_unique (contact_oneSided_limits K b).2.2.2.1
      (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsLT hab] with r hr
    exact (hconst r hr).symm

private theorem normalVector_chord_norm_le (t δ : ℝ) (hδnonneg : 0 ≤ δ) :
    ‖(1 - Real.cos δ) • normalVector (t : Real.Angle) -
      Real.sin δ • tangentVector (t : Real.Angle)‖ ≤ δ := by
  have huu : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 :=
    inner_normalVector_self t
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have huv : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 :=
    inner_normalVector_tangentVector t
  have hvu : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm]
    exact huv
  have hsqn : ‖(1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)‖ ^ 2 =
      2 - 2 * Real.cos (δ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hvv, huv, hvu]
    nlinarith [Real.sin_sq_add_cos_sq (δ)]
  have hznorm : ‖(1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)‖ ≤
      δ := by
    have hcosb : 1 - δ ^ 2 / 2 ≤ Real.cos (δ) :=
      Real.one_sub_sq_div_two_le_cos
    nlinarith [norm_nonneg ((1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)), hsqn, hδnonneg]
  exact hznorm

private theorem tangentArmLengths_snd_support (K : RightAngleCapSpace) :
    ∀ s : ℝ,
     (tangentArmLengths K s).2.1 = supportValue (K.val : Set Point) (s : Real.Angle) -
       inner ℝ (capVertices K s).2.1 (normalVector (s : Real.Angle)) ∧
     (tangentArmLengths K s).2.2 = supportValue (K.val : Set Point) (s : Real.Angle) -
       inner ℝ (capVertices K s).2.2 (normalVector (s : Real.Angle)) := by
  have hy : ∀ s : ℝ, inner ℝ
      (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner
      (normalVector (s : Real.Angle)) = supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s
    have hvu : inner ℝ (tangentVector (s : Real.Angle)) (normalVector (s : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector s
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self s, hvu]
    ring
  intro s
  constructor <;>
    · show inner ℝ (_ - _) (normalVector (s : Real.Angle)) = _
      rw [inner_sub_left, hy s]

theorem maximumPolygonCap_arm_cell (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions) :
    (∀ u ∈ Set.Ioo t (t + polygonStepSize n),
      (tangentArmLengths K u).2.1 ≤ (tangentArmLengths K t).2.1 ∧
      (tangentArmLengths K u).2.1 = (tangentArmLengths K u).2.2 ∧
      (tangentArmLengths K (t + polygonStepSize n)).2.2 ≤
        (tangentArmLengths K u).2.2) ∧
    (tangentArmLengths K t).2.1 -
      (tangentArmLengths K (t + polygonStepSize n)).2.2 ≤ 5 * polygonStepSize n := by
  classical
  obtain ⟨hdiam, harmbd⟩ := maximumPolygonCap_arm_bound n K hK
  obtain ⟨hn2, -, P, hPK, -⟩ := hK
  have hPKval : (P.val.val : ConvexBody Point) = K.val := congrArg Subtype.val hPK
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hδpos : 0 < polygonStepSize n := div_pos (by linarith) hnR
  have hδle : polygonStepSize n ≤ Real.pi / 4 := by
    show Real.pi / 2 / n ≤ Real.pi / 4
    rw [div_le_iff₀ hnR]
    nlinarith
  -- the cell lies in the parameter range and contains no grid direction
  have hcell0 : 0 ≤ t ∧ t + polygonStepSize n ≤ Real.pi / 2 := by
    rcases ht with rfl | ht'
    · exact ⟨le_rfl, by linarith⟩
    · obtain ⟨h1, h2⟩ := rightAngleSet_direction_bounds n hn ht'
      exact ⟨by linarith, by linarith⟩
  obtain ⟨ht0, htδ⟩ := hcell0
  have hnogrid : ∀ s ∈ Set.Ioo t (t + polygonStepSize n),
      s ∉ (rightAngleSet n hn).directions := by
    intro s hs hcon
    rcases ht with rfl | ht'
    · linarith [(rightAngleSet_direction_bounds n hn hcon).1, hs.2]
    · rcases rightAngleSet_direction_le_or_succ_le n hn hcon ht' with h | h
      · linarith [hs.1]
      · linarith [hs.2]
  -- no exposed edge has its normal inside the open cell, shifted or not
  have hdegen : ∀ s ∈ Set.Ioo t (t + polygonStepSize n),
      (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2 ∧
      (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2 := by
    intro s hs
    have hsI : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := rightAnglePolygonCap_edgeVertices_eq n hn2 P hsI (hnogrid s hs)
    rwa [hPKval] at h
  have hdegen2 : ∀ s ∈ Set.Ioo (t + Real.pi / 2) (t + polygonStepSize n + Real.pi / 2),
      (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2 := by
    intro s hs
    have hr : s - Real.pi / 2 ∈ Set.Ioo t (t + polygonStepSize n) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := (hdegen _ hr).2
    rwa [show s - Real.pi / 2 + Real.pi / 2 = s by ring] at h
  -- singleton contacts range over a finite set of constraint vertices
  have hdomain : (angleDomain (rightAngleSet n hn2)).Finite :=
    (((rightAngleSet n hn2).directions.finite_toSet.union
      ((rightAngleSet n hn2).directions.finite_toSet.image
        (fun r ↦ r + Real.pi / 2))).union
      ((Set.finite_singleton (Real.pi / 2)).insert (rightAngleSet n hn2).angle))
  have hNfin : (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain (rightAngleSet n hn2)) ∪
      capLowerNormals (rightAngleSet n hn2).angle).Finite :=
    (hdomain.image (fun r : ℝ ↦ (r : Real.Angle))).union
      ((Set.finite_singleton _).insert _)
  obtain ⟨Cs, hCsfin, -, hKCs⟩ := P.property.finite_constraints hNfin
  rw [hPKval] at hKCs
  have hSfin : (finiteConstraintVertices Cs).Finite :=
    finite_finiteConstraintVertices Cs hCsfin
  have hSmem : ∀ θ : Real.Angle, (edgeVertices K.val θ).1 = (edgeVertices K.val θ).2 →
      (edgeVertices K.val θ).1 ∈ finiteConstraintVertices Cs := by
    intro θ hθ
    refine singleton_exposedEdge_mem_finiteConstraintVertices Cs hCsfin K.val hKCs (t := θ) ?_
    rw [exposedEdge_eq_segment_edgeVertices, ← hθ, segment_same]
  -- the two contact points that are constant across the cell
  obtain ⟨A, hAcell, hAleft, hAright⟩ := exists_edgeVertices_const_of_degenerate K.val hSfin
    (a := t) (b := t + polygonStepSize n) (by linarith)
    (fun s hs ↦ (hdegen s hs).1) (fun s hs ↦ hSmem _ (hdegen s hs).1)
  obtain ⟨Cp, hCcell, hCleft, hCright⟩ := exists_edgeVertices_const_of_degenerate K.val hSfin
    (a := t + Real.pi / 2) (b := t + polygonStepSize n + Real.pi / 2) (by linarith)
    hdegen2 (fun s hs ↦ hSmem _ (hdegen2 s hs))
  -- the arm lengths in support-function coordinates
  have harm := tangentArmLengths_snd_support K
  have hAK : A ∈ (K.val : Set Point) := by
    rw [← hAleft]
    exact (edgeVertices_fst_mem K.val (t : Real.Angle)).1
  have hCK : Cp ∈ (K.val : Set Point) := by
    rw [← hCleft]
    exact (edgeVertices_fst_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hAsup : ∀ s : ℝ, (edgeVertices K.val (s : Real.Angle)).1 = A →
      inner ℝ A (normalVector (s : Real.Angle)) =
        supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s hsA
    rw [← hsA]
    exact (edgeVertices_fst_mem K.val (s : Real.Angle)).2
  have hAsup' : ∀ s : ℝ, (edgeVertices K.val (s : Real.Angle)).2 = A →
      inner ℝ A (normalVector (s : Real.Angle)) =
        supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s hsA
    rw [← hsA]
    exact (edgeVertices_snd_mem K.val (s : Real.Angle)).2
  -- the smooth comparison function and its sign conditions
  have hadd : ∀ s ε : ℝ, inner ℝ (A - Cp) (normalVector ((s + ε : ℝ) : Real.Angle)) =
      Real.cos ε * inner ℝ (A - Cp) (normalVector (s : Real.Angle)) +
      Real.sin ε * inner ℝ (A - Cp) (tangentVector (s : Real.Angle)) := by
    intro s ε
    rw [normalVector_add_real, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hDsign : ∀ s : ℝ, (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp →
      inner ℝ (A - Cp) (tangentVector (s : Real.Angle)) ≤ 0 := by
    intro s hsC
    rw [← normalVector_add_pi_div_two_real s, inner_sub_left]
    have hA' := inner_le_supportValue K.val hAK ((s + Real.pi / 2 : ℝ) : Real.Angle)
    have hC' : inner ℝ Cp (normalVector ((s + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K.val : Set Point) ((s + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← hsC]
      exact (edgeVertices_fst_mem K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2
    linarith
  have hgt : (tangentArmLengths K t).2.1 =
      inner ℝ (A - Cp) (normalVector (t : Real.Angle)) := by
    rw [(harm t).1, inner_sub_left, hAsup t hAleft,
      show (capVertices K t).2.1 = Cp from hCleft]
  have hgb : (tangentArmLengths K (t + polygonStepSize n)).2.2 =
      inner ℝ (A - Cp) (normalVector ((t + polygonStepSize n : ℝ) : Real.Angle)) := by
    rw [(harm (t + polygonStepSize n)).2, inner_sub_left,
      hAsup' (t + polygonStepSize n) hAright,
      show (capVertices K (t + polygonStepSize n)).2.2 = Cp from hCright]
  have hgu : ∀ u ∈ Set.Ioo t (t + polygonStepSize n),
      (tangentArmLengths K u).2.1 = inner ℝ (A - Cp) (normalVector (u : Real.Angle)) ∧
      (tangentArmLengths K u).2.2 = inner ℝ (A - Cp) (normalVector (u : Real.Angle)) := by
    intro u hu
    have hCu : (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp :=
      hCcell (u + Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hCu2 : (capVertices K u).2.2 = Cp := by
      rw [show (capVertices K u).2.2 =
        (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).2 from rfl, ← (hdegen u hu).2]
      exact hCu
    refine ⟨?_, ?_⟩
    · rw [(harm u).1, inner_sub_left, hAsup u (hAcell u hu),
        show (capVertices K u).2.1 = Cp from hCu]
    · rw [(harm u).2, inner_sub_left, hAsup u (hAcell u hu), hCu2]
  have hGt0 : 0 ≤ inner ℝ (A - Cp) (normalVector (t : Real.Angle)) := by
    rw [← hgt]
    exact ((harmbd t ⟨ht0, by linarith⟩).2.2.1).1
  have hGt5 : inner ℝ (A - Cp) (normalVector (t : Real.Angle)) ≤ 5 := by
    rw [← hgt]
    exact ((harmbd t ⟨ht0, by linarith⟩).2.2.1).2
  constructor
  · intro u hu
    have hCu : (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp :=
      hCcell (u + Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hGu0 : 0 ≤ inner ℝ (A - Cp) (normalVector (u : Real.Angle)) := by
      rw [← (hgu u hu).2]
      exact ((harmbd u ⟨by linarith [hu.1], by linarith [hu.2]⟩).2.2.2).1
    have hkey : inner ℝ (A - Cp) (normalVector (u : Real.Angle)) =
        Real.cos (u - t) * inner ℝ (A - Cp) (normalVector (t : Real.Angle)) +
        Real.sin (u - t) * inner ℝ (A - Cp) (tangentVector (t : Real.Angle)) := by
      rw [show ((u : ℝ) : Real.Angle) = ((t + (u - t) : ℝ) : Real.Angle) by
        rw [show t + (u - t) = u by ring], hadd]
    have hkey2 : inner ℝ (A - Cp) (normalVector ((t + polygonStepSize n : ℝ) : Real.Angle)) =
        Real.cos (t + polygonStepSize n - u) *
            inner ℝ (A - Cp) (normalVector (u : Real.Angle)) +
          Real.sin (t + polygonStepSize n - u) *
            inner ℝ (A - Cp) (tangentVector (u : Real.Angle)) := by
      rw [show ((t + polygonStepSize n : ℝ) : Real.Angle) =
        ((u + (t + polygonStepSize n - u) : ℝ) : Real.Angle) by
          rw [show u + (t + polygonStepSize n - u) = t + polygonStepSize n by ring], hadd]
    have hD := hDsign t hCleft
    have hDu := hDsign u hCu
    have hc1 : Real.cos (u - t) ≤ 1 := Real.cos_le_one _
    have hs1 : 0 ≤ Real.sin (u - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hu.1]) (by linarith [hu.2])
    have hc2 : Real.cos (t + polygonStepSize n - u) ≤ 1 := Real.cos_le_one _
    have hs2 : 0 ≤ Real.sin (t + polygonStepSize n - u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hu.2]) (by linarith [hu.1])
    refine ⟨?_, ?_, ?_⟩
    · rw [(hgu u hu).1, hgt, hkey]
      linarith [mul_nonneg (sub_nonneg.mpr hc1) hGt0,
        mul_nonneg hs1 (neg_nonneg.mpr hD)]
    · rw [(hgu u hu).1, (hgu u hu).2]
    · rw [hgb, (hgu u hu).2, hkey2]
      linarith [mul_nonneg (sub_nonneg.mpr hc2) hGu0,
        mul_nonneg hs2 (neg_nonneg.mpr hDu)]
  · have hD := hDsign t hCleft
    have hz : (tangentArmLengths K t).2.1 -
        (tangentArmLengths K (t + polygonStepSize n)).2.2 =
        inner ℝ (A - Cp)
          ((1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle)) := by
      rw [hgt, hgb, hadd t (polygonStepSize n), inner_sub_right, real_inner_smul_right,
        real_inner_smul_right]
      ring
    have hznorm := normalVector_chord_norm_le t (polygonStepSize n) hδpos.le
    have hwnorm : ‖A - Cp‖ ≤ 5 := by
      rw [← dist_eq_norm]
      exact le_trans (Metric.dist_le_diam_of_mem K.val.isCompact.isBounded hAK hCK) hdiam
    rw [hz]
    calc inner ℝ (A - Cp)
          ((1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle))
        ≤ ‖A - Cp‖ * ‖(1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle)‖ :=
          real_inner_le_norm _ _
      _ ≤ 5 * polygonStepSize n :=
          mul_le_mul hwnorm hznorm (norm_nonneg _) (by norm_num)

theorem polygonCap_arm_integral_limit (K : ℕ → RightAngleCapSpace)
    (L : RightAngleCapSpace)
    (hpolygon : ∀ i, ∃ (Θ : AngleSet) (P : PolygonCapSpace Θ),
      Θ.angle = Real.pi / 2 ∧ (P.val.val : Set Point) = ((K i).val : Set Point))
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
      |(tangentArmLengths (K i) t).2.1 - (tangentArmLengths L t).2.1|)
      atTop (𝓝 0) := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n).val, (surfaceAreaMeasure_face_union (K n).val).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L.val, (surfaceAreaMeasure_face_union L.val).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity (fun n ↦ (K n).val) L.val hlim f f.continuous
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := hμ.mass
  obtain ⟨M, hM⟩ := hmass.bddAbove_range
  have hmass_le (n : ℕ) : (μs n).mass ≤ M := hM ⟨n, rfl⟩
  have hcoe_inj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle))
      (Ioc 0 (Real.pi / 2)) :=
    Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos])
  have hshift_inj : Set.InjOn
      (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (Ioc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    apply hcoe_inj hx hy
    simp only [Real.Angle.coe_add] at hxy
    exact add_right_cancel hxy
  have hae_left : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      (μ : Measure Real.Angle) {(t : Real.Angle)} = 0 :=
    ae_measure_singleton_comp_eq_zero_of_injOn (μ : Measure Real.Angle)
      measurableSet_Ioc hcoe_inj
  have hae_right : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      (μ : Measure Real.Angle) {((t + Real.pi / 2 : ℝ) : Real.Angle)} = 0 :=
    ae_measure_singleton_comp_eq_zero_of_injOn (μ : Measure Real.Angle)
      measurableSet_Ioc hshift_inj
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      Tendsto (fun n ↦ (tangentArmLengths (K n) t).2.1) atTop
        (𝓝 (tangentArmLengths L t).2.1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_left, hae_right] with t ht hleft hright
    let A := (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)
    have hfrontier : (μ : Measure Real.Angle) (frontier A) = 0 := by
      apply measure_mono_null (Real.Angle.frontier_image_Ioc_subset
        (by linarith [Real.pi_pos]))
      simp only [insert_eq, measure_union_null hleft hright]
    have hAmeas : MeasurableSet A :=
      Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2)
    have hfrontier' : μ (frontier A) = 0 := by
      rw [← ENNReal.coe_eq_zero, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact hfrontier
    have hres := FiniteMeasure.tendsto_restrict_of_null_frontier
      hAmeas hμ hfrontier'
    let f : Real.Angle →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun u ↦ (u - (t : Real.Angle)).sin,
        Real.Angle.continuous_sin.comp (continuous_id.sub continuous_const)⟩
    have hint := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hres f
    change Tendsto (fun n ↦ ∫ u in A,
      (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure (K n).val) atTop
      (𝓝 (∫ u in A, (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure L.val)) at hint
    have hKt (n : ℕ) := tangentArm_convolution (K n) t ⟨ht.1.le, ht.2⟩
    have hLt := tangentArm_convolution L t ⟨ht.1.le, ht.2⟩
    simpa only [A, hKt, hLt] using hint
  have hmeas_arm := aestronglyMeasurable_tangentArm_fst
  have hbound_arm (C : RightAngleCapSpace) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
      |(tangentArmLengths C t).2.1| ≤
        (surfaceAreaMeasure C.val).real Set.univ := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
      (surfaceAreaMeasure_face_union C.val).1
    rw [tangentArm_convolution C t ht]
    change ‖∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2),
      (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure C.val‖ ≤ _
    calc
      ‖∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2),
          (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure C.val‖ ≤
          1 * (surfaceAreaMeasure C.val).real
            ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)) := by
            apply norm_setIntegral_le_of_norm_le_const
            · finiteness
            · intro u hu
              simp only [Real.norm_eq_abs]
              rw [← Real.Angle.sin_toReal]
              exact Real.abs_sin_le_one _
      _ ≤ (surfaceAreaMeasure C.val).real Set.univ := by
        simpa only [one_mul] using
          measureReal_mono (μ := surfaceAreaMeasure C.val) (Set.subset_univ _)
            (measure_ne_top _ _)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t ↦ |(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1|)
      (volume.restrict (Ioc 0 (Real.pi / 2))) := by
    intro n
    have hm := ((hmeas_arm (K n)).sub (hmeas_arm L)).norm
    convert hm using 1
  have hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      ‖|(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1|‖ ≤
        (M : ℝ) + (μ.mass : ℝ) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1| ≤
          |(tangentArmLengths (K n) t).2.1| + |(tangentArmLengths L t).2.1| :=
        abs_sub _ _
      _ ≤ (surfaceAreaMeasure (K n).val).real Set.univ +
          (surfaceAreaMeasure L.val).real Set.univ :=
        add_le_add (hbound_arm (K n) t ⟨ht.1.le, ht.2⟩)
          (hbound_arm L t ⟨ht.1.le, ht.2⟩)
      _ = ((μs n).mass : ℝ) + (μ.mass : ℝ) := by
        change (μs n : Measure Real.Angle).real univ +
          (μ : Measure Real.Angle).real univ = _
        simp [Measure.real, ← FiniteMeasure.ennreal_mass]
      _ ≤ (M : ℝ) + (μ.mass : ℝ) := by
        have hn : ((μs n).mass : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmass_le n
        exact add_le_add hn le_rfl
  have hlim_zero : ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      Tendsto (fun n ↦ |(tangentArmLengths (K n) t).2.1 -
        (tangentArmLengths L t).2.1|) atTop (𝓝 0) := by
    filter_upwards [hpoint] with t ht
    have hc : Tendsto (fun _ : ℕ ↦ (tangentArmLengths L t).2.1) atTop
        (𝓝 (tangentArmLengths L t).2.1) := tendsto_const_nhds
    simpa only [sub_self, abs_zero] using (ht.sub hc).abs
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 (Real.pi / 2)))
    (fun _ ↦ (M : ℝ) + (μ.mass : ℝ)) hmeas
    (integrableOn_const (μ := volume) (s := Ioc 0 (Real.pi / 2))
      (measure_Ioc_lt_top.ne)) hbound hlim_zero
  simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    integral_zero] using hdom

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Wedge Gap / Infimum
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- The two infima of the wedge-gap components over interior rotation angles. -/
def wedgeGapInfimum {ω : ℝ} (K : CapSpace ω) : ℝ × ℝ :=
  (sInf ((fun t ↦ (wedgeGaps K t).1) '' Set.Ioo 0 ω),
    sInf ((fun t ↦ (wedgeGaps K t).2) '' Set.Ioo 0 ω))

private theorem bddBelow_wedgeGaps_fst {ω : ℝ} (K : CapSpace ω) :
    BddBelow ((fun t ↦ (wedgeGaps K t).1) '' Ioo 0 ω) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := wedgeGaps_positive_lower_bound K t ht
  exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_nonneg {ω : ℝ} (K : CapSpace ω) :
    0 ≤ (wedgeGapInfimum K).1 := by
  rw [wedgeGapInfimum]
  apply le_csInf
  · exact (nonempty_Ioo.mpr K.property.1).image _
  · rintro _ ⟨t, ht, rfl⟩
    have h := wedgeGaps_positive_lower_bound K t ht
    exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_le_supportValue_zero {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤ supportValue K.val (0 : Real.Angle) := by
  let f := fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
    (supportValue K.val (t : Real.Angle) - 1) / Real.cos t
  have hcos : Real.cos ω ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩).ne'
  have hf : ContinuousAt f ω := continuousAt_const.sub
    (((continuous_supportValue_real K.val).continuousAt.sub continuousAt_const).div
      Real.continuous_cos.continuousAt hcos)
  have hf' : Tendsto f (𝓝[<] ω) (𝓝 (f ω)) :=
    hf.tendsto.mono_left inf_le_left
  have hlim : Tendsto f (𝓝[<] ω)
      (𝓝 (supportValue K.val (0 : Real.Angle))) := by
    convert hf' using 1
    simp [f, K.property.2.2.1]
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT K.property.1] with t ht
  rw [wedgeGapInfimum]
  have hle := csInf_le (bddBelow_wedgeGaps_fst K) ⟨t, ht, rfl⟩
  simpa only [f, wedgeGaps_fst_eq_supportValue] using hle

private def bottomGapSegment {ω : ℝ} (K : CapSpace ω) : Set Point :=
  let a := supportValue K.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K).1
  segment ℝ ((a - w) • normalVector (0 : Real.Angle))
    (a • normalVector (0 : Real.Angle))

private theorem point_eq_fst_smul_normalVector_zero_of_mem_normalLine
    {p : Point} (hp : p ∈ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    p = p 0 • normalVector (0 : Real.Angle) := by
  have hpy : p 1 = 0 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hp
    simpa [normalVector, frame, PiLp.inner_apply] using hp
  ext i
  fin_cases i <;> simp [normalVector, frame, hpy]

private theorem bottomGapSegment_subset_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    bottomGapSegment K.val ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let A := a • normalVector (0 : Real.Angle)
  let B := (a - w) • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := by
    exact supportValue_zero_smul_normalVector_mem K.val
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hwa : w ≤ a := wedgeGapInfimum_fst_le_supportValue_zero K.val hω
  have hBK : B ∈ (K.val.val : Set Point) := by
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK
      (sub_nonneg.mpr hwa) (by linarith)
  have hbottom : supportValue K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := K.val.property.2.2.2.2.2.1
  have hAedge : A ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [A, normalVector, frame]
  have hBedge : B ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hBK, ?_⟩
    change inner ℝ B (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [B, normalVector, frame]
  exact (convex_exposedEdge K.val.val _).segment_subset hBedge hAedge

private theorem polygonNiche_fanLine_fst_lt_gapStart {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {q : Point}
    (hq : q ∈ polygonNiche Θ K.val ∩
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    q 0 < supportValue K.val.val (0 : Real.Angle) -
      (wedgeGapInfimum K.val).1 := by
  obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq.1.2
  have htt := Θ.interior t ht
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hb
    simp only [wedgeEndpoints]
    simp [normalVector, frame]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hinf : (wedgeGapInfimum K.val).1 ≤ (wedgeGaps K.val t).1 := by
    rw [wedgeGapInfimum]
    exact csInf_le (bddBelow_wedgeGaps_fst K.val) ⟨t, htt, rfl⟩
  have hgap : (wedgeGaps K.val t).1 =
      supportValue K.val.val (0 : Real.Angle) - (wedgeEndpoints K.val t).1 0 := by
    rw [wedgeGaps_fst_eq_supportValue]
    simp [wedgeEndpoints, normalVector, frame]
  rw [hgap] at hinf
  linarith

private theorem polygonNiche_fanLine_subset_bottom_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  let a := supportValue K.val.val (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := supportValue_zero_smul_normalVector_mem K.val
  have hqx0 : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    have hqy : q 1 = 0 := by
      have hline := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
      simpa [normalVector, frame, PiLp.inner_apply] using hline
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hfan
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan)
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
  have hqxa : q 0 ≤ a := by
    have hlt := polygonNiche_fanLine_fst_lt_gapStart K hq
    have hw0 := wedgeGapInfimum_fst_nonneg K.val
    dsimp only [a]
    linarith
  have hqeq := point_eq_fst_smul_normalVector_zero_of_mem_normalLine hq.2
  have hqK : q ∈ (K.val.val : Set Point) := by
    rw [hqeq]
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK hqx0 hqxa
  refine ⟨hqK, ?_⟩
  change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.val.property.2.2.2.2.2.1]
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  rw [inner_normalVector_three_pi_div_two]
  simp [hqy]

private theorem bottomGapSegment_disjoint_polygonNiche_fanLine {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    Disjoint (bottomGapSegment K.val)
      (polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  rw [Set.disjoint_left]
  intro q hqS hqN
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let B := (a - w) • normalVector (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hqx : a - w ≤ q 0 := by
    change q ∈ segment ℝ B A at hqS
    rw [segment_eq_image'] at hqS
    obtain ⟨r, hr, rfl⟩ := hqS
    have heq : (B + r • (A - B)) 0 = a - w + r * w := by
      simp [B, A, normalVector, frame]
    rw [heq]
    nlinarith [hr.1]
  have hlt := polygonNiche_fanLine_fst_lt_gapStart K hqN
  exact (not_lt_of_ge hqx) (by simpa only [a, w] using hlt)

private theorem hausdorffMeasure_bottomGapSegment {ω : ℝ} (K : CapSpace ω) :
    (Measure.hausdorffMeasure 1 (bottomGapSegment K)).toReal =
      (wedgeGapInfimum K).1 := by
  have hw0 := wedgeGapInfimum_fst_nonneg K
  rw [show bottomGapSegment K =
      segment ℝ
        ((supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle))
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
    MeasureTheory.hausdorffMeasure_segment, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_eq_norm]
  have hdiff :
      (supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle) -
        supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) =
      (-(wedgeGapInfimum K).1) • normalVector (0 : Real.Angle) := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hw0,
    norm_normalVector, mul_one]

private theorem wedgeGapInfimum_fst_le_surface_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2)
    (hbal : IsBalancedPolygonCap K) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let S := bottomGapSegment K.val
  let M := polygonNiche Θ K.val ∩
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0
  let E := exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hSsub : S ⊆ E := bottomGapSegment_subset_exposedEdge K hω
  have hMsub : M ⊆ E := polygonNiche_fanLine_subset_bottom_exposedEdge K hω
  have hSMsub : S ∪ M ⊆ E := Set.union_subset hSsub hMsub
  have hdisj : Disjoint S M := bottomGapSegment_disjoint_polygonNiche_fanLine K
  have hMMeas : MeasurableSet M := by
    apply (measurableSet_polygonNiche Θ K.val).inter
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hSne : μ S ≠ ⊤ := by
    dsimp only [μ, S]
    rw [show bottomGapSegment K.val =
        segment ℝ
          ((supportValue K.val.val (0 : Real.Angle) - (wedgeGapInfimum K.val).1) •
            normalVector (0 : Real.Angle))
          (supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    exact ENNReal.ofReal_ne_top
  have hatom := surfaceAreaMeasure_atom_length K.val.val
    ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hEne : μ E ≠ ⊤ := by
    dsimp only [μ, E]
    rw [← hatom.1, hatom.2.1]
    exact ENNReal.ofReal_ne_top
  have hMne : μ M ≠ ⊤ := measure_ne_top_of_subset hMsub hEne
  have hunion := measureReal_union hdisj hMMeas hSne hMne
  have hmono : μ.real (S ∪ M) ≤ μ.real E :=
    ENNReal.toReal_mono hEne (measure_mono hSMsub)
  have hSreal : μ.real S = (wedgeGapInfimum K.val).1 := by
    exact hausdorffMeasure_bottomGapSegment K.val
  have hMreal : μ.real M =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal -
        polygonPolylineLengthAt K (Real.pi / 2) := by
    have h := (polygonCap_polyline_lengths K).2 (Real.pi / 2) (by simp)
    dsimp only [μ, M]
    change (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)).toReal = _
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    simpa only [hang] using h.2
  have hEreal : μ.real E =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    exact (congrArg ENNReal.toReal hatom.1).symm
  have htT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  let tT : angleDomain Θ := ⟨Real.pi / 2, htT⟩
  have hpoly0 : 0 ≤ polygonCapPolylineLength K tT := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
  have hbalReal :
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal =
        polygonCapPolylineLength K tT := by
    simpa only [tT, ENNReal.toReal_ofReal hpoly0] using
      congrArg ENNReal.toReal (hbal tT)
  have hlength : polygonPolylineLengthAt K (Real.pi / 2) =
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    simp only [polygonPolylineLengthAt, dite_eq_left htT]
    exact hbalReal.symm
  rw [hunion, hSreal, hMreal, hEreal, hlength] at hmono
  linarith

theorem maximumPolygonCap_gap_le_surface {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) (hω : Θ.angle < Real.pi / 2) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K.val).2 ≤
      (surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)}).toReal := by
  have hbal := maximumPolygonCap_balanced K hK
  refine ⟨wedgeGapInfimum_fst_le_surface_of_balanced K hω hbal, ?_⟩
  obtain ⟨Q, hQcarrier, hQmax⟩ := maximumPolygonCap_mirror Θ K hK
  obtain ⟨P, hPcarrier, _hHall, hgap, _hupper, _hniche, hsurface⟩ :=
    cap_mirror_features K.val
  have hPQ : P = Q.val := by
    apply Subtype.ext
    apply ConvexBody.ext
    exact hPcarrier.trans hQcarrier.symm
  have hQbal := maximumPolygonCap_balanced Q hQmax
  have hQright := wedgeGapInfimum_fst_le_surface_of_balanced Q hω hQbal
  have himage :
      (fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle =
        (fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      refine ⟨Θ.angle - t, ⟨by linarith, by linarith⟩, ?_⟩
      have hg := (hgap t ⟨ht0, htω⟩).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val t).1 = (wedgeGaps K.val (Θ.angle - t)).2 at hg
      exact hg.symm
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      have hcomp : Θ.angle - t ∈ Ioo 0 Θ.angle := ⟨by linarith, by linarith⟩
      refine ⟨Θ.angle - t, hcomp, ?_⟩
      have hg := (hgap (Θ.angle - t) hcomp).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val (Θ.angle - t)).1 =
        (wedgeGaps K.val (Θ.angle - (Θ.angle - t))).2 at hg
      simpa only [sub_sub_cancel] using hg
  have hinf : (wedgeGapInfimum Q.val).1 = (wedgeGapInfimum K.val).2 := by
    change sInf ((fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle) =
      sInf ((fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle)
    exact congrArg sInf himage
  have hsurface' :
      surfaceAreaMeasure Q.val.val {((Real.pi / 2 : ℝ) : Real.Angle)} =
        surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)} := by
    have hs := hsurface {((Real.pi / 2 : ℝ) : Real.Angle)}
      (measurableSet_singleton _)
    rw [hPQ] at hs
    rw [Set.image_singleton] at hs
    have hang :
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) -
            ((Real.pi / 2 : ℝ) : Real.Angle) =
          (Θ.angle : Real.Angle) := by
      rw [← Real.Angle.coe_sub]
      congr 1
      ring
    simpa only [hang] using hs
  rw [hinf, hsurface'] at hQright
  exact hQright

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Wedge Gap / Limit
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem wedgeGapInfimum_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).1 - (wedgeGapInfimum L).1| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).1
  let g := fun t : ℝ ↦ (wedgeGaps L t).1
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcost {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_lt hω⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos t := hcost ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le
        (by linarith [Real.pi_pos, hω]) ht.2.le
    dsimp only [f, g]
    rw [wedgeGaps_fst_eq_supportValue, wedgeGaps_fst_eq_supportValue]
    calc
      |(supportValue K.val (0 : Real.Angle) -
          (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) -
        (supportValue L.val (0 : Real.Angle) -
          (supportValue L.val (t : Real.Angle) - 1) / Real.cos t)| =
          |(supportValue K.val (0 : Real.Angle) -
              supportValue L.val (0 : Real.Angle)) -
            (supportValue K.val (t : Real.Angle) -
              supportValue L.val (t : Real.Angle)) / Real.cos t| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |(supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)) / Real.cos t| := abs_sub _ _
      _ = |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)| / Real.cos t := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos t := add_le_add (hsupport' 0)
        (div_le_div_of_nonneg_right (hsupport' t) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val (t : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hf_eq : f = fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue K t
    rw [hf_eq]
    convert continuousOn_const.sub hquot using 1
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val (t : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hg_eq : g = fun t : ℝ ↦ supportValue L.val (0 : Real.Angle) -
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue L t
    rw [hg_eq]
    convert continuousOn_const.sub hquot using 1
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

/-- The left wedge-gap infimum obeys the same Hausdorff estimate as the right one. -/
theorem wedgeGapInfimum_snd_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).2 - (wedgeGapInfimum L).2| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).2
  let g := fun t : ℝ ↦ (wedgeGaps L t).2
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcosδ {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos (ω - t) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.2], by linarith [Real.pi_pos, ht.1, hω]⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos (ω - t) := hcosδ ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos (ω - t) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2.le)
        (by linarith [Real.pi_pos, hω]) (by linarith [ht.1])
    dsimp only [f, g]
    rw [wedgeGaps_snd_eq_supportValue, wedgeGaps_snd_eq_supportValue]
    calc
      |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t)) -
        (supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t))| =
          |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)) -
            (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
                Real.cos (ω - t)| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |(supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
              Real.cos (ω - t)| := abs_sub _ _
      _ = |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)| /
              Real.cos (ω - t) := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos (ω - t) := add_le_add (hsupport' (ω + Real.pi / 2))
        (div_le_div_of_nonneg_right (hsupport' (t + Real.pi / 2)) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hf_eq : f = fun t : ℝ ↦
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue K t
    rw [hf_eq]
    exact continuousOn_const.sub hquot
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hg_eq : g = fun t : ℝ ↦
        supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue L t
    rw [hg_eq]
    exact continuousOn_const.sub hquot
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

theorem balancedMaximumCap_gap_le_surface {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤
      (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K).2 ≤
      (surfaceAreaMeasure K.val {(ω : Real.Angle)}).toReal := by
  obtain ⟨n, hn, _hmono, _hdyadic, P, hmax, hlim⟩ := hK
  let Θ (i : ℕ) := uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)
  have hpolygon (i : ℕ) := maximumPolygonCap_gap_le_surface (P i) (hmax i) hω
  have hfst : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).1) atTop
      (𝓝 (wedgeGapInfimum K).1) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_hausdorff_bound (P i).val K hω
  have hsnd : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).2) atTop
      (𝓝 (wedgeGapInfimum K).2) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_snd_hausdorff_bound (P i).val K hω
  constructor
  · exact le_surfaceAreaMeasure_atom_of_tendsto hlim hfst (fun i ↦ (hpolygon i).1)
  · apply le_surfaceAreaMeasure_atom_of_tendsto hlim hsnd
    intro i
    simpa only [Θ, uniformAngleSet] using (hpolygon i).2

end MovingSofa

end

end

end
