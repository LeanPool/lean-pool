/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements
public import Mathlib.Analysis.Complex.Circle
import LeanPool.GraphMinor.Surface.MoveCuff
import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Twisting a disc

For moving marked discs, as in XII (4.3), claim (7), page 251, and XIX (15.2), step (2), page 381, a
homeomorphism must carry the marked points on one disc to those on another. Any two ordered pairs of
distinct points of the circle are matched by a
homeomorphism of the circle that keeps its orientation (`exists_circle_pair_move`). Such a
homeomorphism extends to the plane, keeping the norm and fixing everything outside a ball
(`exists_twist`):
we extend it radially inside the unit disc, and undo it along the annulus by a homotopy from
`Surface/MoveCuff.lean`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Metric Filter Topology unitInterval

/-- The unit vector of a nonzero complex number. -/
noncomputable def unitOf (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨((‖z‖ : ℝ) : ℂ)⁻¹ * z, by
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk]
    change _ ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩

theorem coe_unitOf (z : ℂ) (hz : z ≠ 0) : (unitOf z hz : ℂ) = ((‖z‖ : ℝ) : ℂ)⁻¹ * z := rfl

theorem norm_mul_unitOf (z : ℂ) (hz : z ≠ 0) : ((‖z‖ : ℝ) : ℂ) * unitOf z hz = z := by
  rw [coe_unitOf, mul_inv_cancel_left₀]
  exact_mod_cast norm_ne_zero_iff.mpr hz

theorem unitOf_mul (r : ℝ) (hr : 0 < r) (w : Circle) (h : (r : ℂ) * w ≠ 0) : unitOf ((r : ℂ) * w) h
  = w := by
  apply Circle.ext
  rw [coe_unitOf, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hr.le, inv_mul_cancel_left₀]
  exact_mod_cast hr.ne'

/-- The parameter along the annulus: `0` up to radius one, and `1` from radius three halves on. -/
noncomputable def twistParam (r : ℝ) : I := Set.projIcc 0 1 zero_le_one (2 * r - 2)

theorem continuous_twistParam : Continuous twistParam :=
  continuous_projIcc.comp (by fun_prop)

theorem twistParam_low {r : ℝ} (h : r ≤ 1) : twistParam r = 0 :=
  Set.projIcc_of_le_left _ (by linarith)

theorem twistParam_high {r : ℝ} (h : 3 / 2 ≤ r) : twistParam r = 1 :=
  Set.projIcc_of_right_le _ (by linarith)

open Classical in
/-- The map that follows the homotopy `μ` along rays. -/
noncomputable def twistMap (μ : I × Circle → Circle) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0 else ((‖z‖ : ℝ) : ℂ) * μ (twistParam ‖z‖, unitOf z hz)

theorem norm_twistMap (μ : I × Circle → Circle) (z : ℂ) : ‖twistMap μ z‖ = ‖z‖ := by
  unfold twistMap
  split_ifs with hz
  · simp [hz]
  · rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, norm_norm]

theorem continuous_unitOf : Continuous fun z : {z : ℂ // z ≠ 0} => unitOf z.1 z.2 := by
  refine Continuous.subtype_mk ?_ _
  have h : Continuous fun z : {z : ℂ // z ≠ 0} => ((‖z.1‖ : ℝ) : ℂ)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun z => ?_
    exact_mod_cast norm_ne_zero_iff.mpr z.2
  exact h.mul continuous_subtype_val

theorem continuous_twistMap {μ : I × Circle → Circle} (hμ : Continuous μ) : Continuous (twistMap μ)
  := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : twistMap μ 0 = 0 := by simp [twistMap]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_twistMap]
    have := (continuous_norm (E := ℂ)).tendsto 0
    simpa using this
  · have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hmem : {z : ℂ | z ≠ 0} ∈ 𝓝 z := hopen.mem_nhds hz
    refine (ContinuousOn.continuousAt ?_ hmem)
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({z : ℂ | z ≠ 0}).domRestrict (twistMap μ) = fun x : {z : ℂ // z ≠ 0} =>
      ((‖x.1‖ : ℝ) : ℂ) * μ (twistParam ‖x.1‖, unitOf x.1 x.2) := by
      funext x
      change twistMap μ x.1 = _
      simp only [twistMap]
      rw [dite_eq_right x.2]
    rw [heq]
    refine Continuous.mul (by fun_prop) (continuous_induced_dom.comp (hμ.comp ?_))
    exact (continuous_twistParam.comp (by fun_prop)).prodMk continuous_unitOf

/-- A homeomorphism of the circle that keeps its orientation extends to the plane. The extension
keeps the norm, and it is the identity outside the ball of radius three halves. -/
theorem exists_twist {h : Circle ≃ₜ Circle} (hh : PreservesCircleOrientation h) :
    ∃ Θ : ℂ ≃ₜ ℂ, (∀ z, 3 / 2 ≤ ‖z‖ → Θ z = z) ∧ (∀ z, ‖Θ z‖ = ‖z‖) ∧ ∀ w : Circle, Θ w = h w := by
  obtain ⟨μ, hμc, hμ0, hμ1, hμb⟩ := exists_circle_homotopy hh
  have hc := continuous_twistMap hμc
  have hinj : Function.Injective (twistMap μ) := by
    intro z w he
    have hn : ‖z‖ = ‖w‖ := by rw [← norm_twistMap μ z, he, norm_twistMap]
    by_cases hz : z = 0
    · subst hz
      exact (norm_eq_zero.mp (by simpa using hn.symm)).symm
    · have hw : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa [h] using hn))
      simp only [twistMap, dite_eq_right hz, dite_eq_right hw] at he
      rw [← hn] at he
      have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have h1 := Circle.ext (mul_left_cancel₀ hr he)
      have h2 := (hμb _).1 h1
      rw [← norm_mul_unitOf z hz, ← norm_mul_unitOf w hw, ← hn, h2]
  have hsurj : Function.Surjective (twistMap μ) := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [twistMap, hw]⟩
    · obtain ⟨v, hv⟩ := (hμb (twistParam ‖w‖)).2 (unitOf w hw)
      have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hne : ((‖w‖ : ℝ) : ℂ) * v ≠ 0 := mul_ne_zero (by exact_mod_cast hpos.ne')
        (Circle.coe_ne_zero v)
      refine ⟨((‖w‖ : ℝ) : ℂ) * v, ?_⟩
      have hnorm : ‖((‖w‖ : ℝ) : ℂ) * v‖ = ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, norm_norm]
      simp only [twistMap, dite_eq_right hne]
      rw [unitOf_mul _ hpos v hne, hnorm]
      have hv' : μ (twistParam ‖w‖, v) = unitOf w hw := hv
      rw [hv', norm_mul_unitOf]
  have hproper : IsProperMap (twistMap μ) := by
    refine isProperMap_iff_tendsto_cocompact.mpr ⟨hc, ?_⟩
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simp only [norm_twistMap]
    exact tendsto_norm_cobounded_atTop
  let Θ : ℂ ≃ₜ ℂ := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hc
    hproper.isClosedMap
  have hΘ : ∀ z, Θ z = twistMap μ z := fun _ => rfl
  refine ⟨Θ, fun z hz => ?_, fun z => norm_twistMap μ z, fun w => ?_⟩
  · have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
    rw [hΘ]
    simp only [twistMap, dite_eq_right hz0]
    rw [twistParam_high hz, hμ1, norm_mul_unitOf]
  · have hw : (w : ℂ) ≠ 0 := Circle.coe_ne_zero w
    have hu : unitOf (w : ℂ) hw = w := by
      have := unitOf_mul 1 one_pos w (by simp [hw])
      simpa using this
    rw [hΘ]
    simp only [twistMap, dite_eq_right hw]
    rw [Circle.norm_coe, twistParam_low le_rfl, hμ0, hu]
    simp

theorem PreservesCircleOrientation.comp {h k : Circle ≃ₜ Circle} (hh : PreservesCircleOrientation
  h) (hk : PreservesCircleOrientation k) : PreservesCircleOrientation (k.trans h) := by
  obtain ⟨l, hl, hm, he⟩ := hh
  obtain ⟨l', hl', hm', he'⟩ := hk
  refine ⟨l ∘ l', hl.comp hl', hm.comp hm', fun t => ?_⟩
  change h (k _) = _
  rw [he', he]
  rfl

/-- Multiplication by a point of the circle keeps the orientation. -/
theorem preservesCircleOrientation_mul (c : Circle) : PreservesCircleOrientation
  (Homeomorph.mulLeft c) := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective c
  exact ⟨fun t => θ + t, by fun_prop, fun a b hab => by simpa using hab,
    fun t => by simp [Circle.exp_add]⟩

/-- Two ordered pairs of distinct points of the circle are matched by a homeomorphism that keeps the
orientation. -/
theorem exists_circle_pair_move {x y x' y' : Circle} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ h x = x' ∧ h y = y' := by
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x⁻¹ * y = ee s := by
    obtain ⟨v, hv⟩ := ee_surjective (x⁻¹ * y)
    refine ⟨Int.fract v, ?_, Int.fract_lt_one v, ?_⟩
    · refine lt_of_le_of_ne (Int.fract_nonneg v) fun h0 => hxy ?_
      have h1 : ee v = 1 := by
        have h2 : ee v = ee 0 := ee_eq_iff.mpr ⟨⌊v⌋, by
          have hvfloor := Int.fract_add_floor v
          rw [← h0] at hvfloor
          linarith⟩
        rw [h2]
        simp [ee]
      rw [hv] at h1
      exact (inv_mul_eq_one.mp h1)
    · rw [← hv]
      exact (ee_eq_iff.mpr ⟨⌊v⌋, (Int.fract_add_floor v).symm⟩ : ee v = ee (Int.fract v))
  obtain ⟨s', hs0', hs1', hs'⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x'⁻¹ * y' = ee s := by
    obtain ⟨v, hv⟩ := ee_surjective (x'⁻¹ * y')
    refine ⟨Int.fract v, ?_, Int.fract_lt_one v, ?_⟩
    · refine lt_of_le_of_ne (Int.fract_nonneg v) fun h0 => hxy' ?_
      have h1 : ee v = 1 := by
        have h2 : ee v = ee 0 := ee_eq_iff.mpr ⟨⌊v⌋, by
          have hvfloor := Int.fract_add_floor v
          rw [← h0] at hvfloor
          linarith⟩
        rw [h2]
        simp [ee]
      rw [hv] at h1
      exact (inv_mul_eq_one.mp h1)
    · rw [← hv]
      exact (ee_eq_iff.mpr ⟨⌊v⌋, (Int.fract_add_floor v).symm⟩ : ee v = ee (Int.fract v))
  have hc : Continuous (tentMap 0 s s' 1) := by
    unfold tentMap tent
    fun_prop
  have hinj : Function.Injective (tentMap 0 s s' 1) :=
    Function.LeftInverse.injective (g := tentMap 0 s' s 1) fun y => tentMap_inv hs0 hs1 hs0' hs1'
  have h00 : tentMap 0 s s' 1 0 = 0 := by rw [tentMap, tent_low hs0 hs1 le_rfl]; ring
  have h11 : tentMap 0 s s' 1 1 = 1 := by rw [tentMap, tent_high hs0 hs1 le_rfl]; ring
  have hss : tentMap 0 s s' 1 s = s' := by
    rw [tentMap, tent_left hs0 hs1 hs0.le le_rfl, sub_zero, div_self hs0.ne']
    ring
  have hmono : StrictMono (tentMap 0 s s' 1) := by
    rcases hc.strictMono_of_inj hinj with h | h
    · exact h
    · have := h zero_lt_one
      rw [h00, h11] at this
      linarith
  obtain ⟨h₀, ho, he⟩ := exists_circle_homeo hc.continuousOn (hmono.strictMonoOn _)
    (by rw [h00, h11]; ring)
  refine ⟨(Homeomorph.mulLeft x⁻¹).trans (h₀.trans (Homeomorph.mulLeft x')), ?_, ?_, ?_⟩
  · exact PreservesCircleOrientation.comp (PreservesCircleOrientation.comp
    (preservesCircleOrientation_mul x') ho) (preservesCircleOrientation_mul _)
  · change x' * h₀ (x⁻¹ * x) = x'
    have h1 := he 0 ⟨le_rfl, zero_le_one⟩
    rw [h00] at h1
    have h2 : ee 0 = 1 := by simp [ee]
    rw [h2] at h1
    rw [inv_mul_cancel, h1, mul_one]
  · change x' * h₀ (x⁻¹ * y) = y'
    rw [hs, he s ⟨hs0.le, hs1.le⟩, hss, ← hs', mul_inv_cancel_left]

end GraphMinor.Surface
