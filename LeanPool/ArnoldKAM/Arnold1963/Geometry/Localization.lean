/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyChart
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.SlabMeasure

/-!
Construct a local frequency chart from nondegeneracy at a real point, before choosing a
perturbation. The frequency domain is a real-centered closed polydisc; the action domain is
its analytic inverse image and need not be convex.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal
namespace KamProject.Arnold1963

theorem realCenteredPolydisc_const_eq_closedBall {n : ℕ} (c : RealSpace n)
    {r : ℝ} (hr : 0 ≤ r) :
    realCenteredPolydisc c (fun _ => r) = closedBall (complexify c) r := by
  ext z
  simp only [realCenteredPolydisc, mem_ofPred_eq, mem_closedBall, dist_eq_norm,
    pi_norm_le_iff_of_nonneg hr, Pi.sub_apply, complexify]

theorem exists_polydisc_frequency_chart {n : ℕ}
    {A : ComplexSpace n → ComplexSpace n} {V : Set (ComplexSpace n)}
    (x : RealSpace n) (hV : V ∈ 𝓝 (complexify x))
    (ha : AnalyticAt ℂ A (complexify x))
    (hu : IsUnit (fderiv ℂ A (complexify x)))
    (hc : ∀ p ∈ V, A (conjVec p) = conjVec (A p)) :
    ∃ (g : ComplexSpace n → ComplexSpace n) (G : Set (ComplexSpace n))
      (r : ℝ), 0 < r ∧ G ⊆ V ∧ complexify x ∈ interior G ∧
      AnalyticFrequencyChart A g G
        (realCenteredPolydisc (realPart (A (complexify x))) (fun _ => r)) := by
  obtain ⟨u, hu⟩ := hu
  let i : ComplexSpace n ≃L[ℂ] ComplexSpace n := ContinuousLinearEquiv.ofUnit u
  have hi : fderiv ℂ A (complexify x) = (i : ComplexSpace n →L[ℂ] ComplexSpace n) := hu.symm
  have hd : HasStrictFDerivAt A (i : ComplexSpace n →L[ℂ] ComplexSpace n) (complexify x) := by
    rw [← hi]
    exact ha.hasStrictFDerivAt
  let R := hd.toOpenPartialHomeomorph A
  have hx : complexify x ∈ R.source := hd.mem_toOpenPartialHomeomorph_source
  have hAx : A (complexify x) ∈ R.target := hd.image_mem_toOpenPartialHomeomorph_target
  have hg : AnalyticAt ℂ R.symm (A (complexify x)) := R.analyticAt_symm' hx ha hi
  have he : R.symm (A (complexify x)) = complexify x := R.left_inv hx
  have hgood : ∀ᶠ p in 𝓝 (complexify x),
      p ∈ R.source ∧ p ∈ V ∧ AnalyticAt ℂ A p := by
    filter_upwards [R.open_source.mem_nhds hx, hV, ha.eventually_analyticAt] with p hp hpV hpA
    exact ⟨hp, hpV, hpA⟩
  obtain ⟨a, ha0, hab⟩ := Metric.mem_nhds_iff.mp hgood
  have hga : ∀ᶠ y in 𝓝 (A (complexify x)), R.symm y ∈ ball (complexify x) a := by
    apply hg.continuousAt.tendsto.eventually
    rw [he]
    exact ball_mem_nhds _ ha0
  have ht : ∀ᶠ y in 𝓝 (A (complexify x)),
      y ∈ R.target ∧ R.symm y ∈ ball (complexify x) a ∧ AnalyticAt ℂ R.symm y := by
    filter_upwards [R.open_target.mem_nhds hAx, hga, hg.eventually_analyticAt] with y hy hyb hya
    exact ⟨hy, hyb, hya⟩
  obtain ⟨r, hr, hrt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ht
  let Ω := closedBall (A (complexify x)) r
  let G := R.symm '' Ω
  have hΩ : ∀ y ∈ Ω, y ∈ R.target ∧ R.symm y ∈ ball (complexify x) a ∧
      AnalyticAt ℂ R.symm y := fun _ hy => hrt hy
  have hright : ∀ y ∈ Ω, A (R.symm y) = y := fun y hy => R.right_inv (hΩ y hy).1
  have hG : ∀ p ∈ G, p ∈ R.source ∧ p ∈ V ∧ AnalyticAt ℂ A p := by
    rintro p ⟨y, hy, rfl⟩
    exact hab (hΩ y hy).2.1
  have hcenter : conjVec (A (complexify x)) = A (complexify x) := by
    simpa only [conjVec_complexify] using (hc _ (mem_of_mem_nhds hV)).symm
  have hΩc : ConjInvariant Ω := by
    intro y hy
    change dist (star y) (A (complexify x)) ≤ r
    change dist y (A (complexify x)) ≤ r at hy
    rw [← hcenter, conjVec_eq_star, dist_star_star]
    exact hy
  have hGc : ConjInvariant G := by
    rintro p ⟨y, hy, rfl⟩
    have hp := (hΩ y hy).2.1
    have hpc : conjVec (R.symm y) ∈ ball (complexify x) a := by
      change dist (star (R.symm y)) (complexify x) < a
      have hxstar : star (complexify x) = complexify x := conjVec_complexify x
      rw [← hxstar, dist_star_star]
      exact hp
    have hmap : A (conjVec (R.symm y)) = conjVec y := by
      rw [hc _ (hab hp).2.1, hright y hy]
    refine ⟨conjVec y, hΩc _ hy, ?_⟩
    rw [← hmap]
    exact R.left_inv (hab hpc).1
  have hchart : AnalyticFrequencyChart A R.symm G Ω := {
    compact := (isCompact_closedBall _ _).image_of_continuousOn
      (fun y hy => (hΩ y hy).2.2.continuousAt.continuousWithinAt)
    analytic := fun p hp => (hG p hp).2.2
    inverse_analytic := fun y hy => (hΩ y hy).2.2
    maps := by
      rintro p ⟨y, hy, rfl⟩
      simpa only [hright y hy] using hy
    inverse_maps := fun y hy => ⟨y, hy, rfl⟩
    left_local := fun p hp => R.eventually_left_inverse (hG p hp).1
    right_local := fun y hy => R.eventually_right_inverse (hΩ y hy).1
    domain_conj := hGc
    map_conj := fun p hp => hc p (hG p hp).2.1 }
  have hxG : complexify x ∈ G := ⟨A (complexify x), mem_closedBall_self hr.le, he⟩
  refine ⟨R.symm, G, r, hr, fun p hp => (hG p hp).2.1,
    hchart.interior_back hxG ?_, ?_⟩
  · exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hr)
  · rw [realCenteredPolydisc_const_eq_closedBall _ hr.le,
      complexify_realPart_of_conj hcenter]
    exact hchart

theorem AnalyticFrequencyChart.exists_derivative_bounds {n : ℕ}
    {A g : ComplexSpace n → ComplexSpace n} {G Ω : Set (ComplexSpace n)}
    (c : AnalyticFrequencyChart A g G Ω) :
    ∃ θ Θ : ℝ≥0, 0 < θ ∧ θ < 1 ∧ 1 < Θ ∧
      (∀ p ∈ G, ∀ v, (θ : ℝ) * ‖v‖ ≤ ‖fderiv ℂ A p v‖) ∧
      (∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ Θ) := by
  obtain ⟨B, hB⟩ := c.compact.exists_bound_of_continuousOn c.analytic.fderiv.continuousOn
  obtain ⟨C, hC⟩ := c.image_compact.exists_bound_of_continuousOn
    c.inverse_analytic.fderiv.continuousOn
  let L := |C| + 2
  have hL : 1 < L := by dsimp [L]; linarith [abs_nonneg C]
  let θ : ℝ≥0 := ⟨L⁻¹, inv_nonneg.mpr (le_of_lt (zero_lt_one.trans hL))⟩
  let Θ : ℝ≥0 := ⟨|B| + 2, by positivity⟩
  refine ⟨θ, Θ, ?_, ?_, ?_, ?_, fun p hp => (hB p hp).trans ?_⟩
  · exact inv_pos.mpr (zero_lt_one.trans hL)
  · exact inv_lt_one_of_one_lt₀ hL
  · change (1 : ℝ) < |B| + 2
    linarith [abs_nonneg B]
  · intro p hp v
    have hd := (c.inverse_analytic _ (c.maps hp)).differentiableAt.hasFDerivAt.comp p
      (c.analytic _ hp).differentiableAt.hasFDerivAt
    have heq : (fun x => g (A x)) =ᶠ[𝓝 p] id := c.left_local p hp
    have hid : (fderiv ℂ g (A p)).comp (fderiv ℂ A p) = ContinuousLinearMap.id ℂ _ :=
      (hd.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id p)
    have hv : ‖v‖ ≤ L * ‖fderiv ℂ A p v‖ := by
      calc
        ‖v‖ = ‖fderiv ℂ g (A p) (fderiv ℂ A p v)‖ := by
          rw [← ContinuousLinearMap.comp_apply, hid, ContinuousLinearMap.id_apply]
        _ ≤ ‖fderiv ℂ g (A p)‖ * ‖fderiv ℂ A p v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖fderiv ℂ A p v‖ := mul_le_mul_of_nonneg_right
          ((hC _ (c.maps hp)).trans (by dsimp [L]; linarith [le_abs_self C])) (norm_nonneg _)
    change L⁻¹ * ‖v‖ ≤ _
    calc
      L⁻¹ * ‖v‖ ≤ L⁻¹ * (L * ‖fderiv ℂ A p v‖) :=
        mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (le_of_lt (zero_lt_one.trans hL)))
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans hL)), one_mul]
  · change B ≤ |B| + 2
    linarith [le_abs_self B]

end KamProject.Arnold1963
