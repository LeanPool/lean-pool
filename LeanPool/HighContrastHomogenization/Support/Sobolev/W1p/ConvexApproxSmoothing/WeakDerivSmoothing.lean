/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp

/-!
# Coarse-graining support: Support.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

open scoped Pointwise Convolution

/-!
# Weak derivatives of the convex smoothing operator

Lifts `HasWeakPartialDerivOn` (and the `HasWeakGradientOn` gradient variant)
through `convexApproxSmoothing` and the globally smooth representative
`convexApproxSmoothRepresentative`.
-/

private theorem integral_convexApproxSmoothing_compactlySupportedTestPairing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {f ρ : Vec d → ℝ}
    (hfLoc : MeasureTheory.LocallyIntegrableOn f U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {ψ : Vec d → ℝ} (hψ_cont : Continuous ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ U) :
    ∫ x in U, HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
        ∂MeasureTheory.volume =
      ∫ z in tsupport ρ,
        ∫ x in tsupport ψ,
          ρ z * Set.indicator U f (convexApproxSample x0 z r ε x) * ψ x
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  let F : Vec d → Vec d → ℝ := fun x z =>
    ρ z * Set.indicator U f (convexApproxSample x0 z r ε x) * ψ x
  have hprod :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => F p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport ψ)).prod
          (MeasureTheory.volume.restrict (tsupport ρ))) := by
    simpa [F] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_locallyIntegrableOn
        hU hfLoc hρ hψ_cont hψ_compact hψ_sub hball hr hε0 hε1
  have hswap :
      ∫ x in tsupport ψ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume =
        ∫ z in tsupport ρ, ∫ x in tsupport ψ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict (tsupport ψ))
        (ν := MeasureTheory.volume.restrict (tsupport ρ)) (f := F) hprod)
  have hrestrict :
      ∫ x in U, HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
          ∂MeasureTheory.volume =
        ∫ x in tsupport ψ,
          HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
            ∂MeasureTheory.volume := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.1.measurableSet hψ_sub (fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2])
  have hinner :
      ∫ x in tsupport ψ,
          HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
            ∂MeasureTheory.volume =
        ∫ x in tsupport ψ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hψ_compact.isCompact.measurableSet ?_
    intro x hx
    have hxU : x ∈ U := hψ_sub hx
    have hsample_mem : ∀ z ∈ tsupport ρ, convexApproxSample x0 z r ε x ∈ U := by
      intro z hz
      have hz_norm : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
      exact convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm
        hε0 (le_of_lt hε1) hxU
    calc
      HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
          = (∫ z in tsupport ρ, ρ z * f (convexApproxSample x0 z r ε x)
              ∂MeasureTheory.volume) * ψ x := rfl
      _ = ∫ z in tsupport ρ,
            (ρ z * f (convexApproxSample x0 z r ε x)) * ψ x
              ∂MeasureTheory.volume := by rw [← MeasureTheory.integral_mul_const]
      _ = ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun hρ.compactSupport.isCompact.measurableSet ?_
        intro z hz
        let y := convexApproxSample x0 z r ε x
        have hy_mem : y ∈ U := hsample_mem z hz
        change ρ z * f y * ψ x = ρ z * Set.indicator U f y * ψ x
        rw [Set.indicator_of_mem hy_mem]
  calc
    ∫ x in U, HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
        ∂MeasureTheory.volume =
      ∫ x in tsupport ψ,
        HCPolySupport.convexApproxSmoothing ρ f x0 r ε x * ψ x
          ∂MeasureTheory.volume := hrestrict
    _ = ∫ x in tsupport ψ, ∫ z in tsupport ρ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := hinner
    _ = ∫ z in tsupport ρ, ∫ x in tsupport ψ, F x z ∂MeasureTheory.volume
          ∂MeasureTheory.volume := hswap

private theorem convexApproxSample_integral_weakPartialDerivative
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi) (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {φ : Vec d → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    (z : Vec d) (hz : z ∈ tsupport ρ) :
    ∫ x in tsupport (fun x => (fderiv ℝ φ x) (basisVec i)),
        ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) *
          (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in tsupport (fun x => (1 - ε) * φ x),
        ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) *
          ((1 - ε) * φ x) ∂MeasureTheory.volume := by
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let φε : Vec d → ℝ := fun x => (1 - ε) * φ x
  have hdφ_support_sub : tsupport dφ ⊆ U := by
    apply (closure_minimal ?_ (isClosed_tsupport (f := φ))).trans hφ_sub
    intro x hx
    exact (support_fderiv_subset (𝕜 := ℝ) (f := φ)) <| by
      change fderiv ℝ φ x ≠ 0
      intro hzero
      apply hx
      simp [dφ, hzero]
  have hφε_sub : tsupport φε ⊆ U := by
    simpa only [φε] using
      (tsupport_mul_subset_right (f := fun _ : Vec d => 1 - ε) (g := φ)).trans hφ_sub
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hz
  have hmap : Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz_norm hε0
      (le_of_lt hε1)
  have hweak_z :
      ∫ x in U, u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume =
        -∫ x in U,
          ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
            ∂MeasureTheory.volume := by
    simpa [dφ] using
      ((hu.comp_convexApproxSample hU hball hr hz_norm hε0 hε1)
        φ hφ_smooth hφ_compact hφ_sub)
  have hleft :
      ∫ x in tsupport dφ,
          ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
            ∂MeasureTheory.volume =
        ρ z * ∫ x in U,
          u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
    calc
      _ = ∫ x in U,
            ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          hU.1.measurableSet hdφ_support_sub (fun x hx => by
            simp [dφ, image_eq_zero_of_notMem_tsupport hx.2])
      _ = ∫ x in U,
            ρ z * (u (convexApproxSample x0 z r ε x) * dφ x)
              ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
        intro x hx
        dsimp only [φε]
        rw [Set.indicator_of_mem (hmap hx)]
        ring
      _ = ρ z * ∫ x in U,
            u (convexApproxSample x0 z r ε x) * dφ x ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_const_mul]
  have hright :
      ∫ x in tsupport φε,
          ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
            ∂MeasureTheory.volume =
        ρ z * ∫ x in U,
          ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
            ∂MeasureTheory.volume := by
    calc
      _ = ∫ x in U,
            ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
              ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          hU.1.measurableSet hφε_sub (fun x hx => by
            simp [φε, image_eq_zero_of_notMem_tsupport hx.2])
      _ = ∫ x in U,
            ρ z * (((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x)
              ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
        intro x hx
        dsimp only [φε]
        rw [Set.indicator_of_mem (hmap hx)]
        ring
      _ = ρ z * ∫ x in U,
            ((1 - ε) * gi (convexApproxSample x0 z r ε x)) * φ x
              ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_const_mul]
  change
    ∫ x in tsupport dφ,
        ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
          ∂MeasureTheory.volume =
      -∫ x in tsupport φε,
        ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
          ∂MeasureTheory.volume
  rw [hleft, hright, hweak_z]
  ring

theorem HasWeakPartialDerivOn.convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (HCPolySupport.convexApproxSmoothing ρ u x0 r ε)
      (fun x => (1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) := by
  intro φ hφ_smooth hφ_compact hφ_sub
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let φε : Vec d → ℝ := fun x => (1 - ε) * φ x
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdφ_sub : tsupport dφ ⊆ U := by
    apply (closure_minimal ?_ (isClosed_tsupport (f := φ))).trans hφ_sub
    intro x hx
    exact (support_fderiv_subset (𝕜 := ℝ) (f := φ)) <| by
      change fderiv ℝ φ x ≠ 0
      intro hzero
      apply hx
      simp [dφ, hzero]
  have hφε_cont : Continuous φε := by
    simpa [φε] using! continuous_const.mul hφ_smooth.continuous
  have hφε_compact : HasCompactSupport φε := by
    simpa [φε] using! (HasCompactSupport.mul_left (f := fun _ : Vec d => 1 - ε) hφ_compact)
  have hφε_sub : tsupport φε ⊆ U := by
    simpa only [φε] using
      (tsupport_mul_subset_right (f := fun _ : Vec d => 1 - ε) (g := φ)).trans hφ_sub
  have hleft := integral_convexApproxSmoothing_compactlySupportedTestPairing
    hU huLoc hρ hball hr hε0 hε1 hdφ_cont hdφ_compact hdφ_sub
  have hright := integral_convexApproxSmoothing_compactlySupportedTestPairing
    hU hgiLoc hρ hball hr hε0 hε1 hφε_cont hφε_compact hφε_sub
  have hfixed :
      ∀ z ∈ tsupport ρ,
        ∫ x in tsupport dφ,
          ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
            ∂MeasureTheory.volume =
          -∫ x in tsupport φε,
            ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
              ∂MeasureTheory.volume := by
    intro z hz
    simpa [dφ, φε] using
      convexApproxSample_integral_weakPartialDerivative hU hu hρ hball hr
        hε0 hε1 hφ_smooth hφ_compact hφ_sub z hz
  have hfixed_integrated :
      ∫ z in tsupport ρ,
          ∫ x in tsupport dφ,
            ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume ∂MeasureTheory.volume =
        ∫ z in tsupport ρ,
          -∫ x in tsupport φε,
            ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
              ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hρ.compactSupport.isCompact.measurableSet ?_
    intro z hz
    exact hfixed z hz
  calc
    ∫ x in U,
        HCPolySupport.convexApproxSmoothing ρ u x0 r ε x * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume =
      ∫ x in U, HCPolySupport.convexApproxSmoothing ρ u x0 r ε x * dφ x
        ∂MeasureTheory.volume := by simp [dφ]
    _ = ∫ z in tsupport ρ,
          ∫ x in tsupport dφ,
            ρ z * Set.indicator U u (convexApproxSample x0 z r ε x) * dφ x
              ∂MeasureTheory.volume ∂MeasureTheory.volume := hleft
    _ = ∫ z in tsupport ρ,
          -∫ x in tsupport φε,
            ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
              ∂MeasureTheory.volume ∂MeasureTheory.volume := hfixed_integrated
    _ = -∫ z in tsupport ρ,
          ∫ x in tsupport φε,
            ρ z * Set.indicator U gi (convexApproxSample x0 z r ε x) * φε x
              ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_neg]
    _ = -∫ x in U, HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x * φε x
          ∂MeasureTheory.volume := by
        rw [← hright]
    _ = -∫ x in U, ((1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) * φ x
          ∂MeasureTheory.volume := by
        congr 1
        refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
        intro x hx
        ring

theorem HasWeakGradientOn.convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d, MeasureTheory.LocallyIntegrableOn (fun x => Du x i) U
      MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (HCPolySupport.convexApproxSmoothing ρ u x0 r ε)
      (fun x i => (1 - ε) * HCPolySupport.convexApproxSmoothing ρ (fun y => Du y i) x0 r ε x) := by
  intro i
  simpa using
    (HasWeakPartialDerivOn.convexApproxSmoothing (i := i) hU huLoc (hDuLoc i) (hu i) hρ
      hball hr hε0 hε1)

theorem HasWeakPartialDerivOn.convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x => (1 - ε) *
        HCPolySupport.convexApproxSmoothRepresentative U ρ gi x0 r ε x) := by
  intro φ hφ_smooth hφ_compact hφ_sub
  have hweak :
      HasWeakPartialDerivOn U i
        (HCPolySupport.convexApproxSmoothing ρ u x0 r ε)
        (fun x => (1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) :=
    HasWeakPartialDerivOn.convexApproxSmoothing (i := i) hU huLoc hgiLoc hu hρ hball
      hr.le hε0.le hε1
  have hleft :
      ∫ x in U,
          HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U,
          HCPolySupport.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
    intro x hx
    have hrep :
        HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε x =
          HCPolySupport.convexApproxSmoothing ρ u x0 r ε x :=
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := u) hU hρ hx hball hr hε0 hε1
    change
      HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i) =
        HCPolySupport.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
    rw [hrep]
  have hright :
      ∫ x in U,
          ((1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume =
        ∫ x in U,
          ((1 - ε) * HCPolySupport.convexApproxSmoothRepresentative U ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU.1.measurableSet ?_
    intro x hx
    have hrep :
        HCPolySupport.convexApproxSmoothRepresentative U ρ gi x0 r ε x =
          HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x :=
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := gi) hU hρ hx hball hr hε0 hε1
    change
      ((1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) * φ x =
        ((1 - ε) * HCPolySupport.convexApproxSmoothRepresentative U ρ gi x0 r ε x) *
          φ x
    rw [hrep]
  calc
    ∫ x in U,
        HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U,
            HCPolySupport.convexApproxSmoothing ρ u x0 r ε x *
              (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := hleft
    _ = -∫ x in U,
          ((1 - ε) * HCPolySupport.convexApproxSmoothing ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume :=
        hweak φ hφ_smooth hφ_compact hφ_sub
    _ = -∫ x in U,
          ((1 - ε) * HCPolySupport.convexApproxSmoothRepresentative U ρ gi x0 r ε x) * φ x
            ∂MeasureTheory.volume := by
        rw [hright]

theorem HasWeakGradientOn.convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d, MeasureTheory.LocallyIntegrableOn (fun x => Du x i) U
      MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (HCPolySupport.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x i => (1 - ε) *
        HCPolySupport.convexApproxSmoothRepresentative U ρ (fun y => Du y i) x0 r ε x) := by
  intro i
  simpa using
    (HasWeakPartialDerivOn.convexApproxSmoothRepresentative (i := i) hU huLoc (hDuLoc i)
      (hu i) hρ hball hr hε0 hε1)

end HCPolySupport
