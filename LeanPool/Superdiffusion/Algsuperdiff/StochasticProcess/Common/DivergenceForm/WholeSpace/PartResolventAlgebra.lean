/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Comparison
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAt

/-!
# PartResolventAlgebra

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The algebra of the Dirichlet resolvent of a bounded part domain

`partC0Resolvent` is the Dirichlet resolvent of a bounded measurable datum on an arbitrary
bounded open convex domain, extended by zero.  This file records the elementary operations it
supports, each one the domain-generic form of the corresponding statement about the resolvent of
an exhaustion cube:

* `partC0Resolvent_eq_of_eqOn` — only the restriction of the datum to the domain is seen;
* `abs_partC0Resolvent_le` — the shift-dependent maximum-principle bound `D / mu`;
* `partC0Resolvent_add`, `partC0Resolvent_smul`, `partC0Resolvent_add_const_mul` — linearity in
  the datum;
* `partC0Resolvent_mono` — monotonicity in the datum;
* `partC0Resolvent_resolvent_identity` — the resolvent identity in the shift.

Every proof is the corresponding proof for an exhaustion cube with the cube replaced by the
domain: the analytic representative `continuousCoeffBoundedResolvent` and all of its lemmas are
already stated for an arbitrary bounded open convex domain, and the ellipticity certificate is
the one `partEllipticity` supplies.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## Measurability -/

/-- **The Dirichlet resolvent of a part domain is measurable on the ambient space.**  It is the
zero extension of the restriction to the domain of a function continuous there. -/
theorem measurable_partC0Resolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.partC0Resolvent hV mu f hf hfD) := by
  set h : Vec d → ℝ := continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu
    (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
    (hf.comp measurable_subtype_coe) (fun z ↦ hfD z) with hhdef
  have hcont : ContinuousOn h V :=
    continuousOn_continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu (partEllipticity A hV)
      A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hf.comp measurable_subtype_coe) (fun z ↦ hfD z)
  have hmeas : Measurable fun y : V ↦ h y := hcont.domRestrict.measurable
  have heq : A.partC0Resolvent hV mu f hf hfD = domainExtension fun y : V ↦ h y := by
    funext x
    by_cases hx : x ∈ V
    · rw [A.partC0Resolvent_of_mem hV mu f hf hfD hx, domainExtension_of_mem hx]
    · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx]
      have hnot : ¬ ∃ y : V, (y : Vec d) = x := by
        rintro ⟨y, rfl⟩
        exact hx y.2
      exact (Function.extend_apply' (fun y : V ↦ h y) (0 : Vec d → ℝ) x hnot).symm
  rw [heq]
  exact measurable_domainExtension hV.isOpen.measurableSet hmeas

/-! ## The datum is seen only on the domain -/

/-- **The Dirichlet resolvent of a part domain sees only the values of its datum on that
domain.** -/
theorem partC0Resolvent_eq_of_eqOn {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : Set.EqOn f g V)
    (x : Vec d) :
    A.partC0Resolvent hV mu f hf hfD x = A.partC0Resolvent hV mu g hg hgE x := by
  by_cases hx : x ∈ V
  · rw [A.partC0Resolvent_of_mem hV mu f hf hfD hx,
      A.partC0Resolvent_of_mem hV mu g hg hgE hx]
    have hdatum : boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
          (fun y ↦ hfD y) =
        boundedMeasurableToScalarL2 hV (hg.comp measurable_subtype_coe) (fun y ↦ hgE y) := by
      refine (Lp.ext_iff).2 ?_
      filter_upwards [boundedMeasurableToScalarL2_coeFn hV
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
        boundedMeasurableToScalarL2_coeFn hV
          (hg.comp measurable_subtype_coe) (fun y ↦ hgE y),
        ae_restrict_mem hV.isOpen.measurableSet] with y hyF hyG hyV
      rw [hyF, hyG, domainExtension_of_mem hyV, domainExtension_of_mem hyV]
      exact hfg hyV
    refine continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq A.a hV A.hnu A.hnu
      (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hg.comp measurable_subtype_coe) (fun y ↦ hgE y)
      (continuousOn_continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu
        (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) ?_ hx
    rw [← hdatum]
    exact continuousCoeffBoundedResolvent_ae A.a hV A.hnu A.hnu (partEllipticity A hV)
      A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx,
      A.partC0Resolvent_of_notMem hV mu g hg hgE hx]

/-! ## The maximum-principle bound -/

/-- **The shift-dependent maximum-principle bound of the Dirichlet resolvent of a part
domain.** -/
theorem abs_partC0Resolvent_le {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |A.partC0Resolvent hV mu f hf hfD x| ≤ D / (mu : ℝ) := by
  by_cases hx : x ∈ V
  · rw [A.partC0Resolvent_of_mem hV mu f hf hfD hx]
    simpa only [abs_of_nonneg hD] using
      abs_continuousCoeffBoundedResolvent_le A.a hV A.hnu A.hnu (partEllipticity A hV)
        A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) x hx
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx, abs_zero]
    exact div_nonneg hD mu.property.le

/-! ## Linearity in the datum -/

/-- **The Dirichlet resolvent of a part domain is additive in its datum.** -/
theorem partC0Resolvent_add {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, |f x + g x| ≤ D + E) (x : Vec d) :
    A.partC0Resolvent hV mu (fun y ↦ f y + g y) (hf.add hg) hfg x =
      A.partC0Resolvent hV mu f hf hfD x + A.partC0Resolvent hV mu g hg hgE x := by
  by_cases hx : x ∈ V
  · rw [A.partC0Resolvent_of_mem hV mu (fun y ↦ f y + g y) (hf.add hg) hfg hx,
      A.partC0Resolvent_of_mem hV mu f hf hfD hx,
      A.partC0Resolvent_of_mem hV mu g hg hgE hx]
    exact (continuousCoeffBoundedResolvent_add A.a hV A.hnu A.hnu (partEllipticity A hV)
      A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hf.comp measurable_subtype_coe) (hg.comp measurable_subtype_coe)
      (fun y ↦ hfD y) (fun y ↦ hgE y) (fun y ↦ hfg y) hx).symm
  · rw [A.partC0Resolvent_of_notMem hV mu (fun y ↦ f y + g y) (hf.add hg) hfg hx,
      A.partC0Resolvent_of_notMem hV mu f hf hfD hx,
      A.partC0Resolvent_of_notMem hV mu g hg hgE hx, add_zero]

/-- **The Dirichlet resolvent of a part domain is homogeneous in its datum.** -/
theorem partC0Resolvent_smul {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (c : ℝ) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hcf : ∀ x, |c * f x| ≤ |c| * D) (x : Vec d) :
    A.partC0Resolvent hV mu (fun y ↦ c * f y) (hf.const_smul c) hcf x =
      c * A.partC0Resolvent hV mu f hf hfD x := by
  by_cases hx : x ∈ V
  · rw [A.partC0Resolvent_of_mem hV mu (fun y ↦ c * f y) (hf.const_smul c) hcf hx,
      A.partC0Resolvent_of_mem hV mu f hf hfD hx]
    exact (continuousCoeffBoundedResolvent_smul A.a hV A.hnu A.hnu (partEllipticity A hV)
      A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu c
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) (fun y ↦ hcf y) hx).symm
  · rw [A.partC0Resolvent_of_notMem hV mu (fun y ↦ c * f y) (hf.const_smul c) hcf hx,
      A.partC0Resolvent_of_notMem hV mu f hf hfD hx, mul_zero]

/-- **The Dirichlet resolvent of a part domain is affine in its datum.** -/
theorem partC0Resolvent_add_const_mul {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (c : ℝ) {f h : Vec d → ℝ} (hf : Measurable f) (hh : Measurable h)
    {D E S : ℝ} (hfD : ∀ y, |f y| ≤ D) (hhE : ∀ y, |h y| ≤ E)
    (hs : Measurable fun y ↦ f y + c * h y) (hsS : ∀ y, |f y + c * h y| ≤ S) (x : Vec d) :
    A.partC0Resolvent hV mu (fun y ↦ f y + c * h y) hs hsS x =
      A.partC0Resolvent hV mu f hf hfD x + c * A.partC0Resolvent hV mu h hh hhE x := by
  have hcb : ∀ y, |c * h y| ≤ |c| * E := fun y ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hhE y) (abs_nonneg c)
  have hsum : ∀ y, |f y + c * h y| ≤ D + |c| * E := fun y ↦
    (abs_add_le _ _).trans (add_le_add (hfD y) (hcb y))
  calc A.partC0Resolvent hV mu (fun y ↦ f y + c * h y) hs hsS x
      = A.partC0Resolvent hV mu (fun y ↦ f y + c * h y) hs hsum x :=
        A.partC0Resolvent_eq_of_eqOn hV mu hs hs hsS hsum (Set.eqOn_refl _ _) x
    _ = A.partC0Resolvent hV mu f hf hfD x +
          A.partC0Resolvent hV mu (fun y ↦ c * h y) (hh.const_smul c) hcb x :=
        A.partC0Resolvent_add hV mu hf (hh.const_smul c) hfD hcb hsum x
    _ = A.partC0Resolvent hV mu f hf hfD x + c * A.partC0Resolvent hV mu h hh hhE x := by
        rw [A.partC0Resolvent_smul hV mu c hh hhE hcb x]

/-! ## Monotonicity in the datum -/

/-- **The Dirichlet resolvent of a part domain preserves pointwise order between bounded
measurable data.** -/
theorem partC0Resolvent_mono {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : ∀ x, f x ≤ g x)
    (x : Vec d) :
    A.partC0Resolvent hV mu f hf hfD x ≤ A.partC0Resolvent hV mu g hg hgE x := by
  by_cases hx : x ∈ V
  · have hFG : ∀ᵐ y ∂volumeMeasureOn V,
        boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe) (fun z ↦ hfD z) y ≤
          boundedMeasurableToScalarL2 hV (hg.comp measurable_subtype_coe) (fun z ↦ hgE z) y := by
      filter_upwards [boundedMeasurableToScalarL2_coeFn hV
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
        boundedMeasurableToScalarL2_coeFn hV
          (hg.comp measurable_subtype_coe) (fun y ↦ hgE y),
        ae_restrict_mem hV.isOpen.measurableSet] with y hF hG hy
      rw [hF, hG, domainExtension_of_mem hy, domainExtension_of_mem hy]
      exact hfg y
    refine le_of_ae_le_of_continuousOn hV.isOpen
      (A.continuousOn_partC0Resolvent hV mu f hf hfD)
      (A.continuousOn_partC0Resolvent hV mu g hg hgE) ?_ x hx
    filter_upwards [A.partC0Resolvent_ae hV mu f hf hfD, A.partC0Resolvent_ae hV mu g hg hgE,
      alphaShiftedResolvent_mono_ae A.a hV mu.property A.hnu (partEllipticity A hV)
        (boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe) (fun z ↦ hfD z))
        (boundedMeasurableToScalarL2 hV (hg.comp measurable_subtype_coe) (fun z ↦ hgE z))
        hFG] with y h1 h2 h3
    rw [h1, h2]
    exact h3
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx,
      A.partC0Resolvent_of_notMem hV mu g hg hgE hx]

/-! ## The resolvent identity in the shift -/

private theorem partAlphaShiftedResolvent_identity {V : Set (Vec d)} {Lam : ℝ}
    (mu nu : PositiveShift) (hEll : IsEllipticFieldOn A.nu Lam V A.a) (F : ScalarL2 V) :
    alphaShiftedResolvent A.a mu.property A.hnu hEll F =
      alphaShiftedResolvent A.a nu.property A.hnu hEll F +
        ((nu : ℝ) - (mu : ℝ)) • alphaShiftedResolvent A.a nu.property A.hnu hEll
          (alphaShiftedResolvent A.a mu.property A.hnu hEll F) := by
  have hid := alphaShiftedResolvent_resolvent_identity A.a nu.property mu.property A.hnu hEll
  have happ := congrArg (fun T : ScalarL2 V →L[ℝ] ScalarL2 V ↦ T F) hid
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply] at happ
  have hstep : alphaShiftedResolvent A.a nu.property A.hnu hEll F -
        alphaShiftedResolvent A.a mu.property A.hnu hEll F =
      ((mu : ℝ) - (nu : ℝ)) • alphaShiftedResolvent A.a nu.property A.hnu hEll
        (alphaShiftedResolvent A.a mu.property A.hnu hEll F) := happ
  have hsmul : ((mu : ℝ) - (nu : ℝ)) • alphaShiftedResolvent A.a nu.property A.hnu hEll
        (alphaShiftedResolvent A.a mu.property A.hnu hEll F) =
      -(((nu : ℝ) - (mu : ℝ)) • alphaShiftedResolvent A.a nu.property A.hnu hEll
        (alphaShiftedResolvent A.a mu.property A.hnu hEll F)) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hsmul] at hstep
  linear_combination (norm := module) -hstep

/-- **The resolvent identity for the Dirichlet resolvent of a part domain.**  The value at one
shift is the value at another plus the difference of the shifts times the second resolvent of
the first. -/
theorem partC0Resolvent_resolvent_identity {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (mu nu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.partC0Resolvent hV mu f hf hfD x =
      A.partC0Resolvent hV nu f hf hfD x +
        ((nu : ℝ) - (mu : ℝ)) *
          A.partC0Resolvent hV nu (A.partC0Resolvent hV mu f hf hfD)
            (A.measurable_partC0Resolvent hV mu f hf hfD) (D := D / (mu : ℝ))
            (A.abs_partC0Resolvent_le hV mu hf hD hfD) x := by
  set g : Vec d → ℝ := A.partC0Resolvent hV mu f hf hfD with hgdef
  have hg : Measurable g := A.measurable_partC0Resolvent hV mu f hf hfD
  have hgD : ∀ y, |g y| ≤ D / (mu : ℝ) := A.abs_partC0Resolvent_le hV mu hf hD hfD
  set F : ScalarL2 V :=
    boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) with hFdef
  by_cases hx : x ∈ V
  · have hfae : A.partC0Resolvent hV mu f hf hfD =ᵐ[volumeMeasureOn V]
        ⇑(alphaShiftedResolvent A.a mu.property A.hnu (partEllipticity A hV) F) :=
      A.partC0Resolvent_ae hV mu f hf hfD
    have hnufae : A.partC0Resolvent hV nu f hf hfD =ᵐ[volumeMeasureOn V]
        ⇑(alphaShiftedResolvent A.a nu.property A.hnu (partEllipticity A hV) F) :=
      A.partC0Resolvent_ae hV nu f hf hfD
    have hclass : boundedMeasurableToScalarL2 hV (hg.comp measurable_subtype_coe)
          (fun y ↦ hgD y) =
        alphaShiftedResolvent A.a mu.property A.hnu (partEllipticity A hV) F := by
      refine (Lp.ext_iff).2 ?_
      filter_upwards [boundedMeasurableToScalarL2_coeFn hV
          (hg.comp measurable_subtype_coe) (fun y ↦ hgD y), hfae,
        ae_restrict_mem hV.isOpen.measurableSet] with y hdatum hrep hy
      rw [hdatum, domainExtension_of_mem hy]
      exact hrep
    have hgae : A.partC0Resolvent hV nu g hg hgD =ᵐ[volumeMeasureOn V]
        ⇑(alphaShiftedResolvent A.a nu.property A.hnu (partEllipticity A hV)
          (boundedMeasurableToScalarL2 hV (hg.comp measurable_subtype_coe)
            (fun y ↦ hgD y))) :=
      A.partC0Resolvent_ae hV nu g hg hgD
    rw [hclass] at hgae
    have hL2 := A.partAlphaShiftedResolvent_identity mu nu (partEllipticity A hV) F
    have heq := continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq A.a hV A.hnu
      A.hnu (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd
      mu (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
      (v := fun y ↦ A.partC0Resolvent hV nu f hf hfD y +
        ((nu : ℝ) - (mu : ℝ)) * A.partC0Resolvent hV nu g hg hgD y)
      ((A.continuousOn_partC0Resolvent hV nu f hf hfD).add
        (continuousOn_const.mul (A.continuousOn_partC0Resolvent hV nu g hg hgD))) ?_
    · rw [A.partC0Resolvent_of_mem hV mu f hf hfD hx]
      exact (heq hx).symm
    · rw [← hFdef, hL2]
      filter_upwards [hnufae, hgae,
        Lp.coeFn_add (alphaShiftedResolvent A.a nu.property A.hnu (partEllipticity A hV) F)
          (((nu : ℝ) - (mu : ℝ)) • alphaShiftedResolvent A.a nu.property A.hnu
            (partEllipticity A hV) (alphaShiftedResolvent A.a mu.property A.hnu
              (partEllipticity A hV) F)),
        Lp.coeFn_smul ((nu : ℝ) - (mu : ℝ))
          (alphaShiftedResolvent A.a nu.property A.hnu (partEllipticity A hV)
            (alphaShiftedResolvent A.a mu.property A.hnu (partEllipticity A hV) F))]
        with y hnuy houter hadd hsmul
      rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, ← hnuy, ← houter]
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx,
      A.partC0Resolvent_of_notMem hV nu f hf hfD hx,
      A.partC0Resolvent_of_notMem hV nu g hg hgD hx, mul_zero, add_zero]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
