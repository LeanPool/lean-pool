/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventIdentity

/-!
# RealResolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Signed real algebra for the analytic minimal resolvent

The signed real minimal resolvent is the limit of the signed zero-extended
cube resolvents. Cube linearity yields additivity and homogeneity of the
limit, together with the sharp maximum-principle bound.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
private theorem analyticPositivePart_sub (f : Vec d → ℝ) :
    (fun x ↦ analyticPositivePart f x - analyticPositivePart (fun y ↦ -f y) x) = f := by
  funext x
  exact max_zero_sub_max_neg_zero_eq_self (f x)

omit [NeZero d] in
private theorem abs_analyticPositivePart_le' {f : Vec d → ℝ} {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |analyticPositivePart f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hpart : 0 ≤ analyticPositivePart f x := le_max_right _ _
  rw [abs_of_nonneg hpart, analyticPositivePart]
  exact max_le ((le_abs_self (f x)).trans (hfD x)) hD

/-- Scalar multiplication commutes with one local analytic cube resolvent. -/
theorem analyticCubeResolvent_smul (mu : PositiveShift) (c : ℝ)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D)
    (hcf : ∀ x, |c * f x| ≤ |c| * D) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu (fun y => c * f y) (hf.const_smul c) hcf m x =
      c * A.analyticCubeResolvent mu f hf hfD m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx]
    exact (continuousCoeffBoundedResolvent_smul A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu c
      (hf.comp measurable_subtype_coe) (fun y => hfD y) (fun y => hcf y) hx).symm
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx,
      mul_zero]

/-- A local cube resolvent depends only on the datum restricted to that
cube. -/
theorem analyticCubeResolvent_eq_of_eqOn (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (m : ℕ) (hfg : Set.EqOn f g (wholeSpaceCube d m)) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
      A.analyticCubeResolvent mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx]
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    have hdatum : boundedMeasurableToScalarL2 hU
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) =
        boundedMeasurableToScalarL2 hU
          (hg.comp measurable_subtype_coe) (fun y ↦ hgE y) := by
      refine (Lp.ext_iff).2 ?_
      filter_upwards [boundedMeasurableToScalarL2_coeFn hU
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
        boundedMeasurableToScalarL2_coeFn hU
          (hg.comp measurable_subtype_coe) (fun y ↦ hgE y),
        ae_restrict_mem hU.isOpen.measurableSet] with y hyF hyG hyU
      rw [hyF, hyG, domainExtension_of_mem hyU, domainExtension_of_mem hyU]
      exact hfg hyU
    exact continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq A.a hU A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
      (hg.comp measurable_subtype_coe) (fun y ↦ hgE y)
      (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu A.hnu
        (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) (by
          rw [← hdatum]
          exact continuousCoeffBoundedResolvent_ae A.a hU A.hnu A.hnu
            (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
            (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) hx
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx]

private theorem analyticCubeResolvent_bound_irrel (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hfE : ∀ x, |f x| ≤ E) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
    A.analyticCubeResolvent mu f hf hfE m x :=
  A.analyticCubeResolvent_eq_of_eqOn mu hf hf hfD hfE m
    (fun _ _ ↦ rfl) x

private theorem analyticCubeResolvent_congr (mu : PositiveShift)
    {f g : Vec d → ℝ} (hfg : f = g) (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
      A.analyticCubeResolvent mu g hg hgE m x := by
  subst g
  exact A.analyticCubeResolvent_bound_irrel mu hf hfD hgE m x

private theorem analyticCubeResolvent_eq_parts (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
      A.analyticCubeResolvent mu (analyticPositivePart f)
          (measurable_analyticPositivePart hf)
          (abs_analyticPositivePart_le' hfD) m x -
        A.analyticCubeResolvent mu (analyticPositivePart fun y ↦ -f y)
          (measurable_analyticPositivePart hf.neg)
          (abs_analyticPositivePart_le'
            (fun y ↦ by simpa only [abs_neg] using hfD y)) m x := by
  let fp := analyticPositivePart f
  let fn := analyticPositivePart fun y ↦ -f y
  have hfp : Measurable fp := measurable_analyticPositivePart hf
  have hfn : Measurable fn := measurable_analyticPositivePart hf.neg
  have hfpD : ∀ y, |fp y| ≤ D := abs_analyticPositivePart_le' hfD
  have hfnD : ∀ y, |fn y| ≤ D :=
    abs_analyticPositivePart_le' (fun y ↦ by simpa only [abs_neg] using hfD y)
  have hneg : ∀ y, |((-1 : ℝ) • fn) y| ≤ |-1| * D := by
    intro y
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfnD y) (abs_nonneg (-1 : ℝ))
  have hneg' : ∀ y, |-1 * fn y| ≤ |-1| * D := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfnD y) (abs_nonneg (-1 : ℝ))
  have hsum : ∀ y, |fp y + ((-1 : ℝ) • fn) y| ≤ D + |(-1 : ℝ)| * D := by
    intro y
    rw [show fp y + ((-1 : ℝ) • fn) y = f y by
      simpa only [fp, fn, Pi.smul_apply, smul_eq_mul, analyticPositivePart, neg_mul, one_mul,
        sub_eq_add_neg]
        using congrFun (analyticPositivePart_sub f) y]
    calc
      |f y| ≤ D := hfD y
      _ ≤ D + |-1| * D := le_add_of_nonneg_right
        (mul_nonneg (abs_nonneg (-1 : ℝ))
          ((abs_nonneg (f y)).trans (hfD y)))
  have hadd := A.analyticCubeResolvent_add mu hfp (hfn.const_smul (-1))
    hfpD hneg hsum m x
  have hsmul := A.analyticCubeResolvent_smul mu (-1) hfn hfnD hneg m x
  have hinput : (fun y ↦ fp y + ((-1 : ℝ) • fn) y) = f := by
    simpa only [fp, fn, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, sub_eq_add_neg] using
      analyticPositivePart_sub f
  calc
    A.analyticCubeResolvent mu f hf hfD m x =
        A.analyticCubeResolvent mu (fun y ↦ fp y + ((-1 : ℝ) • fn) y)
          (hfp.add (hfn.const_smul (-1))) hsum m x := by
            exact A.analyticCubeResolvent_congr mu hinput.symm hf
              (hfp.add (hfn.const_smul (-1))) hfD hsum m x
    _ = A.analyticCubeResolvent mu fp hfp hfpD m x +
        A.analyticCubeResolvent mu ((-1 : ℝ) • fn)
          (hfn.const_smul (-1)) hneg m x := hadd
    _ = A.analyticCubeResolvent mu fp hfp hfpD m x -
        A.analyticCubeResolvent mu fn hfn hfnD m x := by
          have hfun : ((-1 : ℝ) • fn) = (fun y ↦ -1 * fn y) := by
            funext y
            simp only [Pi.smul_apply, smul_eq_mul]
          have htransport := A.analyticCubeResolvent_congr mu hfun
            (hfn.const_smul (-1)) (measurable_const.mul hfn) hneg hneg' m x
          have hs : A.analyticCubeResolvent mu ((-1 : ℝ) • fn)
              (hfn.const_smul (-1)) hneg m x =
                -A.analyticCubeResolvent mu fn hfn hfnD m x := by
            calc
              _ = A.analyticCubeResolvent mu (fun y ↦ -1 * fn y)
                  (measurable_const.mul hfn) hneg' m x := htransport
              _ = _ := by simpa only [neg_mul, one_mul] using hsmul
          rw [hs]
          ring

/-- The signed zero-extended cube resolvents converge to the real minimal
resolvent. -/
theorem tendsto_analyticCubeResolvent_real (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Tendsto (fun m ↦ A.analyticCubeResolvent mu f hf hfD m x) atTop
      (nhds (A.analyticMinimalResolventReal mu f hf hfD x)) := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hp := A.tendsto_analyticCubeResolvent mu
    (measurable_analyticPositivePart hf) (fun y ↦ le_max_right (f y) 0) hD
    (abs_analyticPositivePart_le' hfD) x
  have hn := A.tendsto_analyticCubeResolvent mu
    (measurable_analyticPositivePart hf.neg) (fun y ↦ le_max_right (-f y) 0) hD
    (abs_analyticPositivePart_le' (fun y ↦ by
      have h : abs (-f y) ≤ D := by simpa only [abs_neg] using hfD y
      exact h)) x
  apply (hp.sub hn).congr'
  filter_upwards with m
  exact A.analyticCubeResolvent_eq_parts mu hf hfD m x |>.symm

/-- The real analytic minimal resolvent is additive. -/
theorem analyticMinimalResolventReal_add (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (x : Vec d) :
    A.analyticMinimalResolventReal mu (fun y ↦ f y + g y) (hf.add hg)
        (D := D + E) (fun y ↦ (abs_add_le (f y) (g y)).trans
          (add_le_add (hfD y) (hgE y))) x =
      A.analyticMinimalResolventReal mu f hf hfD x +
        A.analyticMinimalResolventReal mu g hg hgE x := by
  let hfg : ∀ y, |f y + g y| ≤ D + E := fun y ↦
    (abs_add_le (f y) (g y)).trans (add_le_add (hfD y) (hgE y))
  have hleft := A.tendsto_analyticCubeResolvent_real mu (hf.add hg) hfg x
  have hright := (A.tendsto_analyticCubeResolvent_real mu hf hfD x).add
    (A.tendsto_analyticCubeResolvent_real mu hg hgE x)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with m
  exact A.analyticCubeResolvent_add mu hf hg hfD hgE hfg m x |>.symm

/-- Scalar multiplication commutes with the real analytic minimal resolvent. -/
theorem analyticMinimalResolventReal_smul (mu : PositiveShift) (c : ℝ)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticMinimalResolventReal mu (fun y ↦ c * f y) (hf.const_smul c)
        (D := |c| * D) (fun y ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hfD y) (abs_nonneg c)) x =
      c * A.analyticMinimalResolventReal mu f hf hfD x := by
  let hcf : ∀ y, |c * f y| ≤ |c| * D := fun y ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfD y) (abs_nonneg c)
  have hleft := A.tendsto_analyticCubeResolvent_real mu (hf.const_smul c) hcf x
  have hright := (A.tendsto_analyticCubeResolvent_real mu hf hfD x).const_mul c
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with m
  exact A.analyticCubeResolvent_smul mu c hf hfD hcf m x |>.symm

/-- The signed real analytic minimal resolvent has the sharp maximum-principle
bound inherited from every cube. -/
theorem abs_analyticMinimalResolventReal_le (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |A.analyticMinimalResolventReal mu f hf hfD x| ≤ D / (mu : ℝ) := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  refine le_of_tendsto
    ((A.tendsto_analyticCubeResolvent_real mu hf hfD x).abs)
    (Eventually.of_forall fun m ↦ A.abs_analyticCubeResolvent_le mu hf hD hfD m x)

/-- The value of the real minimal resolvent is independent of the numerical
bound used to certify boundedness of its datum. -/
theorem analyticMinimalResolventReal_bound_irrel (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hfE : ∀ x, |f x| ≤ E) (x : Vec d) :
    A.analyticMinimalResolventReal mu f hf hfD x =
      A.analyticMinimalResolventReal mu f hf hfE x :=
  tendsto_nhds_unique (A.tendsto_analyticCubeResolvent_real mu hf hfD x)
    (A.tendsto_analyticCubeResolvent_real mu hf hfE x)

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
