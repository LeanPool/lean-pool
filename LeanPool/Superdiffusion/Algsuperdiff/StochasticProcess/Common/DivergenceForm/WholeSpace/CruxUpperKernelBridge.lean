/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperIdentities
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveMinimalMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventTail
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointExtension
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingPotential

/-!
# CruxUpperKernelBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# From the kernel resolvent to the analytic minimal resolvent

The comparison family of the process layer is compared with the real kernel
resolvent of the compactified semigroup.  This module records the three
translations needed for that comparison: the real kernel resolvent of a
nonnegative bounded observable is the real value of its extended-real kernel
resolvent; at the added point the kernel resolvent reads only the value of the
observable there; and at a live point, for a conservative live semigroup, it
is the real analytic minimal resolvent of the restricted observable.

The last translation is the named identification hypothesis of the analytic
layer, normalized to observables bounded by one, so it is used through a
rescaling.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup ProbabilityTheory
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section Generic

variable {alpha : Type*} [MeasurableSpace alpha]

private theorem abs_kernelIntegral_le (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  rw [← Real.norm_eq_abs]
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  calc
    ‖kernelIntegral (P t) f x‖ ≤ ∫ _y, D ∂(P t x) := by
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall hfD
    _ ≤ D := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hD0
      rw [measureReal_def, ← ENNReal.toReal_one]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      exact (P.isSubMarkovKernel t).measure_le_one x Set.univ

private theorem integrableOn_resolventIntegrand
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).measurable.mul
      ((P.measurable_kernelIntegral hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (abs_kernelIntegral_le P hfD (Real.toNNReal t) x) (Real.exp_pos _).le

/-- The real kernel resolvent of a nonnegative observable is nonnegative. -/
theorem kernelResolventReal_nonneg (P : SubMarkovKernelSemigroup alpha)
    (lam : ℝ) {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ P.kernelResolventReal lam f x := by
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  refine integral_nonneg fun t ↦ ?_
  exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ ↦ hf0 _)

/-- On nonnegative bounded measurable observables the real kernel resolvent is
the real value of the extended-real kernel resolvent. -/
theorem ofReal_kernelResolventReal_eq_kernelResolvent
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    ENNReal.ofReal (P.kernelResolventReal lam f x) =
      P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (f y)) x := by
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_resolventIntegrand P hlam hf hfD x)
    (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le
      (integral_nonneg fun _ ↦ hf0 _))]
  unfold SubMarkovKernelSemigroup.kernelResolvent
  refine lintegral_congr fun t ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  let : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hint : Integrable f (P (Real.toNNReal t) x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
      (Eventually.of_forall hfD)
  unfold kernelIntegral
  exact ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)

/-- The real kernel resolvent of a nonnegative bounded measurable observable
is the real value of the extended-real one. -/
theorem kernelResolventReal_eq_toReal_kernelResolvent
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    P.kernelResolventReal lam f x =
      (P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (f y)) x).toReal := by
  rw [← ofReal_kernelResolventReal_eq_kernelResolvent P hlam hf hf0 hfD x,
    ENNReal.toReal_ofReal (kernelResolventReal_nonneg P lam hf0 x)]

end Generic

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- At the added point the real kernel resolvent of the one-point extension
reads only the value of the observable there. -/
theorem onePointKernelResolventReal_infty
    (R : PositiveC0ContractiveResolvent (Vec d)) (lam : ℝ)
    {G : OnePoint (Vec d) → ℝ} (hG : Measurable G) :
    R.onePointKernelSemigroup.kernelResolventReal lam G OnePoint.infty =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * G OnePoint.infty := by
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ht ↦ ?_
  congr 1
  unfold kernelIntegral
  rw [R.onePointKernelSemigroup_absorbing]
  exact integral_dirac' G OnePoint.infty hG.stronglyMeasurable

omit [NeZero d] in
/-- An observable vanishing at the added point has vanishing real kernel
resolvent there. -/
theorem onePointKernelResolventReal_infty_eq_zero
    (R : PositiveC0ContractiveResolvent (Vec d)) (lam : ℝ)
    {G : OnePoint (Vec d) → ℝ} (hG : Measurable G)
    (hGzero : G OnePoint.infty = 0) :
    R.onePointKernelSemigroup.kernelResolventReal lam G OnePoint.infty = 0 := by
  rw [onePointKernelResolventReal_infty R lam hG, hGzero]
  simp

omit [NeZero d] in
/-- At a live point the real kernel resolvent of the one-point extension of a
conservative semigroup is the real kernel resolvent of the restricted
observable. -/
theorem onePointKernelResolventReal_coe
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative) (lam : ℝ)
    {G : OnePoint (Vec d) → ℝ} (hG : Measurable G) (x : Vec d) :
    R.onePointKernelSemigroup.kernelResolventReal lam G (x : OnePoint (Vec d)) =
      R.kernelSemigroup.kernelResolventReal lam
        (fun y ↦ G (y : OnePoint (Vec d))) x := by
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ht ↦ ?_
  congr 1
  unfold kernelIntegral
  rw [R.onePointKernelSemigroup_apply_coe, hcons, tsub_self, zero_smul, add_zero,
    integral_map OnePoint.continuous_coe.measurable.aemeasurable
      hG.aestronglyMeasurable]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The kernel resolvent of a nonnegative bounded observable is the analytic
minimal resolvent.  The named identification hypothesis is normalized to
observables bounded by one, so the datum is rescaled by a positive bound. -/
theorem kernelResolvent_eq_analyticMinimalResolvent
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    R.kernelSemigroup.kernelResolvent (mu : ℝ)
        (fun y ↦ ENNReal.ofReal (f y)) x =
      A.analyticMinimalResolvent mu f hf hfD x := by
  have hD : 0 ≤ D := (abs_nonneg (f 0)).trans (hfD 0)
  set C : ℝ := max D 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set g : Vec d → ℝ := fun y ↦ C⁻¹ * f y with hgdef
  have hg : Measurable g := hf.const_smul C⁻¹
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ mul_nonneg (inv_nonneg.mpr hC.le) (hf0 y)
  have hg1 : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [hgdef, abs_mul, abs_of_nonneg (inv_nonneg.mpr hC.le)]
    calc
      C⁻¹ * |f y| ≤ C⁻¹ * D :=
        mul_le_mul_of_nonneg_left (hfD y) (inv_nonneg.mpr hC.le)
      _ ≤ C⁻¹ * C :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hkernel : R.kernelSemigroup.kernelResolvent (mu : ℝ)
      (fun y ↦ ENNReal.ofReal (g y)) x =
        A.analyticMinimalResolvent mu g hg hg1 x := hid mu hg hg0 hg1 x
  have hfscale : (fun y ↦ ENNReal.ofReal C * ENNReal.ofReal (g y)) =
      fun y ↦ ENNReal.ofReal (f y) := by
    funext y
    rw [← ENNReal.ofReal_mul hC.le, hgdef]
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  have hkernel' : R.kernelSemigroup.kernelResolvent (mu : ℝ)
      (ENNReal.ofReal ∘ g) x = A.analyticMinimalResolvent mu g hg hg1 x := hkernel
  rw [← hfscale]
  have hhom := R.kernelSemigroup.kernelResolvent_const_mul (mu : ℝ)
    (ENNReal.ofReal C) (ENNReal.measurable_ofReal.comp hg) x
  change R.kernelSemigroup.kernelResolvent (mu : ℝ)
      (fun y ↦ ENNReal.ofReal C * (ENNReal.ofReal ∘ g) y) x = _
  rw [hhom, hkernel']
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (A.analyticMinimalResolvent_ne_top mu hg hg0 (by norm_num) hg1 x))
    (A.analyticMinimalResolvent_ne_top mu hf hf0 hD hfD x)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
  have hscaled := A.toReal_analyticMinimalResolvent_smul mu hC.le hg hg0
    (by norm_num) hg1 x
  rw [← hscaled]
  apply congrArg ENNReal.toReal
  apply A.analyticMinimalResolvent_congr_ae mu (hg.const_smul C) hf
    (fun y ↦ by
      change |C * g y| ≤ C * 1
      rw [abs_mul, abs_of_nonneg hC.le]
      exact mul_le_mul_of_nonneg_left (hg1 y) hC.le)
    hfD
  refine Filter.Eventually.of_forall fun y ↦ ?_
  change C * (C⁻¹ * f y) = f y
  rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]

/-- **The real kernel resolvent is the signed real analytic minimal
resolvent** on signed bounded measurable observables. -/
theorem kernelResolventReal_eq_analyticMinimalResolventReal
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) :
    R.kernelSemigroup.kernelResolventReal (mu : ℝ) f x =
      A.analyticMinimalResolventReal mu f hf hfD x := by
  have hfp : Measurable (analyticPositivePart f) :=
    measurable_analyticPositivePart hf
  have hfn : Measurable (analyticPositivePart fun y ↦ -f y) :=
    measurable_analyticPositivePart hf.neg
  have hfp0 : ∀ y, 0 ≤ analyticPositivePart f y := fun y ↦ le_max_right (f y) 0
  have hfn0 : ∀ y, 0 ≤ analyticPositivePart (fun y ↦ -f y) y := fun y ↦
    le_max_right (-f y) 0
  have hfpD : ∀ y, |analyticPositivePart f y| ≤ D :=
    abs_analyticPositivePart_le_of_bound hfD
  have hfnD : ∀ y, |analyticPositivePart (fun y ↦ -f y) y| ≤ D :=
    abs_analyticPositivePart_le_of_bound
      (fun y ↦ by simpa only [abs_neg] using hfD y)
  have hsplit : f = analyticPositivePart f +
      (-1 : ℝ) • analyticPositivePart fun y ↦ -f y := by
    funext y
    have := congrFun (analyticPositivePart_sub_neg f) y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul]
    linarith only [this]
  have hnegD : ∀ y, |((-1 : ℝ) • analyticPositivePart fun z ↦ -f z) y| ≤ D := by
    intro y
    simpa only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, abs_neg] using hfnD y
  have hleft : R.kernelSemigroup.kernelResolventReal (mu : ℝ) f x =
      R.kernelSemigroup.kernelResolventReal (mu : ℝ) (analyticPositivePart f) x -
        R.kernelSemigroup.kernelResolventReal (mu : ℝ)
          (analyticPositivePart fun y ↦ -f y) x := by
    conv_lhs => rw [hsplit]
    rw [R.kernelSemigroup.kernelResolventReal_add mu.property hfp
      (hfn.const_smul (-1)) hfpD hnegD,
      R.kernelSemigroup.kernelResolventReal_smul (mu : ℝ) (-1)
        (analyticPositivePart fun y ↦ -f y)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul]
    ring
  rw [hleft,
    kernelResolventReal_eq_toReal_kernelResolvent R.kernelSemigroup
      mu.property hfp hfp0 hfpD x,
    kernelResolventReal_eq_toReal_kernelResolvent R.kernelSemigroup
      mu.property hfn hfn0 hfnD x,
    A.kernelResolvent_eq_analyticMinimalResolvent R hid mu hfp hfp0 hfpD x,
    A.kernelResolvent_eq_analyticMinimalResolvent R hid mu hfn hfn0 hfnD x]
  rfl

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
