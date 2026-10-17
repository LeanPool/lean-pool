/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartGreenLimit

/-!
# PartGreenH10

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Green potential of a bounded part domain is a zero-trace weak solution

The vanishing-shift limit `partGreenPotential` of the Dirichlet resolvents of a bounded
measurable datum on a bounded open convex domain is identified here: it is the value function of
an honest zero-trace Sobolev function on the domain solving
  `-div (a grad w) = f`   weakly, with zero trace.

The representative is exact: `partGreenH10` is an `H10Function` whose value function *is*
`partGreenPotential`, not merely a function almost everywhere equal to it.  Pointwise arguments
downstream read the values of the Green potential, so the exact representative matters.

This is the statement of `ExitMeanValueIdentificationGreen.lean` with the exhaustion cube
replaced by an arbitrary bounded open convex domain.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open ZeroTraceSobolev
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The `L²` class of the Green potential -/

/-- The `L²` class of the Green potential of a bounded part domain. -/
def partGreenPotentialL2 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) : ScalarL2 V :=
  boundedMeasurableToScalarL2 hV
    ((A.measurable_partGreenPotential hV hf hD hfD).comp measurable_subtype_coe)
    (fun y ↦ A.abs_partGreenPotential_le hV hf hD hfD y)

theorem partGreenPotentialL2_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ⇑(A.partGreenPotentialL2 hV hf hD hfD) =ᵐ[volumeMeasureOn V]
      A.partGreenPotential hV f hf hD hfD := by
  have hcoe : ⇑(A.partGreenPotentialL2 hV hf hD hfD) =ᵐ[volumeMeasureOn V]
      domainExtension (A.partGreenPotential hV f hf hD hfD ∘ Subtype.val) :=
    boundedMeasurableToScalarL2_coeFn hV
      ((A.measurable_partGreenPotential hV hf hD hfD).comp measurable_subtype_coe)
      (fun y ↦ A.abs_partGreenPotential_le hV hf hD hfD y)
  filter_upwards [hcoe, ae_restrict_mem hV.isOpen.measurableSet] with x hx hxmem
  rw [hx, domainExtension_of_mem hxmem]
  rfl

/-- The `L²` rate of the vanishing-shift limit, from the pointwise rate. -/
theorem norm_toL2_partShiftSolution_sub_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) {lam : ℝ} (hlam : 0 < lam) :
    ‖toL2 (A.partShiftSolution hV hf hfD lam) - A.partGreenPotentialL2 hV hf hD hfD‖ ≤
      scalarL2Factor V * (A.partGreenRate hV D * lam) := by
  refine norm_scalarL2_le_of_ae_bound hV _
    (mul_nonneg (A.partGreenRate_nonneg hV hD) hlam.le) ?_
  filter_upwards [Lp.coeFn_sub (toL2 (A.partShiftSolution hV hf hfD lam))
      (A.partGreenPotentialL2 hV hf hD hfD),
    A.toL2_partShiftSolution_ae hV hf hfD lam,
    A.partGreenPotentialL2_ae hV hf hD hfD] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  exact A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x hlam

/-- **The value component of the Green solution is the `L²` class of the Green potential.** -/
theorem toL2_partGreenSolution {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    toL2 (A.partGreenSolution hV hf hD hfD) = A.partGreenPotentialL2 hV hf hD hfD := by
  have h1 : Tendsto (fun n : ℕ ↦ toL2 (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) atTop
      (𝓝 (toL2 (A.partGreenSolution hV hf hD hfD))) :=
    (ZeroTraceSobolev.toL2.continuous.tendsto _).comp
      (A.tendsto_partShiftSolution_partGreenSolution hV hf hD hfD)
  have hzero : Tendsto (fun n : ℕ ↦ scalarL2Factor V *
      (A.partGreenRate hV D * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hstep : Tendsto (fun n : ℕ ↦ scalarL2Factor V *
        (A.partGreenRate hV D * ((n : ℝ) + 1)⁻¹)) atTop
        (𝓝 (scalarL2Factor V * (A.partGreenRate hV D * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hb)
    rwa [mul_zero, mul_zero] at hstep
  have h2 : Tendsto (fun n : ℕ ↦ toL2 (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) atTop
      (𝓝 (A.partGreenPotentialL2 hV hf hD hfD)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hzero
    rw [dist_eq_norm]
    exact A.norm_toL2_partShiftSolution_sub_le hV hf hD hfD (by positivity)
  exact tendsto_nhds_unique h1 h2

theorem toL2_partGreenSolution_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ⇑(toL2 (A.partGreenSolution hV hf hD hfD)) =ᵐ[volumeMeasureOn V]
      A.partGreenPotential hV f hf hD hfD := by
  rw [A.toL2_partGreenSolution hV hf hD hfD]
  exact A.partGreenPotentialL2_ae hV hf hD hfD

/-! ## The exact zero-trace representative -/

/-- **The Green potential is the value function of a zero-trace Sobolev function** whose class in
the carrier is the Green solution. -/
theorem exists_partGreenH10 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ∃ w : H10Function V,
      w.toH1Function.toFun = A.partGreenPotential hV f hf hD hfD ∧
        ZeroTraceSobolev.ofH10Function w = A.partGreenSolution hV hf hD hfD := by
  obtain ⟨u, hval, hgrad⟩ :=
    ZeroTraceSobolev.exists_h10Function hV (A.partGreenSolution hV hf hD hfD)
  have hgae : A.partGreenPotential hV f hf hD hfD =ᵐ[volumeMeasureOn V]
      u.toH1Function.toFun := by
    have h2 := A.toL2_partGreenSolution_ae hV hf hD hfD
    rw [← hval] at h2
    filter_upwards [u.toH1Function.coeFn_toScalarL2, h2] with x hx1 hx2
    rw [← hx2, hx1]
  have hmem : MemL2On V (A.partGreenPotential hV f hf hD hfD) :=
    (MeasureTheory.memLp_congr_ae hgae).mpr u.toH1Function.memL2
  obtain ⟨p, hpval, hpgrad⟩ := exists_h1Function_toFun_eq u.toH1Function hmem hgae
  obtain ⟨w, hw⟩ := memH10_of_ae_eq_h10 hV p u (by rw [hpval]; exact hgae)
  have hwval : w.toH1Function.toFun = A.partGreenPotential hV f hf hD hfD := by
    rw [hw, hpval]
  have hwu : w.toH1Function.toFun =ᵐ[volumeMeasureOn V] u.toH1Function.toFun := by
    rw [hwval]
    exact hgae
  refine ⟨w, hwval, ?_⟩
  refine ZeroTraceSobolev.ext ?_ ?_
  · rw [toL2_ofH10Function, ← hval]
    refine (Lp.ext_iff).2 ?_
    filter_upwards [w.toH1Function.coeFn_toScalarL2, u.toH1Function.coeFn_toScalarL2, hwu]
      with x h1 h2 h3
    rw [h1, h2, h3]
  · rw [gradient_ofH10Function, ← hgrad]
    have hgradae : w.toH1Function.grad =ᵐ[volumeMeasureOn V] u.toH1Function.grad :=
      h1grad_ae_eq_of_toFun_ae_eq hV.isOpen hwu
    refine (Lp.ext_iff).2 ?_
    filter_upwards [w.toH1Function.coeFn_gradToHilbertVectorL2,
      u.toH1Function.coeFn_gradToHilbertVectorL2, hgradae] with x h1 h2 h3
    rw [h1, h2]
    simp only [hilbertifyVecField, h3]

/-- **The zero-trace Sobolev function of a bounded part domain whose value function is the Green
potential.** -/
def partGreenH10 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) : H10Function V :=
  Classical.choose (A.exists_partGreenH10 hV hf hD hfD)

@[simp] theorem partGreenH10_toFun {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    (A.partGreenH10 hV hf hD hfD).toH1Function.toFun = A.partGreenPotential hV f hf hD hfD :=
  (Classical.choose_spec (A.exists_partGreenH10 hV hf hD hfD)).1

theorem ofH10Function_partGreenH10 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ZeroTraceSobolev.ofH10Function (A.partGreenH10 hV hf hD hfD) =
      A.partGreenSolution hV hf hD hfD :=
  (Classical.choose_spec (A.exists_partGreenH10 hV hf hD hfD)).2

/-- **The Green potential solves the unshifted zero-trace Dirichlet problem.** -/
theorem isScalarForcedWeakSolution_partGreenH10 {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    IsScalarForcedWeakSolution A.a V f (A.partGreenH10 hV hf hD hfD).toH1Function := by
  have hweak : IsAlphaShiftedWeakSolution A.a V 0 (partDatumL2 hV hf hfD)
      (ZeroTraceSobolev.ofH10Function (A.partGreenH10 hV hf hD hfD)) := by
    rw [A.ofH10Function_partGreenH10 hV hf hD hfD]
    exact A.isAlphaShiftedWeakSolution_partGreenSolution hV hf hD hfD
  have h := isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution
    (A.partGreenH10 hV hf hD hfD) hweak
  refine h.congr_datum ?_
  filter_upwards [partDatumL2_ae hV hf hfD] with x hx
  rw [hx, zero_mul, sub_zero]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
