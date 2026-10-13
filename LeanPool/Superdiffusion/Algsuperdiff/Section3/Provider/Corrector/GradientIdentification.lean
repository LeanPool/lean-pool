/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifierConvergence

/-!
# GradientIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the mollified gradient is the mollification of the gradient

`Algsuperdiff/Section3/Provider/Corrector/MollifiedPrimitive.lean` produces, for
every stationary `L²` scalar `φ` and every smooth compactly supported kernel
`κ`, a member `mollify κ φ` of the dense class of part (i) of
`l.approximation.stationary.by.local` together with its spatial gradient
`mollifyGrad κ φ` (whose `i`th component is the mollification of `φ` by `∂ᵢκ`).

`mollifyGrad κ φ = mollify κ F`  almost surely,

whenever `F` is the strong horizontal gradient of `φ` in `L²(Ω)`
(`Algsuperdiff.Probability.Stationary.HasHorizontalGradient`).

The proof uses **no integration by parts**.  The difference quotients of the
mollified field along the `i`th coordinate orbit converge

* pointwise, for almost every sample, to `mollify (∂ᵢκ) φ`, because the spatial
  realization of `mollify κ φ` is smooth with derivative
  `(∂ᵢκ) ⋆ realize φ` (`fderiv_realize_mollify`), and
* in `L²(Ω)` to `mollify κ Fᵢ`, because the difference quotients of `φ` itself
  converge to `Fᵢ` in `L²(Ω)` and mollification is an `L²` contraction
  (`integral_normSq_mollify_le`).

Fatou's lemma then forces the two limits to agree.  Combining this with the
approximate-identity estimate of
`Algsuperdiff/Section3/Provider/Corrector/MollifierConvergence.lean` shows that
the mollified gradients are `L²`-dense in the stationary potential subspace.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### The Koopman action at the origin -/

section Koopman

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Koopman operator of the zero translation is the identity. -/
theorem koopman_zero (f : Lp E 2 μ) : koopman (μ := μ) (0 : Vec d) f = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := E) (p := 2) f
    (measurePreserving_const_vadd (μ := μ) (0 : Vec d))] with ω hω
  refine hω.trans ?_
  show f ((0 : Vec d) +ᵥ ω) = f ω
  rw [zero_vadd]

end Koopman

/-! ### An `L²`-versus-pointwise uniqueness lemma -/

section Fatou

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E]

/-- If a sequence converges pointwise almost everywhere to `B` and its squared
`L²` distance to `C` tends to zero, then `B = C` almost everywhere.  This is
Fatou's lemma; it replaces the usual "convergence in measure plus subsequence"
argument. -/
theorem ae_eq_of_tendsto_of_tendsto_integral_normSq {A : ℕ → Ω → E} {B C : Ω → E}
    (hAm : ∀ n, AEStronglyMeasurable (A n) μ) (hBm : AEStronglyMeasurable B μ)
    (hCm : AEStronglyMeasurable C μ)
    (hae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => A n ω) Filter.atTop (nhds (B ω)))
    (hint : ∀ n, Integrable (fun ω => ‖A n ω - C ω‖ ^ 2) μ)
    (htend : Filter.Tendsto (fun n => ∫ ω, ‖A n ω - C ω‖ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    B =ᵐ[μ] C := by
  have hgm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (‖A n ω - C ω‖ ^ 2)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hAm n).sub hCm).norm.aemeasurable.pow_const 2)
  have hBCm : AEMeasurable (fun ω => ENNReal.ofReal (‖B ω - C ω‖ ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (((hBm.sub hCm).norm.aemeasurable.pow_const 2))
  have hliminf : ∀ᵐ ω ∂μ, ENNReal.ofReal (‖B ω - C ω‖ ^ 2)
      = Filter.liminf (fun n => ENNReal.ofReal (‖A n ω - C ω‖ ^ 2)) Filter.atTop := by
    filter_upwards [hae] with ω hω
    have h1 : Filter.Tendsto (fun n => ‖A n ω - C ω‖ ^ 2) Filter.atTop
        (nhds (‖B ω - C ω‖ ^ 2)) := ((hω.sub_const (C ω)).norm).pow 2
    have h2 : Filter.Tendsto (fun n => ENNReal.ofReal (‖A n ω - C ω‖ ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal (‖B ω - C ω‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h1
    exact h2.liminf_eq.symm
  have heq : ∀ n, ∫⁻ ω, ENNReal.ofReal (‖A n ω - C ω‖ ^ 2) ∂μ
      = ENNReal.ofReal (∫ ω, ‖A n ω - C ω‖ ^ 2 ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hint n)
      (Filter.Eventually.of_forall fun ω => by positivity)).symm
  have hzero : Filter.liminf
      (fun n => ∫⁻ ω, ENNReal.ofReal (‖A n ω - C ω‖ ^ 2) ∂μ) Filter.atTop = 0 := by
    have hlim : Filter.Tendsto
        (fun n => ∫⁻ ω, ENNReal.ofReal (‖A n ω - C ω‖ ^ 2) ∂μ) Filter.atTop (nhds 0) := by
      simp only [heq]
      simpa using! (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp htend
    exact hlim.liminf_eq
  have hle : ∫⁻ ω, ENNReal.ofReal (‖B ω - C ω‖ ^ 2) ∂μ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ ω, ENNReal.ofReal (‖B ω - C ω‖ ^ 2) ∂μ
        = ∫⁻ ω, Filter.liminf
            (fun n => ENNReal.ofReal (‖A n ω - C ω‖ ^ 2)) Filter.atTop ∂μ :=
          lintegral_congr_ae hliminf
      _ ≤ Filter.liminf
            (fun n => ∫⁻ ω, ENNReal.ofReal (‖A n ω - C ω‖ ^ 2) ∂μ) Filter.atTop :=
          lintegral_liminf_le' hgm
      _ = 0 := hzero
  have hae0 := (lintegral_eq_zero_iff' hBCm).1 hle
  filter_upwards [hae0] with ω hω
  have : ‖B ω - C ω‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hω
  have hnorm : ‖B ω - C ω‖ = 0 := by nlinarith [norm_nonneg (B ω - C ω)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

end Fatou

/-! ### Difference quotients of the mollified orbit -/

section Orbit

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The mollified field is differentiable along every coordinate orbit, with
derivative the mollification by the corresponding partial derivative of the
kernel.  This is the pointwise half of the gradient identification. -/
theorem ae_hasDerivAt_mollify_orbit (ρ : Mollifier d) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∀ᵐ ω ∂μ, HasDerivAt (fun t : ℝ => mollify ρ.toFun φ ((t • basisVec i) +ᵥ ω))
      (mollify (kernelDeriv ρ.toFun i) φ ω) 0 := by
  filter_upwards [ae_locallyIntegrable_realize (d := d) (μ := μ) hφm hφ] with ω hloc
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (realize (d := d) (mollify ρ.toFun φ) ω) := by
    rw [realize_mollify]
    exact ρ.compactSupport.contDiff_convolution_left _ ρ.smooth hloc
  have hpt : ((0 : ℝ) • (basisVec i : Vec d)) = 0 := zero_smul _ _
  have hfd : HasFDerivAt (realize (d := d) (mollify ρ.toFun φ) ω)
      (fderiv ℝ (realize (d := d) (mollify ρ.toFun φ) ω) ((0 : ℝ) • (basisVec i : Vec d)))
      ((0 : ℝ) • (basisVec i : Vec d)) :=
    (hsmooth.differentiable (by simp) _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • (basisVec i : Vec d)) (basisVec i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (basisVec i : Vec d)
  have hcomp := hfd.comp_hasDerivAt (0 : ℝ) hline
  rw [hpt] at hcomp
  have hval : fderiv ℝ (realize (d := d) (mollify ρ.toFun φ) ω) 0 (basisVec i)
      = mollify (kernelDeriv ρ.toFun i) φ ω := by
    rw [fderiv_realize_mollify ρ.compactSupport ρ.smooth hloc 0 i,
      realize_mollifyGrad_toVec, realize_apply, zero_vadd]
  rw [hval] at hcomp
  exact hcomp

end Orbit

/-! ### Difference quotients along a coordinate orbit -/

section DiffQuot

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The difference quotient of a stationary field along the `i`th coordinate
orbit at scale `t`. -/
def diffQuot (i : Fin d) (t : ℝ) (φ : Ω → ℝ) (ω : Ω) : ℝ :=
  t⁻¹ • (φ ((t • basisVec i) +ᵥ ω) - φ ω)

end DiffQuot

section DiffQuotLp

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

omit [VAddInvariantMeasure (Vec d) Ω μ] in
private theorem stronglyMeasurable_diffQuot (i : Fin d) (t : ℝ) {φ : Ω → ℝ}
    (hφm : StronglyMeasurable φ) : StronglyMeasurable (diffQuot (Ω := Ω) i t φ) :=
  ((hφm.comp_measurable (measurable_const_vadd (t • basisVec i))).sub hφm).const_smul (t⁻¹ : ℝ)

private theorem memLp_diffQuot (i : Fin d) (t : ℝ) {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) :
    MemLp (diffQuot (Ω := Ω) i t φ) 2 μ :=
  ((hφ.comp_measurePreserving
    (measurePreserving_const_vadd (μ := μ) (t • basisVec i))).sub hφ).const_smul (t⁻¹ : ℝ)

/-- The difference quotient is represented in `L²` by the corresponding
difference quotient of the Koopman orbit. -/
private theorem integral_normSq_diffQuot_sub_eq (i : Fin d) (t : ℝ)
    {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) {G : Ω → ℝ} (hG : MemLp G 2 μ) :
    ∫ ω, ‖diffQuot i t φ ω - G ω‖ ^ 2 ∂μ
      = ‖t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ)
          - hG.toLp G‖ ^ 2 := by
  rw [norm_sq_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub
      (t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ)) (hG.toLp G),
    Lp.coeFn_smul (t⁻¹ : ℝ) (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ),
    Lp.coeFn_sub (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ)) (hφ.toLp φ),
    coeFn_koopman_toLp hφ (t • basisVec i), hφ.coeFn_toLp, hG.coeFn_toLp]
    with ω h1 h2 h3 h4 h5 h6
  rw [h1]
  simp only [Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  rfl

end DiffQuotLp

/-! ### The gradient identification -/

section Identification

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The sequence of scales along which the difference quotients are taken. -/
def quotScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem quotScale_pos (n : ℕ) : 0 < quotScale n := by
  unfold quotScale; positivity

private theorem tendsto_quotScale :
    Filter.Tendsto quotScale Filter.atTop (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) := by
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto quotScale Filter.atTop (nhds (0 : ℝ)) := by
    refine h.congr fun n => ?_
    rw [quotScale, one_div]
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within quotScale hlim ?_
  exact Filter.Eventually.of_forall fun n => (quotScale_pos n).ne'

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] in
/-- The difference quotients converge to the strong horizontal derivative in
`L²(Ω)`. -/
private theorem tendsto_integral_normSq_diffQuot_sub (i : Fin d)
    {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) {G : Ω → ℝ} (hG : MemLp G 2 μ)
    (hderiv : HasDerivAt (fun t : ℝ => koopman (μ := μ) (t • basisVec i) (hφ.toLp φ))
      (hG.toLp G) 0) :
    Filter.Tendsto (fun n : ℕ => ∫ ω, ‖diffQuot i (quotScale n) φ ω - G ω‖ ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  have hf0 : koopman (μ := μ) ((0 : ℝ) • (basisVec i : Vec d)) (hφ.toLp φ) = hφ.toLp φ := by
    rw [zero_smul, koopman_zero]
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (hG.toLp G)) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 hderiv
    simpa only [slope_fun_def, vsub_eq_sub, sub_zero, hf0] using hthis
  have hQtend : Filter.Tendsto
      (fun n : ℕ => (quotScale n)⁻¹ •
        (koopman (μ := μ) (quotScale n • basisVec i) (hφ.toLp φ) - hφ.toLp φ))
      Filter.atTop (nhds (hG.toLp G)) := hslope.comp tendsto_quotScale
  have hnorm : Filter.Tendsto (fun n : ℕ =>
      ‖(quotScale n)⁻¹ •
        (koopman (μ := μ) (quotScale n • basisVec i) (hφ.toLp φ) - hφ.toLp φ)
        - hG.toLp G‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using ((hQtend.sub_const (hG.toLp G)).norm).pow 2
  refine hnorm.congr fun n => ?_
  exact (integral_normSq_diffQuot_sub_eq i (quotScale n) hφ hG).symm

/-- The mollified difference quotients converge pointwise to the mollification
by the corresponding partial derivative of the kernel. -/
private theorem ae_tendsto_mollify_diffQuot (ρ : Mollifier d) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => mollify ρ.toFun (diffQuot i (quotScale n) φ) ω) Filter.atTop
      (nhds (mollify (kernelDeriv ρ.toFun i) φ ω)) := by
  have hintφ : ∀ᵐ ω ∂μ, Integrable (fun y => ρ.toFun y • φ ((-y) +ᵥ ω)) volume :=
    ae_integrable_smul_comp_vadd (μ := μ) ρ.continuous ρ.integrable hφm hφ
  have hintshift : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      Integrable (fun y =>
        ρ.toFun y • φ ((quotScale n • basisVec i) +ᵥ ((-y) +ᵥ ω))) volume := by
    refine ae_all_iff.2 fun n => ?_
    exact ae_integrable_smul_comp_vadd (μ := μ)
      (X := fun ω => φ ((quotScale n • basisVec i) +ᵥ ω)) ρ.continuous ρ.integrable
      (hφm.comp_measurable (measurable_const_vadd (quotScale n • basisVec i)))
      (hφ.comp_measurePreserving
        (measurePreserving_const_vadd (μ := μ) (quotScale n • basisVec i)))
  filter_upwards [hintφ, hintshift,
    ae_hasDerivAt_mollify_orbit (μ := μ) ρ i hφm hφ] with ω h0 hn hderiv'
  have heq : ∀ n : ℕ, mollify ρ.toFun (diffQuot i (quotScale n) φ) ω
      = (quotScale n)⁻¹ • (mollify ρ.toFun φ ((quotScale n • basisVec i) +ᵥ ω)
        - mollify ρ.toFun φ ω) := by
    intro n
    show mollify ρ.toFun (fun ω' =>
        (quotScale n)⁻¹ • (φ ((quotScale n • basisVec i) +ᵥ ω') - φ ω')) ω = _
    rw [mollify_smul ρ.toFun ((quotScale n)⁻¹ : ℝ)
        (fun ω' => φ ((quotScale n • basisVec i) +ᵥ ω') - φ ω') ω,
      mollify_sub (hn n) h0, mollify_comp_vadd]
  have hg0 : mollify ρ.toFun φ (((0 : ℝ) • (basisVec i : Vec d)) +ᵥ ω)
      = mollify ρ.toFun φ ω := by
    rw [zero_smul, zero_vadd]
  have hs : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (mollify ρ.toFun φ ((t • basisVec i) +ᵥ ω) - mollify ρ.toFun φ ω))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (mollify (kernelDeriv ρ.toFun i) φ ω)) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 hderiv'
    simpa only [slope_fun_def, vsub_eq_sub, sub_zero, hg0] using hthis
  exact (hs.comp tendsto_quotScale).congr fun n => (heq n).symm

/-- **Componentwise gradient identification.**  If the coordinate orbit of `φ`
has strong `L²` derivative `G` at the origin, then mollifying `φ` by the `i`th
partial derivative of the kernel is the same as mollifying `G` by the kernel. -/
theorem mollify_kernelDeriv_ae_eq (ρ : Mollifier d) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    {G : Ω → ℝ} (hGm : StronglyMeasurable G) (hG : MemLp G 2 μ)
    (hderiv : HasDerivAt (fun t : ℝ => koopman (μ := μ) (t • basisVec i) (hφ.toLp φ))
      (hG.toLp G) 0) :
    mollify (kernelDeriv ρ.toFun i) φ =ᵐ[μ] mollify ρ.toFun G := by
  have hDm : ∀ n : ℕ, StronglyMeasurable (diffQuot (Ω := Ω) i (quotScale n) φ) := fun n =>
    stronglyMeasurable_diffQuot i (quotScale n) hφm
  have hDL : ∀ n : ℕ, MemLp (diffQuot (Ω := Ω) i (quotScale n) φ) 2 μ := fun n =>
    memLp_diffQuot (μ := μ) i (quotScale n) hφ
  have hZm : ∀ n : ℕ, StronglyMeasurable
      fun ω => diffQuot (Ω := Ω) i (quotScale n) φ ω - G ω := fun n => (hDm n).sub hGm
  have hZL : ∀ n : ℕ, MemLp
      (fun ω => diffQuot (Ω := Ω) i (quotScale n) φ ω - G ω) 2 μ := fun n => (hDL n).sub hG
  have hcontr : ∀ n : ℕ,
      ∫ ω, ‖mollify ρ.toFun (diffQuot i (quotScale n) φ) ω - mollify ρ.toFun G ω‖ ^ 2 ∂μ
        ≤ (∫ y, |ρ.toFun y|) ^ 2 * ∫ ω, ‖diffQuot i (quotScale n) φ ω - G ω‖ ^ 2 ∂μ := by
    intro n
    have hsub : ∀ᵐ ω ∂μ,
        mollify ρ.toFun (fun ω' => diffQuot i (quotScale n) φ ω' - G ω') ω
          = mollify ρ.toFun (diffQuot i (quotScale n) φ) ω - mollify ρ.toFun G ω := by
      filter_upwards [ae_integrable_smul_comp_vadd (μ := μ) ρ.continuous ρ.integrable
          (hDm n) (hDL n),
        ae_integrable_smul_comp_vadd (μ := μ) ρ.continuous ρ.integrable hGm hG] with ω h1 h2
      exact mollify_sub h1 h2
    have hbase := integral_normSq_mollify_le (μ := μ) ρ.continuous ρ.integrable
      (hZm n) (hZL n)
    refine le_trans (le_of_eq ?_) hbase
    exact (integral_congr_ae (by filter_upwards [hsub] with ω hω; rw [hω])).symm
  have hL2 := tendsto_integral_normSq_diffQuot_sub (μ := μ) i hφ hG hderiv
  have hAL2 : Filter.Tendsto (fun n : ℕ =>
      ∫ ω, ‖mollify ρ.toFun (diffQuot i (quotScale n) φ) ω - mollify ρ.toFun G ω‖ ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun ω => by positivity) hcontr ?_
    simpa using hL2.const_mul ((∫ y, |ρ.toFun y|) ^ 2)
  have hmemA : ∀ n : ℕ, MemLp (mollify ρ.toFun (diffQuot (Ω := Ω) i (quotScale n) φ)) 2 μ :=
    fun n => memLp_two_mollify ρ.continuous ρ.integrable (hDm n) (hDL n)
  have hmemC : MemLp (mollify ρ.toFun G) 2 μ :=
    memLp_two_mollify ρ.continuous ρ.integrable hGm hG
  have hmemB : MemLp (mollify (kernelDeriv ρ.toFun i) φ) 2 μ :=
    memLp_two_mollify (continuous_kernelDeriv ρ.smooth i)
      (integrable_kernelDeriv ρ.compactSupport ρ.smooth i) hφm hφ
  refine ae_eq_of_tendsto_of_tendsto_integral_normSq
    (fun n => (hmemA n).aestronglyMeasurable) hmemB.aestronglyMeasurable
    hmemC.aestronglyMeasurable (ae_tendsto_mollify_diffQuot (μ := μ) ρ i hφm hφ)
    (fun n => ?_) hAL2
  have hd : MemLp (fun ω =>
      mollify ρ.toFun (diffQuot (Ω := Ω) i (quotScale n) φ) ω - mollify ρ.toFun G ω) 2 μ :=
    (hmemA n).sub hmemC
  exact (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd

end Identification

/-! ### The vector form of the gradient identification -/

section VectorIdentification

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The `i`th coordinate of a Euclidean-vector-valued stationary field. -/
def coordField (F : Ω → HilbertVec d) (i : Fin d) (ω : Ω) : ℝ := (F ω).toVec i

omit [AddAction (Vec d) Ω] [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
  [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
theorem stronglyMeasurable_coordField {F : Ω → HilbertVec d} (hFm : StronglyMeasurable F)
    (i : Fin d) : StronglyMeasurable (coordField F i) :=
  (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).continuous.comp_stronglyMeasurable hFm

omit [AddAction (Vec d) Ω] [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
  [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
theorem memLp_coordField {F : Ω → HilbertVec d} (hFm : StronglyMeasurable F)
    (hF : MemLp F 2 μ) (i : Fin d) : MemLp (coordField F i) 2 μ := by
  refine MemLp.mono' hF.norm (stronglyMeasurable_coordField hFm i).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  simpa [coordField, Real.norm_eq_abs] using HilbertVec.abs_apply_le_norm (F ω) i

omit [MeasurableSpace Ω] [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
  [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
/-- Mollification commutes with taking a coordinate. -/
theorem mollify_coordField_eq {κ : Vec d → ℝ} {F : Ω → HilbertVec d} {ω : Ω}
    (hint : Integrable (fun y => κ y • F ((-y) +ᵥ ω)) volume) (i : Fin d) :
    mollify κ (coordField F i) ω = (mollify κ F ω).toVec i := by
  calc mollify κ (coordField F i) ω
      = ∫ y, (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i)
          (κ y • F ((-y) +ᵥ ω)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show κ y • coordField F i ((-y) +ᵥ ω)
          = (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i) (κ y • F ((-y) +ᵥ ω))
        rw [map_smul]
        rfl
    _ = (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i)
          (∫ y, κ y • F ((-y) +ᵥ ω)) :=
        (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).integral_comp_comm hint
    _ = (mollify κ F ω).toVec i := rfl

omit [AddAction (Vec d) Ω] [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
  [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
/-- The `L²` coordinate projection is computed by the coordinate field. -/
theorem vectorL2Coord_toLp {F : Ω → HilbertVec d} (hFm : StronglyMeasurable F)
    (hF : MemLp F 2 μ) (i : Fin d) :
    vectorL2Coord (μ := μ) i (hF.toLp F) = (memLp_coordField hFm hF i).toLp (coordField F i) := by
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i) (hF.toLp F),
    hF.coeFn_toLp, (memLp_coordField hFm hF i).coeFn_toLp] with ω h1 h2 h3
  rw [h3]
  refine h1.trans ?_
  rw [h2]
  rfl

/-- **The gradient identification.**  The mollified gradient of a stationary
`L²` scalar is the mollification of its strong horizontal gradient. -/
theorem mollifyGrad_ae_eq_mollify (ρ : Mollifier d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    {F : Ω → HilbertVec d} (hFm : StronglyMeasurable F) (hF : MemLp F 2 μ)
    (hHG : HasHorizontalGradient (μ := μ) (hφ.toLp φ) (hF.toLp F)) :
    mollifyGrad ρ.toFun φ =ᵐ[μ] mollify ρ.toFun F := by
  have hcomp : ∀ i : Fin d,
      mollify (kernelDeriv ρ.toFun i) φ =ᵐ[μ] mollify ρ.toFun (coordField F i) := by
    intro i
    refine mollify_kernelDeriv_ae_eq ρ i hφm hφ (stronglyMeasurable_coordField hFm i)
      (memLp_coordField hFm hF i) ?_
    have h := hHG i
    rwa [vectorL2Coord_toLp hFm hF i] at h
  filter_upwards [ae_all_iff.2 hcomp,
    ae_integrable_smul_comp_vadd (μ := μ) ρ.continuous ρ.integrable hFm hF] with ω h1 h2
  refine HilbertVec.ext fun i => ?_
  have hlhs : (mollifyGrad ρ.toFun φ ω) i = mollify (kernelDeriv ρ.toFun i) φ ω :=
    mollifyGrad_toVec ρ.toFun φ ω i
  rw [hlhs, h1 i]
  exact mollify_coordField_eq h2 i

end VectorIdentification

/-! ### Density of the mollified gradients in the stationary potential subspace -/

section Density

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω]
  [ContinuousVAdd (Vec d) Ω] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
/-- The `L²` energy of the difference of two square-integrable fields is the
squared distance of their classes. -/
theorem integral_normSq_sub_eq_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X Y : Ω → E} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ = ‖hX.toLp X - hY.toLp Y‖ ^ 2 := by
  rw [norm_sq_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hX.toLp X) (hY.toLp Y), hX.coeFn_toLp, hY.coeFn_toLp]
    with ω h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply, h2, h3]

/-- **Density of the mollified gradients.**  Every element of the stationary
potential subspace `L²_pot(Ω)` is approximated in `L²(Ω)`, to any prescribed
accuracy, by the mollified gradient of a stationary square-integrable scalar.
This is what removes the smooth-primitive hypothesis from the cutoff core of
part (i) of `l.approximation.stationary.by.local`. -/
theorem exists_mollifyGrad_integral_normSq_sub_le
    {p : Ω → HilbertVec d} (hp : MemLp p 2 μ)
    (hmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (hr : 0 < r) (φ : Ω → ℝ), StronglyMeasurable φ ∧ MemLp φ 2 μ ∧
      ∫ ω, ‖mollifyGrad (Mollifier.ofRadius d hr).toFun φ ω - p ω‖ ^ 2 ∂μ ≤ ε := by
  classical
  set δ : ℝ := Real.sqrt (ε / 4) with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 (by linarith)
  have hclosure : hp.toLp p
      ∈ closure ((horizontalGradientRange (μ := μ) (d := d) : Submodule ℝ (VectorL2 d μ)) :
        Set (VectorL2 d μ)) := hmem
  obtain ⟨G, hGmem, hGdist⟩ := Metric.mem_closure_iff.1 hclosure δ hδ
  obtain ⟨ψ, hψG⟩ := hGmem
  -- honest strongly measurable representatives
  set ψ₀ : Ω → ℝ := (Lp.aestronglyMeasurable ψ).mk ψ with hψ₀def
  have hψ₀m : StronglyMeasurable ψ₀ := (Lp.aestronglyMeasurable ψ).stronglyMeasurable_mk
  have hψ₀ae : ⇑ψ =ᵐ[μ] ψ₀ := (Lp.aestronglyMeasurable ψ).ae_eq_mk
  have hψ₀L : MemLp ψ₀ 2 μ := (Lp.memLp ψ).ae_eq hψ₀ae
  have hψ₀toLp : hψ₀L.toLp ψ₀ = ψ := by
    rw [MemLp.toLp_congr hψ₀L (Lp.memLp ψ) hψ₀ae.symm, Lp.toLp_coeFn]
  set G₀ : Ω → HilbertVec d := (Lp.aestronglyMeasurable G).mk G with hG₀def
  have hG₀m : StronglyMeasurable G₀ := (Lp.aestronglyMeasurable G).stronglyMeasurable_mk
  have hG₀ae : ⇑G =ᵐ[μ] G₀ := (Lp.aestronglyMeasurable G).ae_eq_mk
  have hG₀L : MemLp G₀ 2 μ := (Lp.memLp G).ae_eq hG₀ae
  have hG₀toLp : hG₀L.toLp G₀ = G := by
    rw [MemLp.toLp_congr hG₀L (Lp.memLp G) hG₀ae.symm, Lp.toLp_coeFn]
  have hHG : HasHorizontalGradient (μ := μ) (hψ₀L.toLp ψ₀) (hG₀L.toLp G₀) := by
    rw [hψ₀toLp, hG₀toLp]
    exact hψG
  -- the tail term
  have htail : ∫ ω, ‖G₀ ω - p ω‖ ^ 2 ∂μ ≤ ε / 4 := by
    rw [integral_normSq_sub_eq_norm_sq hG₀L hp, hG₀toLp]
    have hd : ‖G - hp.toLp p‖ < δ := by
      rw [← dist_eq_norm]
      exact (dist_comm (hp.toLp p) G) ▸ hGdist
    have hsq : δ ^ 2 = ε / 4 := Real.sq_sqrt (by linarith)
    nlinarith [norm_nonneg (G - hp.toLp p), hd, hδ]
  -- the mollification term
  obtain ⟨r, hr, hmoll⟩ := exists_radius_integral_normSq_mollify_sub_le (μ := μ) (d := d)
    hG₀m hG₀L (ε := ε / 4) (by linarith)
  refine ⟨r, hr, ψ₀, hψ₀m, hψ₀L, ?_⟩
  set ρ : Mollifier d := Mollifier.ofRadius d hr with hρdef
  have hid : mollifyGrad ρ.toFun ψ₀ =ᵐ[μ] mollify ρ.toFun G₀ :=
    mollifyGrad_ae_eq_mollify ρ hψ₀m hψ₀L hG₀m hG₀L hHG
  have hmemM : MemLp (mollify ρ.toFun G₀) 2 μ :=
    memLp_two_mollify ρ.continuous ρ.integrable hG₀m hG₀L
  have hint1 : Integrable (fun ω => ‖mollify ρ.toFun G₀ ω - G₀ ω‖ ^ 2) μ := by
    have h : MemLp (fun ω => mollify ρ.toFun G₀ ω - G₀ ω) 2 μ := hmemM.sub hG₀L
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  have hint2 : Integrable (fun ω => ‖G₀ ω - p ω‖ ^ 2) μ := by
    have h : MemLp (fun ω => G₀ ω - p ω) 2 μ := hG₀L.sub hp
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  have hstep : ∫ ω, ‖mollifyGrad ρ.toFun ψ₀ ω - p ω‖ ^ 2 ∂μ
      ≤ ∫ ω, (2 * ‖mollify ρ.toFun G₀ ω - G₀ ω‖ ^ 2 + 2 * ‖G₀ ω - p ω‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      ((hint1.const_mul 2).add (hint2.const_mul 2)) ?_
    filter_upwards [hid] with ω hω
    rw [hω]
    have htri : ‖mollify ρ.toFun G₀ ω - p ω‖
        ≤ ‖mollify ρ.toFun G₀ ω - G₀ ω‖ + ‖G₀ ω - p ω‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub
        (mollify ρ.toFun G₀ ω) (G₀ ω) (p ω)
    nlinarith [htri, norm_nonneg (mollify ρ.toFun G₀ ω - p ω),
      norm_nonneg (mollify ρ.toFun G₀ ω - G₀ ω), norm_nonneg (G₀ ω - p ω),
      sq_nonneg (‖mollify ρ.toFun G₀ ω - G₀ ω‖ - ‖G₀ ω - p ω‖)]
  refine hstep.trans ?_
  rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul,
    integral_const_mul]
  linarith [hmoll, htail]

end Density


end

end Algsuperdiff.Section3.Provider.Corrector
