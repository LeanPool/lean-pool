/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.Young
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Convolution with integrable kernels in `L_p`

On a finite-dimensional real vector space `V` with a Haar measure `μ`, the **convolution** of an
integrable kernel `K` with `f ∈ L_p` is `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy` (`Rd.conv`, Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ`).

**Young's inequality** `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`, `1 ≤ p ≤ ∞` (`Rd.eLpNorm_conv_le`), is the case
of the group `V` of `MeasureTheory.eLpNorm_complexConvolution_le`. The integral of the convolution
converges absolutely at almost every point (`MeasureTheory.ae_convolutionExistsAt`), so
convolution is linear in `f` almost everywhere (`Rd.conv_add_ae`, `Rd.conv_sub_ae`,
`Rd.conv_finsetSum_ae`, and `Rd.conv_add_ae_of_memLp` for `f ∈ L_p`, `g ∈ L_r`) and defines a
bounded operator on `L_p` of norm at most `‖K‖_1` (`Rd.convLp`). These operators compose like
their kernels, `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f` (`Rd.convLp_convLp`, from the associativity
`Rd.conv_conv_ae`), and are linear in the kernel (`Rd.convLp_sub_kernel`).

**Pointwise
bounds**: if `|K| ≤ A` and `K = 0` outside `closedBall(0, ρ)`, Hölder's inequality on balls gives
`|(K ⋆ g)(x)| ≤ A |closedBall(0,ρ)|^(1-1/p) ‖g‖_p` (`Rd.lintegral_closedBall_le`,
`Rd.enorm_conv_le_of_bound`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Convolution

namespace Rd

/-! ### Convolution and Young's inequality -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-- The **convolution** of complex functions, `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy` (Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ`). -/
noncomputable def conv (K f : V → ℂ) (μ : Measure V) : V → ℂ :=
  K ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] f

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy`. -/
theorem conv_apply (K f : V → ℂ) (μ : Measure V) (x : V) :
    conv K f μ x = ∫ y, K y * f (x - y) ∂μ := by
  rw [conv, convolution_def]
  rfl

/-- Convolutions of a.e. strongly measurable functions are a.e. strongly measurable (Mathlib's
`AEStronglyMeasurable.convolution_integrand` and `AEStronglyMeasurable.integral_prod_right'`). -/
theorem aestronglyMeasurable_conv {K f : V → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (conv K f μ) μ :=
  (hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf).integral_prod_right'

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The pointwise bound `|(K ⋆ f)(x)| ≤ ∫ |K(y)| |f(x - y)| dy`. -/
theorem enorm_conv_le_lintegral (K f : V → ℂ) (x : V) :
    ‖conv K f μ x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ := by
  rw [conv_apply]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun y => eNorm_mul _ _

/-- **Young's inequality** for an integrable kernel: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`, `1 ≤ p ≤ ∞`
(`MeasureTheory.eLpNorm_complexConvolution_le` on the group `V`). -/
theorem eLpNorm_conv_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K f : V → ℂ}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (conv K f μ) p μ ≤ eLpNorm K 1 μ * eLpNorm f p μ :=
  eLpNorm_complexConvolution_le hp1 hK hf

/-- Convolution of an integrable kernel with an `L_p` function is in `L_p`. -/
theorem memLp_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K f : V → ℂ} (hK : Integrable K μ)
    (hf : MemLp f p μ) : MemLp (conv K f μ) p μ :=
  memLp_convolution hp1 hK hf

/-- **Convolution is additive** almost everywhere, in the two-exponent form: for `f ∈ L_p` and
`g ∈ L_r` with `1 ≤ p, r < ∞`, `K ⋆ (f + g) = K ⋆ f + K ⋆ g` almost everywhere, since both
convolution integrals converge absolutely at almost every point
(`MeasureTheory.ae_convolutionExistsAt`). -/
theorem conv_add_ae_of_memLp {p r : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hr1 : 1 ≤ r) (hr : r ≠ ∞)
    {K f g : V → ℂ} (hK : Integrable K μ) (hf : MemLp f p μ) (hg : MemLp g r μ) :
    conv K (f + g) μ =ᵐ[μ] conv K f μ + conv K g μ := by
  filter_upwards [ae_convolutionExistsAt hp1 hp hK hf, ae_convolutionExistsAt hr1 hr hK hg]
    with x hfx hgx
  exact hfx.distrib_add hgx

/-- **Convolution is additive** in `f ∈ L_p` almost everywhere: the case of equal exponents of
`Rd.conv_add_ae_of_memLp`. -/
theorem conv_add_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f g : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    conv K (f + g) μ =ᵐ[μ] conv K f μ + conv K g μ :=
  conv_add_ae_of_memLp hp1 hp hp1 hp hK hf hg

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- Convolution is homogeneous in `f`. -/
theorem conv_smul (K f : V → ℂ) (c : ℂ) : conv K (c • f) μ = c • conv K f μ :=
  convolution_smul

/-- **The double convolution integral converges absolutely almost everywhere**: for integrable
`K`, `L` and `f ∈ L_p`, `1 ≤ p < ∞`, for almost every `x₀`,
`∫∫ |K(y)| |L(x - y)| |f(x₀ - x)| dx dy < ∞`. The double integral is
`∫ |K(y)| F(x₀ - y) dy` with `F(z) = ∫ |L(w)| |f(z - w)| dw`, and the integral form of Young's
inequality, applied twice, bounds the integral of its `p`-th power. -/
theorem ae_integrable_conv_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K L f : V → ℂ}
    (hK : Integrable K μ) (hL : Integrable L μ) (hf : MemLp f p μ) :
    ∀ᵐ x₀ ∂μ, Integrable (Function.uncurry fun x y => K y * (L (x - y) * f (x₀ - x)))
      (μ.prod μ) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hfm := hf.aestronglyMeasurable
  set F : V → ℝ≥0∞ := fun z => ∫⁻ w, ‖L w‖ₑ * ‖f (z - w)‖ₑ ∂μ with hFdef
  have hF : AEMeasurable F μ := aemeasurable_lintegral_kernel hL.aestronglyMeasurable hfm
  set G : V → ℝ≥0∞ := fun x₀ => ∫⁻ y, ‖K y‖ₑ * F (x₀ - y) ∂μ with hGdef
  have hGm : AEMeasurable G μ :=
    (hK.aestronglyMeasurable.eNorm.comp_snd.mul (hF.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ))).lintegral_prod_right'
  -- the double integral of the norms is `G x₀`
  have hdouble : ∀ x₀, ∫⁻ z, ‖Function.uncurry (fun x y => K y * (L (x - y) * f (x₀ - x))) z‖ₑ
      ∂(μ.prod μ) = G x₀ := fun x₀ => by
    have hmeas : AEMeasurable (Function.uncurry fun x y =>
        ‖K y‖ₑ * (‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ)) (μ.prod μ) :=
      hK.aestronglyMeasurable.eNorm.comp_snd.mul
        ((hL.aestronglyMeasurable.eNorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul
          (hfm.eNorm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀)).comp_fst)
    have hrw : (fun z : V × V =>
        ‖Function.uncurry (fun x y => K y * (L (x - y) * f (x₀ - x))) z‖ₑ) =
        Function.uncurry fun x y => ‖K y‖ₑ * (‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) := by
      funext z
      obtain ⟨x, y⟩ := z
      simp only [Function.uncurry_apply_pair, eNorm_mul]
    have hinner : ∀ y, AEMeasurable (fun x => ‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) μ := fun y =>
      (hL.aestronglyMeasurable.eNorm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right μ y).quasiMeasurePreserving).mul
        (hfm.eNorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀))
    rw [hrw, lintegral_prod _ hmeas]
    simp only [Function.uncurry_apply_pair]
    rw [lintegral_lintegral_swap hmeas]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul'' _ (hinner y),
      ← lintegral_add_right_eq_self (fun x => ‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) y]
    congr 1
    refine lintegral_congr fun w => ?_
    simp only [add_sub_cancel_right]
    rw [show x₀ - (w + y) = x₀ - y - w by abel]
  -- the `p`-th power of `G` has finite integral
  have hK1 : ∫⁻ y, ‖K y‖ₑ ∂μ ≠ ∞ := hK.2.ne
  have hL1 : ∫⁻ y, ‖L y‖ₑ ∂μ ≠ ∞ := hL.2.ne
  have hfq : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    rw [← eLpNorm_rpow_eq hfm hp0 hp]
    exact ENNReal.rpow_ne_top_of_nonneg hq.le hf.eLpNorm_ne_top
  have hGfin : ∫⁻ x₀, G x₀ ^ p.toReal ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ ((lintegral_rpow_lintegral_mul_le hq1
      hK.aestronglyMeasurable.eNorm hF).trans (mul_le_mul' le_rfl
        (lintegral_rpow_lintegral_mul_le hq1 hL.aestronglyMeasurable.eNorm hfm.eNorm)))
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le hK1)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le hL1) hfq)
  filter_upwards [ae_lt_top' (hGm.pow_const _) hGfin] with x₀ hx₀
  have hG : G x₀ < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hq] at hx₀
    exact lt_irrefl _ hx₀
  refine ⟨hK.aestronglyMeasurable.comp_snd.mul
    ((hL.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul
      ((hfm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀)).comp_fst)), ?_⟩
  rw [HasFiniteIntegral, hdouble x₀]
  exact hG

/-- **Convolution is associative**: `(K ⋆ L) ⋆ f = K ⋆ (L ⋆ f)` almost everywhere for integrable
`K`, `L` and `f ∈ L_p`, `1 ≤ p < ∞` (Mathlib's `convolution_assoc'`, with the absolute convergence
of `Rd.ae_integrable_conv_conv`). -/
theorem conv_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K L f : V → ℂ}
    (hK : Integrable K μ) (hL : Integrable L μ) (hf : MemLp f p μ) :
    conv (conv K L μ) f μ =ᵐ[μ] conv K (conv L f μ) μ := by
  filter_upwards [ae_integrable_conv_conv hp1 hp hK hL hf] with x₀ hx₀
  exact convolution_assoc' (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (fun x y z => by simp only [ContinuousLinearMap.mul_apply']; ring)
    (hK.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hL)
    (ae_convolutionExistsAt hp1 hp hL hf) hx₀

/-- **Convolution is additive in the kernel** almost everywhere, for integrable kernels and
`f ∈ L_p`. -/
theorem add_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K K' f : V → ℂ}
    (hK : Integrable K μ) (hK' : Integrable K' μ) (hf : MemLp f p μ) :
    conv (K + K') f μ =ᵐ[μ] conv K f μ + conv K' f μ := by
  filter_upwards [ae_convolutionExistsAt hp1 hp hK hf, ae_convolutionExistsAt hp1 hp hK' hf]
    with x hx hx'
  exact hx.add_distrib hx'

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- Convolution is homogeneous in the kernel. -/
theorem smul_conv (K f : V → ℂ) (c : ℂ) : conv (c • K) f μ = c • conv K f μ :=
  smul_convolution

/-- **Convolution is subtractive in the kernel** almost everywhere. -/
theorem sub_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K K' f : V → ℂ}
    (hK : Integrable K μ) (hK' : Integrable K' μ) (hf : MemLp f p μ) :
    conv (K - K') f μ =ᵐ[μ] conv K f μ - conv K' f μ := by
  have hneg : conv (-K') f μ = -conv K' f μ := by
    rw [show -K' = (-1 : ℂ) • K' by simp, smul_conv]
    simp
  filter_upwards [add_conv_ae hp1 hp hK hK'.neg hf] with x hx
  rw [sub_eq_add_neg K K', hx, Pi.add_apply, hneg, Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg]

/-- **Convolution is subtractive in `f`** almost everywhere: `K ⋆ (f - g) = K ⋆ f - K ⋆ g` a.e.
for `K ∈ L_1` and `f, g ∈ L_p`, `1 ≤ p < ∞`. -/
theorem conv_sub_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f g : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    conv K (f - g) μ =ᵐ[μ] conv K f μ - conv K g μ := by
  have hneg : conv K (-g) μ = -conv K g μ := by
    rw [show -g = (-1 : ℂ) • g by simp, conv_smul]
    simp
  filter_upwards [conv_add_ae hp1 hp hK hf hg.neg] with x hx
  rw [sub_eq_add_neg f g, hx, Pi.add_apply, hneg, Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg]

/-- **Convolution is linear in `f`** almost everywhere: `K ⋆ ∑_i f_i = ∑_i K ⋆ f_i` a.e. for
`K ∈ L_1` and finitely many `f_i ∈ L_p`, `1 ≤ p < ∞`. -/
theorem conv_finsetSum_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} {K : V → ℂ}
    (hK : Integrable K μ) {s : Finset ι} {f : ι → V → ℂ} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    conv K (∑ i ∈ s, f i) μ =ᵐ[μ] ∑ i ∈ s, conv K (f i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine Filter.EventuallyEq.of_eq (funext fun x => ?_)
    simp [conv_apply]
  | insert i s hi ih =>
    have hs : MemLp (∑ j ∈ s, f j) p μ :=
      memLp_finsetSum' s fun j hj => hf j (Finset.mem_insert_of_mem hj)
    filter_upwards [conv_add_ae hp1 hp hK (hf i (Finset.mem_insert_self i s)) hs,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)] with x h1 h2
    rw [Finset.sum_insert hi, h1, Pi.add_apply, h2, Finset.sum_insert hi, Pi.add_apply]

/-- Convolutions of functions that agree almost everywhere agree everywhere (Mathlib's
`convolution_congr`). -/
theorem conv_congr_ae {K f g : V → ℂ} (hfg : f =ᵐ[μ] g) : conv K f μ = conv K g μ :=
  convolution_congr (ContinuousLinearMap.mul ℂ ℂ) (Filter.EventuallyEq.refl _ K) hfg

/-- **Convolution is commutative**: `K ⋆ L = L ⋆ K` (Mathlib's `convolution_flip`). -/
theorem conv_comm (K L : V → ℂ) : conv K L μ = conv L K μ := by
  rw [conv, conv, ← convolution_flip, ContinuousLinearMap.flip_mul]

/-- Convolutions of integrable functions are integrable (Mathlib's
`Integrable.integrable_convolution`). -/
theorem integrable_conv {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ) :
    Integrable (conv K L μ) μ :=
  hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hL

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Young's inequality for the classes in `L_p`**:
`‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p` for `f ∈ L_p`. -/
theorem norm_toLp_conv_le {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖(memLp_conv Fact.out hK (Lp.memLp f)).toLp (conv K f μ)‖ ≤
      (eLpNorm K 1 μ).toReal * ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top
    (Lp.eLpNorm_ne_top f)) (eLpNorm_conv_le Fact.out hK.aestronglyMeasurable
      (Lp.aestronglyMeasurable f))

/-- **Convolution with an integrable kernel as a bounded operator on `L_p`**, `1 ≤ p < ∞`, of
norm at most `‖K‖_1` (Young's inequality). -/
noncomputable def convLp (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) :
    Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_conv Fact.out hK (Lp.memLp f)).toLp (conv K f μ)
      map_add' := fun f g => by
        refine Lp.ext ?_
        have hc : conv K (⇑(f + g)) μ = conv K (⇑f + ⇑g) μ := conv_congr_ae (Lp.coeFn_add f g)
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp (f + g))),
          MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp g)),
          Lp.coeFn_add ((memLp_conv Fact.out hK (Lp.memLp f)).toLp (conv K f μ))
            ((memLp_conv Fact.out hK (Lp.memLp g)).toLp (conv K g μ)),
          conv_add_ae Fact.out hp hK (Lp.memLp f) (Lp.memLp g)] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, hc, h5, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have hc : conv K (⇑(c • f)) μ = conv K (c • ⇑f) μ := conv_congr_ae (Lp.coeFn_smul c f)
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp (c • f))),
          MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp f)),
          Lp.coeFn_smul c ((memLp_conv Fact.out hK (Lp.memLp f)).toLp (conv K f μ))]
          with x h1 h2 h3
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, hc, conv_smul, Pi.smul_apply] }
    (eLpNorm K 1 μ).toReal (norm_toLp_conv_le hK)

/-- The operator `convLp` is convolution, almost everywhere. -/
theorem convLp_apply_ae (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    convLp hp hK f =ᵐ[μ] conv K f μ :=
  MemLp.coeFn_toLp (memLp_conv Fact.out hK (Lp.memLp f))

/-- **Young's inequality on `L_p`**: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`. -/
theorem norm_convLp_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖convLp hp hK f‖ ≤ (eLpNorm K 1 μ).toReal * ‖f‖ :=
  norm_toLp_conv_le hK f

/-- **Young's inequality on `L_p`** in extended norms: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`. -/
theorem enorm_convLp_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖convLp hp hK f‖ₑ ≤ eLpNorm K 1 μ * ‖f‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (convLp_apply_ae hp hK f)]
  exact eLpNorm_conv_le Fact.out hK.aestronglyMeasurable (Lp.aestronglyMeasurable f)

/-- **Convolution operators compose like their kernels**: `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f` in `L_p`
(`Rd.conv_conv_ae`). -/
theorem convLp_convLp (hp : p ≠ ∞) {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ)
    (f : Lp ℂ p μ) : convLp hp hK (convLp hp hL f) = convLp hp (integrable_conv hK hL) f := by
  refine Lp.ext ?_
  have h1 : conv K (⇑(convLp hp hL f)) μ = conv K (conv L f μ) μ :=
    conv_congr_ae (convLp_apply_ae hp hL f)
  filter_upwards [convLp_apply_ae hp hK (convLp hp hL f),
    convLp_apply_ae hp (integrable_conv hK hL) f, conv_conv_ae Fact.out hp hK hL (Lp.memLp f)]
    with x hx1 hx2 hx3
  rw [hx1, h1, hx2, hx3]

/-- If `K ⋆ L = M`, then `K ⋆ (L ⋆ f) = M ⋆ f` in `L_p`. -/
theorem convLp_convLp_of_eq (hp : p ≠ ∞) {K L M : V → ℂ} (hK : Integrable K μ)
    (hL : Integrable L μ) (hM : Integrable M μ) (h : conv K L μ = M) (f : Lp ℂ p μ) :
    convLp hp hK (convLp hp hL f) = convLp hp hM f := by
  rw [convLp_convLp hp hK hL]
  subst h
  rfl

/-- Convolution with the zero kernel is zero. -/
theorem convLp_of_eq_zero (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (h : K = 0)
    (f : Lp ℂ p μ) : convLp hp hK f = 0 := by
  subst h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [convLp_apply_ae hp hK f] with x hx
  rw [hx, conv_apply]
  simp

/-- **Convolution operators commute**: `K ⋆ (L ⋆ f) = L ⋆ (K ⋆ f)` in `L_p`. -/
theorem convLp_comm (hp : p ≠ ∞) {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ)
    (f : Lp ℂ p μ) : convLp hp hK (convLp hp hL f) = convLp hp hL (convLp hp hK f) := by
  rw [convLp_convLp_of_eq hp hK hL (integrable_conv hL hK) (conv_comm K L), convLp_convLp]

/-- **Convolution operators are additive in the kernel**: `(K + K') ⋆ f = K ⋆ f + K' ⋆ f` in
`L_p`. -/
theorem convLp_add_kernel (hp : p ≠ ∞) {K K' : V → ℂ} (hK : Integrable K μ)
    (hK' : Integrable K' μ) (f : Lp ℂ p μ) :
    convLp hp (hK.add hK') f = convLp hp hK f + convLp hp hK' f := by
  refine Lp.ext ?_
  filter_upwards [convLp_apply_ae hp (hK.add hK') f, convLp_apply_ae hp hK f,
    convLp_apply_ae hp hK' f, Lp.coeFn_add (convLp hp hK f) (convLp hp hK' f),
    add_conv_ae Fact.out hp hK hK' (Lp.memLp f)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]

/-- **Convolution operators are subtractive in the kernel**: `(K - K') ⋆ f = K ⋆ f - K' ⋆ f`
in `L_p`. -/
theorem convLp_sub_kernel (hp : p ≠ ∞) {K K' : V → ℂ} (hK : Integrable K μ)
    (hK' : Integrable K' μ) (f : Lp ℂ p μ) :
    convLp hp (hK.sub hK') f = convLp hp hK f - convLp hp hK' f := by
  refine Lp.ext ?_
  filter_upwards [convLp_apply_ae hp (hK.sub hK') f, convLp_apply_ae hp hK f,
    convLp_apply_ae hp hK' f, Lp.coeFn_sub (convLp hp hK f) (convLp hp hK' f),
    sub_conv_ae Fact.out hp hK hK' (Lp.memLp f)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3, h5, Pi.sub_apply]

end Rd

/-! ### Pointwise bounds with Lebesgue measure -/

namespace Rd

open Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `0 ≤ 1 - 1/p` for `p ≥ 1`. -/
theorem one_sub_one_div_toReal_nonneg {p : ℝ≥0∞} (hp1 : 1 ≤ p) : 0 ≤ 1 - 1 / p.toReal := by
  rcases eq_or_ne p ∞ with hpt | hpt
  · simp [hpt]
  · have : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hpt
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this

/-- **Hölder's inequality on a ball**: `∫_{closedBall(x,ρ)} |g| ≤ |closedBall(x,ρ)|^(1-1/p)
‖g‖_p`. -/
theorem lintegral_closedBall_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) (x : V) (ρ : ℝ) :
    ∫⁻ z in closedBall x ρ, ‖g z‖ₑ ≤
      volume (closedBall x ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume := by
  have hgr : AEStronglyMeasurable g (volume.restrict (closedBall x ρ)) := hg.restrict
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hgr
  rw [eLpNorm_one_eq_lintegral_eNorm hgr, Measure.restrict_apply_univ, ENNReal.toReal_one,
    div_one] at h
  refine h.trans ?_
  rw [mul_comm]
  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- `∫ |K(y)| |g(x - y)| dy ≤ A |closedBall(0,ρ)|^(1-1/p) ‖g‖_p` if `|K| ≤ A` and `K = 0` outside
`closedBall(0, ρ)`. -/
theorem lintegral_kernel_mul_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) {A : ℝ≥0∞} (hK : ∀ y, ‖K y‖ₑ ≤ A) {ρ : ℝ}
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) (x : V) :
    ∫⁻ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤
      A * volume (closedBall (0 : V) ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume := by
  set G : V → ℝ≥0∞ := (closedBall x ρ).indicator fun z => ‖g z‖ₑ
  have h1 : ∀ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤ A * G (x - y) := fun y => by
    by_cases hy : ‖y‖ ≤ ρ
    · have hmem : x - y ∈ closedBall x ρ := by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hy
      simp only [G, Set.indicator_of_mem hmem]
      exact mul_le_mul' (hK y) le_rfl
    · rw [hKρ y (not_le.1 hy), eNorm_zero, zero_mul]
      exact zero_le
  calc ∫⁻ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤ ∫⁻ y, A * G (x - y) := lintegral_mono h1
    _ = ∫⁻ z, A * G z := lintegral_sub_left_eq_self (fun z => A * G z) x
    _ = A * ∫⁻ z in closedBall x ρ, ‖g z‖ₑ := by
        rw [lintegral_const_mul'' A (hg.eNorm.indicator measurableSet_closedBall),
          lintegral_indicator measurableSet_closedBall]
    _ ≤ A * (volume (closedBall x ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume) :=
        mul_le_mul' le_rfl (lintegral_closedBall_le hp1 hg x ρ)
    _ = _ := by rw [Measure.addHaar_closedBall_center, mul_assoc]

/-- **Pointwise bound of a convolution**: if `|K| ≤ A` and `K = 0` outside `closedBall(0, ρ)`, then
`|(K ⋆ g)(x)| ≤ A |closedBall(0,ρ)|^(1-1/p) ‖g‖_p`, by Hölder's inequality on the ball
`closedBall(x, ρ)`. -/
theorem enorm_conv_le_of_bound {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) {A : ℝ≥0∞} (hK : ∀ y, ‖K y‖ₑ ≤ A) {ρ : ℝ}
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) (x : V) :
    ‖conv K g volume x‖ₑ ≤
      A * volume (closedBall (0 : V) ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume :=
  (enorm_conv_le_lintegral K g x).trans (lintegral_kernel_mul_le hp1 hg hK hKρ x)

/-- The convolution integrals of a continuous kernel with compact support and a locally integrable
function converge absolutely. -/
theorem integrable_translate_mul_of_locallyIntegrable {K g : V → ℂ} (hKc : Continuous K)
    (hKs : HasCompactSupport K) (hg : LocallyIntegrable g volume) (v x : V) :
    Integrable (fun y => K (y + v) * g (x - y)) volume := by
  have hc : HasCompactSupport fun y => K (y + v) :=
    hKs.comp_homeomorph (Homeomorph.addRight v)
  exact (hc.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    (hKc.comp (continuous_id.add continuous_const)) hg) x

/-- `(K ⋆ g)(x + v) = ∫ K(y + v) g(x - y) dy`, by translation invariance. -/
theorem conv_add_apply (K g : V → ℂ) (x v : V) :
    conv K g volume (x + v) = ∫ y, K (y + v) * g (x - y) := by
  rw [conv_apply, ← integral_add_right_eq_self (fun y => K y * g (x + v - y)) v]
  congr 1
  funext y
  congr 2
  abel

end Rd
