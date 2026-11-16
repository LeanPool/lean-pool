/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Mollification against a Haar measure

Convolution with a normalised smooth bump `ρ = φ.normed m`, `φ : ContDiffBump (0 : V)`, on a
finite-dimensional real inner product space `V` with a Haar measure `m`. Mathlib provides the
smoothness of the mollification, its pointwise convergence at points of continuity and the
derivative of a convolution; this module adds the four facts that an `L²`-based regularity
argument needs and that Mathlib does not state:

* `eLpNorm_convolution_le`: the mollifier is an **`L²` contraction**, `‖ρ ⋆ f‖₂ ≤ ‖f‖₂`, for a
  vector-valued `f`, through the pointwise Cauchy–Schwarz bound
  `‖(ρ ⋆ f) x‖² ≤ ∫ ρ(t) ‖f (x - t)‖² dt` and Tonelli (`memLp_convolution` records that
  `ρ ⋆ f ∈ L²`).
* `tendsto_eLpNorm_convolution_sub`: **`L²` convergence** `ρₙ ⋆ f → f` for every `f ∈ L²(m)`
  as the radii of the bumps tend to zero, from the continuous compactly supported case
  (`tendsto_eLpNorm_convolution_sub_of_continuous`, uniform continuity) and the density of that
  class in `L²`, using the contraction.
* `integral_inner_convolution_eq`: the **symmetry identity** `∫ ⟪ρ ⋆ a, b⟫ = ∫ ⟪a, ρ ⋆ b⟫` for
  an integrable `a` and a continuous compactly supported `b`, by Fubini and the evenness of the
  bump; it is what moves the mollifier from an `L²` class onto a test function.
* `gradient_convolution` and `laplacian_convolution`: on smooth compactly supported `g`,
  `∇(ρ ⋆ g) = ρ ⋆ ∇g` and `Δ(ρ ⋆ g) = ρ ⋆ Δg`, from Mathlib's derivative of a convolution
  applied twice, directionally.

Nothing here involves a probability law, a weighted operator or a semigroup; the consumer is the
interior-regularity argument of `KLS/LogConcave/HeatSemigroup/Generator/InteriorRegularity.lean`.
-/

@[expose] public section

section

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Mollification

open FunctionalInequalities.Analysis.BakryEmery

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]

section Contraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (φ : ContDiffBump (0 : V))

/-- Pointwise Cauchy–Schwarz for the mollifier: `‖(ρ ⋆ f) x‖² ≤ ∫ ρ(t) ‖f (x - t)‖² dt`. -/
theorem enorm_convolution_sq_le {f : V → E} (hf : AEStronglyMeasurable f m) (x : V) :
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m := by
  set a : V → ℝ≥0∞ := fun t => ENNReal.ofReal (φ.normed m t) with ha_def
  set b : V → ℝ≥0∞ := fun t => ‖f (x - t)‖ₑ with hb_def
  have ha : Measurable a := ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hb : AEMeasurable b m :=
    hf.enorm.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left m x).quasiMeasurePreserving
  have h1 : ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ≤ ∫⁻ t, a t * b t ∂m := by
    rw [convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp only [ContinuousLinearMap.lsmul_apply, enorm_smul,
      Real.enorm_of_nonneg (φ.nonneg_normed t), ha_def, hb_def]
  have hint : ∫⁻ t, a t ∂m = 1 := by
    rw [ha_def, ←
      ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (Filter.Eventually.of_forall φ.nonneg_normed),
      φ.integral_normed, ENNReal.ofReal_one]
  have hH :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two (f := fun t =>
      a t ^ (1 / 2 : ℝ)) (g := fun t => a t ^ (1 / 2 : ℝ) * b t) (ha.pow_const _).aemeasurable
      ((ha.pow_const _).aemeasurable.mul hb)
  have e1 : ∀ t, (a t ^ (1 / 2 : ℝ)) * (a t ^ (1 / 2 : ℝ) * b t) = a t * b t := by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ t, (a t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a t := by
    intro t
    rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ t, (a t ^ (1 / 2 : ℝ) * b t) ^ (2 : ℝ) = a t * b t ^ 2 := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3, hint, ENNReal.one_rpow, one_mul] at hH
  have h2 :
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ≤
      (∫⁻ t, a t * b t ^ 2 ∂m) ^ (1 / (2 : ℝ)) :=
    h1.trans hH
  calc
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
        ((∫⁻ t, a t * b t ^ 2 ∂m) ^ (1 / (2 : ℝ))) ^ 2 :=
      pow_le_pow_left' h2 2
    _ = ∫⁻ t, a t * b t ^ 2 ∂m := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- The mollifier is an `L²` contraction: `∫ ‖ρ ⋆ f‖² ≤ ∫ ‖f‖²`. -/
theorem lintegral_enorm_convolution_sq_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by
  have ha : Measurable fun t => ENNReal.ofReal (φ.normed m t) :=
    ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hmeas : AEMeasurable (fun p : V × V => ENNReal.ofReal (φ.normed m p.2) *
      ‖f (p.1 - p.2)‖ₑ ^ 2) (m.prod m) := by
    refine (ha.comp measurable_snd).aemeasurable.mul ?_
    exact (hf.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant m m)).pow_const _
  have hint : ∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  calc ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_mono fun x => enorm_convolution_sq_le φ hf x
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m ∂m := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ 2) t]
    _ = (∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m :=
        lintegral_mul_const _ ha
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by rw [hint, one_mul]

/-- `L²` contraction of the mollifier in `eLpNorm` form. -/
theorem eLpNorm_convolution_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m := by
  have hconv : AEStronglyMeasurable (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) m :=
    φ.continuous_normed.aestronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hconv,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_convolution_sq_le φ hf) (by norm_num)

/-- The mollification of a locally integrable function is continuous. -/
theorem continuous_convolution {f : V → E} (hf : LocallyIntegrable f m) :
    Continuous (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) :=
  HasCompactSupport.continuous_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
    φ.continuous_normed hf

/-- The mollification of an `L²` function is again `L²`. -/
theorem memLp_convolution {f : V → E} (hf : MemLp f 2 m) :
    MemLp (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m :=
  (eLpNorm_convolution_le φ hf.aestronglyMeasurable).trans_lt hf.eLpNorm_lt_top

/-- The mollifier is linear on locally integrable functions. -/
theorem convolution_sub {f g : V → E} (hf : LocallyIntegrable f m) (hg : LocallyIntegrable g m) :
    φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g) =
      φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f -
        φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g := by
  funext x
  have h1 := HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed hf x
  have h2 := HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed hg x
  simp only [Pi.sub_apply, convolution_def, ContinuousLinearMap.lsmul_apply, smul_sub]
  exact integral_sub h1 h2

end Contraction

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section ConvolutionSupport

omit [CompleteSpace E]
/-- The support of a mollification with `rOut ≤ ε` lies in the closed `ε`-thickening of the
support of the function. -/
theorem support_convolution_subset_cthickening_of_rOut_le (φ : ContDiffBump (0 : V)) {ε : ℝ}
    (hφ : φ.rOut ≤ ε) (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening ε (tsupport f) := by
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  rw [φ.support_normed_eq] at ha
  refine mem_cthickening_of_dist_le (a + b) b ε _ (subset_tsupport _ hb) ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  rw [mem_ball, dist_zero_right] at ha
  exact ha.le.trans hφ

/-- The support of a mollification with `rOut ≤ 1` lies in the closed `1`-thickening of the
support of the function. -/
theorem support_convolution_subset_cthickening (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1)
    (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening 1 (tsupport f) :=
  support_convolution_subset_cthickening_of_rOut_le φ hφ f

end ConvolutionSupport

/-- **Mollifications of a continuous compactly supported function converge in `L²`** as the
radius of the bump tends to zero. -/
theorem tendsto_eLpNorm_convolution_sub_of_continuous {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by
  set K : Set V := cthickening 1 (tsupport f) with hK
  have hKc : IsCompact K := hfc.cthickening
  have hKfin : m K ≠ ⊤ := hKc.measure_lt_top.ne
  set c : ℝ≥0∞ := m K ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
  have hcfin : c ≠ ⊤ := by
    rw [hc]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKfin
  have hunif : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  have hev1 : ∀ᶠ n in atTop, (φ n).rOut ≤ 1 :=
    hφ.eventually (ge_mem_nhds zero_lt_one)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- a real bound `δ > 0` with `c * ofReal δ ≤ ε`
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ c * ENNReal.ofReal δ ≤ ε := by
    by_cases hc0 : c = 0
    · exact ⟨1, one_pos, by rw [hc0, zero_mul]; exact bot_le⟩
    by_cases hεtop : ε = ⊤
    · exact ⟨1, one_pos, by rw [hεtop]; exact le_top⟩
    have hdiv : ε / c ≠ ⊤ := ENNReal.div_ne_top hεtop hc0
    refine ⟨(ε / c).toReal, ENNReal.toReal_pos (ENNReal.div_pos hε.ne' hcfin).ne' hdiv, ?_⟩
    rw [ENNReal.ofReal_toReal hdiv, ENNReal.mul_div_cancel hc0 hcfin]
  obtain ⟨η, hη, hηδ⟩ := Metric.uniformContinuous_iff.mp hunif δ hδ
  have hev2 : ∀ᶠ n in atTop, (φ n).rOut < η := hφ.eventually (gt_mem_nhds hη)
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hbound : ∀ x, ‖((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) x‖ ≤ δ := by
    intro x
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine ContDiffBump.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy => ?_
    rw [mem_ball] at hy
    exact (hηδ (lt_of_lt_of_le hy hn2.le)).le
  have hsupp : Function.support ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) ⊆ K := by
    refine (Function.support_sub _ _).trans (Set.union_subset ?_ ?_)
    · exact support_convolution_subset_cthickening (φ n) hn1 f
    · exact (subset_tsupport f).trans (self_subset_cthickening _)
  have hmeas : AEStronglyMeasurable
      ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) m :=
    ((φ n).continuous_normed.aestronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable).sub hf.aestronglyMeasurable
  calc eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m
      = eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 (m.restrict K) :=
        (eLpNorm_restrict_eq_of_support_subset hmeas hsupp).symm
    _ ≤ (m.restrict K) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal δ :=
        eLpNorm_le_of_ae_bound hmeas.restrict (Filter.Eventually.of_forall hbound)
    _ = c * ENNReal.ofReal δ := by rw [Measure.restrict_apply_univ]
    _ ≤ ε := hδε

/-- **Mollifications of an `L²` function converge in `L²`** as the radius of the bump tends to
zero: the contraction property reduces the statement to the continuous compactly supported case,
which is dense. -/
theorem tendsto_eLpNorm_convolution_sub {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : MemLp f 2 m) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨g, hgc, hfg, hg, hgL⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hε3
  have hloc_f : LocallyIntegrable f m := hf.locallyIntegrable one_le_two
  have hloc_g : LocallyIntegrable g m := hgL.locallyIntegrable one_le_two
  have hg3 := (tendsto_eLpNorm_convolution_sub_of_continuous (m := m) hφ hg hgc).eventually
    (ge_mem_nhds (pos_iff_ne_zero.mpr hε3))
  filter_upwards [hg3] with n hn
  have hsplit : (φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f =
      ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g) +
        ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g - g)) + (g - f) := by
    rw [convolution_sub (φ n) hloc_f hloc_g]
    abel
  calc eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m
      ≤ eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g)) 2 m +
          eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g - g) 2 m +
          eLpNorm (g - f) 2 m := by
        rw [hsplit]
        exact (eLpNorm_add_le one_le_two).trans
          (add_le_add_left (eLpNorm_add_le one_le_two) _)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (eLpNorm_convolution_le (φ n)
            (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)).trans hfg
        · rw [eLpNorm_sub_comm]; exact hfg
    _ = ε := ENNReal.add_thirds ε

end Convergence

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (φ : ContDiffBump (0 : V))

/-- **The mollifier is symmetric for the `L²` pairing**: for an integrable `a` and a continuous
compactly supported `b`, `∫ ⟪ρ ⋆ a, b⟫ = ∫ ⟪a, ρ ⋆ b⟫`. The bump is even, so no reflection of the
kernel appears. -/
theorem integral_inner_convolution_eq {a b : V → E} (ha : Integrable a m) (hb : Continuous b)
    (hbc : HasCompactSupport b) :
    ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
      ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m := by
  obtain ⟨C, hC⟩ := hb.bounded_above_of_compact_support hbc
  have hρi : Integrable (φ.normed m) m := φ.integrable_normed
  have hρm : Measurable (φ.normed m) :=
    φ.continuous_normed.measurable
  -- the two product integrands
  have hI₁ : Integrable (fun p : V × V => φ.normed m p.2 * ⟪a (p.1 - p.2), b p.1⟫) (m.prod m) := by
    have h0 := hρi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) ha
    refine (h0.norm.mul_const C).mono' ?_ ?_
    · refine ((hρm.comp measurable_snd).aestronglyMeasurable.mul ?_)
      refine (AEStronglyMeasurable.inner ?_ (hb.comp continuous_fst).aestronglyMeasurable)
      exact ha.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant m m)
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (φ.nonneg_normed _), norm_mul]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed _)
      exact
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  have hI₂ : Integrable (fun p : V × V => φ.normed m p.1 * ⟪a p.2, b (p.2 + p.1)⟫) (m.prod m) := by
    have h0 := hρi.mul_prod ha.norm
    refine (h0.mul_const C).mono' ?_ ?_
    · refine ((hρm.comp measurable_fst).aestronglyMeasurable.mul ?_)
      refine (AEStronglyMeasurable.inner ?_ ?_)
      · exact ha.1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)
      · exact (hb.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed _)
      exact
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  -- left side: pull the pairing inside, swap, translate
  have hL :
    ∀ x,
      ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ =
        ∫ t, φ.normed m t * ⟪a (x - t), b x⟫ ∂m := by
    intro x
    have hint :
      Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t)) (a (x - t))) m :=
      HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed ha.locallyIntegrable x
    rw [convolution_def, real_inner_comm, ← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_right, real_inner_comm]
  have hR :
    ∀ y,
      ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ =
        ∫ t, φ.normed m t * ⟪a y, b (y + t)⟫ ∂m := by
    intro y
    have hint : Integrable (fun t => φ.normed m t • b (y + t)) m := by
      refine
        hρi.smul_of_top_left
          (memLp_top_of_bound ?_ C (Filter.Eventually.of_forall fun t => hC _))
      exact (hb.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    rw [convolution_def, ←
      integral_neg_eq_self (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t)) (b (y - t)))
        m]
    simp only [ContinuousLinearMap.lsmul_apply, φ.normed_neg, sub_neg_eq_add]
    rw [← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [real_inner_smul_right]
  simp only [hL, hR]
  rw [integral_integral_swap hI₁]
  have hmid :
    ∀ t, ∫ x, φ.normed m t * ⟪a (x - t), b x⟫ ∂m = ∫ y, φ.normed m t * ⟪a y, b (y + t)⟫ ∂m := by
    intro t
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have := integral_sub_right_eq_self (μ := m) (fun y => ⟪a y, b (y + t)⟫) t
    simp only [sub_add_cancel] at this
    exact this
  simp only [hmid]
  exact integral_integral_swap hI₂

end Adjoint

section Derivative

variable (φ : ContDiffBump (0 : V))

/-- The mollifier commutes with the gradient on smooth compactly supported functions:
`∇(ρ ⋆ g) = ρ ⋆ ∇g`. -/
theorem gradient_convolution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x := by
  have hρ : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  have hd :=
    HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hgc hρ
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)) x
  have hg1 : Continuous (fderiv ℝ g) :=
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_fderiv one_ne_zero
  refine ext_inner_right ℝ fun v => ?_
  have hint :
    Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t)) (gradient g (x - t)))
      m :=
    HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed
      ((continuous_gradient (hg.of_le (WithTop.coe_le_coe.mpr le_top))).locallyIntegrable) x
  have hL :
    ⟪gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x, v⟫ =
      ∫ t, φ.normed m t * fderiv ℝ g (x - t) v ∂m := by
    rw [gradient, toDual_symm_apply, hd.fderiv,
      convolution_precompR_apply _ hρ (hgc.fderiv ℝ) hg1, convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hR :
    ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x, v⟫ =
      ∫ t, φ.normed m t * fderiv ℝ g (x - t) v ∂m := by
    rw [convolution_def, real_inner_comm, ← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_right]
    rw [real_inner_comm _ v, inner_gradient_left]
  rw [hL, hR]

/-- The mollifier commutes with the Laplacian on smooth compactly supported functions:
`Δ(ρ ⋆ g) = ρ ⋆ Δg`. -/
theorem laplacian_convolution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x := by
  have hρ : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgD : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
  have hgc1 : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  have hconv : ContDiff ℝ ∞ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) :=
    HasCompactSupport.contDiff_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
      φ.contDiff_normed (hg1.continuous.locallyIntegrable)
  have hdiffx :
    DifferentiableAt ℝ (fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g)) x :=
    (hconv.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable one_ne_zero
      x
  -- the directional derivative of the mollification is the mollification of the directional
  -- derivative
  have hdir :
    ∀ v,
      (fun y => fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) y v) =
        φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun a => fderiv ℝ g a v := by
    intro v
    funext y
    rw [(HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hgc hρ
          hg1 y).fderiv,
      convolution_precompR_apply _ hρ hgc1 hgD.continuous]
  -- the second derivative
  have hsecond :
    ∀ v w,
      fderiv ℝ (fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g)) x v w =
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun a => fderiv ℝ (fderiv ℝ g) a v w)
          x := by
    intro v w
    rw [← fderiv_fderiv_apply hdiffx v w, hdir w]
    have hw1 : ContDiff ℝ 1 fun a => fderiv ℝ g a w := hgD.clm_apply contDiff_const
    have hwc : HasCompactSupport fun a => fderiv ℝ g a w := hgc.fderiv_apply ℝ w
    rw [(HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hwc hρ
          hw1 x).fderiv,
      convolution_precompR_apply _ hρ (hwc.fderiv ℝ) (hw1.continuous_fderiv one_ne_zero)]
    simp only [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [fderiv_fderiv_apply (hgD.differentiable one_ne_zero _) v w]
  have hg2c : Continuous (fderiv ℝ (fderiv ℝ g)) := hgD.continuous_fderiv one_ne_zero
  have hint :
    ∀ i,
      Integrable
        (fun t =>
          (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t))
            (fderiv ℝ (fderiv ℝ g) (x - t) (stdOrthonormalBasis ℝ V i)
              (stdOrthonormalBasis ℝ V i)))
        m :=
    fun i =>
    HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed
      (((hg2c.clm_apply continuous_const).clm_apply continuous_const).locallyIntegrable) x
  rw [laplacian_eq_sum_fderiv_fderiv]
  simp only [hsecond, convolution_def]
  rw [← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, laplacian_eq_sum_fderiv_fderiv,
    Finset.mul_sum]

end Derivative

end FunctionalInequalities.Analysis.Mollification

namespace FunctionalInequalities.Analysis

section LipschitzConvolution

open MeasureTheory
open scoped Convolution

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-! Derivative of a normalized-bump convolution with a Lipschitz function. -/

private theorem integral_fderiv_kernel_eq
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
    (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
    (x v : E) (ℓ : E →L[ℝ] ℝ) :
    (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
      ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
  let g : E → ℝ := fun y => k (x - y)
  have hgc : HasCompactSupport g :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hgd : ContDiff ℝ 1 g :=
    hk.comp (contDiff_const.sub contDiff_id)
  obtain ⟨D, hg⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hgc hgd (by decide)
  have hdg (y : E) :
      lineDeriv ℝ g y (-v) = fderiv ℝ k (x - y) v := by
    change lineDeriv ℝ (k ∘ (fun z : E => x - z)) y (-v) = _
    simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, neg_neg] using
      ((((hk.differentiable (by decide)) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).const_sub x)).hasLineDerivAt (-v)).lineDeriv
  have hdF :
      ∀ᵐ y ∂(volume : Measure E),
        lineDeriv ℝ (ℓ ∘ F) y v = ℓ (fderiv ℝ F y v) := by
    filter_upwards [hF.ae_differentiableAt (μ := (volume : Measure E))] with y hy
    exact ((ℓ.hasFDerivAt.comp y hy.hasFDerivAt).hasLineDerivAt v).lineDeriv
  have hb :=
    (ℓ.lipschitzWith.comp hF).integral_lineDeriv_mul_eq
      (μ := (volume : Measure E)) hg hgc v
  have he :
      (∫ y, lineDeriv ℝ (ℓ ∘ F) y v * g y) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    apply integral_congr_ae
    filter_upwards [hdF] with y hy
    rw [hy]
    exact mul_comm _ _
  rw [he] at hb
  have hb' :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    simpa only [hdg, Function.comp_apply] using hb.symm
  have ha :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ t, fderiv ℝ k t v * ℓ (F (x - t)) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => fderiv ℝ k t v * ℓ (F (x - t)))
        (volume : Measure E) x
  have hz :
      (∫ y, k (x - y) * ℓ (fderiv ℝ F y v)) =
        ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => k t * ℓ (fderiv ℝ F (x - t) v))
        (volume : Measure E) x
  exact ha.symm.trans (hb'.trans hz)

/-- **Derivative of the mollification of a Lipschitz map** (support for the
mollification identities): for a Lipschitz map `F : E → E` and a bump `φ`, the convolution
`φ.normed ⋆ F` is differentiable with derivative `φ.normed ⋆ DF`, where `DF = fderiv ℝ F` is the
almost-everywhere (Rademacher) derivative of `F` (a bounded measurable map). -/
theorem hasFDerivAt_convolution_normed_of_lipschitz {F : E → E} {G : NNReal}
    (hF : LipschitzWith G F) (φ : ContDiffBump (0 : E)) (x : E) :
    HasFDerivAt
      (φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] F)
      ((φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
          fderiv ℝ F)
        x)
      x := by
  let k := φ.normed (volume : Measure E)
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  let P := ContinuousLinearMap.precompL E L
  have hk : ContDiff ℝ 1 k := φ.contDiff_normed
  have hc : HasCompactSupport k := φ.hasCompactSupport_normed
  have hDF : LocallyIntegrable (fderiv ℝ F) (volume : Measure E) :=
    (memLp_top_of_bound (measurable_fderiv ℝ F).aestronglyMeasurable (G : ℝ)
          (Filter.Eventually.of_forall
            (fun _ => norm_fderiv_le_of_lipschitz ℝ hF))).locallyIntegrable
      le_top
  have hFloc : LocallyIntegrable F (volume : Measure E) := hF.continuous.locallyIntegrable
  have hi := (hc.fderiv ℝ).convolutionExists_left P (hk.continuous_fderiv (by decide)) hFloc x
  have hj :=
    hc.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) hk.continuous hDF
      x
  change Integrable (fun t => k t • fderiv ℝ F (x - t)) (volume : Measure E) at hj
  apply (hc.hasFDerivAt_convolution_left L hk hFloc x).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  let ℓ : E →L[ℝ] ℝ := innerSL ℝ w
  let Q : (E →L[ℝ] E) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.apply ℝ E v)
  change Q (∫ t, P (fderiv ℝ k t) (F (x - t))) = Q (∫ t, k t • fderiv ℝ F (x - t))
  rw [← Q.integral_comp_comm hi, ← Q.integral_comp_comm hj]
  simpa only [Q, P, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, map_smul,
    smul_eq_mul] using integral_fderiv_kernel_eq hF k hk hc x v ℓ

end FiniteDimensional

end LipschitzConvolution

end FunctionalInequalities.Analysis


/-! Weak-route support for Letwin arXiv:2607.24164v1. -/

section ConvexRangeMollification

open MeasureTheory Set Filter Metric
open scoped Topology Convolution

namespace FunctionalInequalities.Analysis

/-- **Mollified values stay in a closed convex set**: if the vector of values
`(f k x)ₖ` lies in a closed convex `C` for almost every `x` in `cthickening r S`, then for every
bump `φ` with
`φ.rOut ≤ r` and every `x ∈ S`, the mollified vector `((φ.normed ⋆ f k) x)ₖ` lies in `C`. -/
theorem convolution_mem_of_ae_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Finite ι]
    {f : ι → E → ℝ} (hf : ∀ k, LocallyIntegrable (f k) (volume : Measure E)) {C : Set (ι → ℝ)}
    (hCc : Convex ℝ C) (hCcl : IsClosed C) {S : Set E} {r : ℝ}
    (hfC : ∀ᵐ x ∂((volume : Measure E).restrict (cthickening r S)), (fun k => f k x) ∈ C)
    (φ : ContDiffBump (0 : E)) (hφ : φ.rOut ≤ r) {x : E} (hx : x ∈ S) :
    (fun k => convolution (φ.normed volume) (f k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) ∈
      C := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let ρ : E → ℝ := fun y => φ.normed volume (x - y)
  let P : Measure E := volume.withDensity (fun y => ENNReal.ofReal (ρ y))
  have hρ_cont : Continuous ρ := by
    exact φ.continuous_normed.comp (continuous_const.sub continuous_id)
  have hρ_meas : Measurable ρ := hρ_cont.measurable
  have hρ_nn : ∀ y, 0 ≤ ρ y := by
    intro y
    exact φ.nonneg_normed _
  have hρ_comp : HasCompactSupport ρ := by
    exact φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have hρ_integrable : Integrable ρ (volume : Measure E) :=
    hρ_cont.integrable_of_hasCompactSupport hρ_comp
  have hρ_int : ∫ y, ρ y ∂(volume : Measure E) = 1 := by
    have hsub :
      ∫ y, φ.normed volume (x - y) ∂(volume : Measure E) =
        ∫ y, φ.normed volume y ∂(volume : Measure E) := by
      exact
        (Measure.measurePreserving_sub_left (volume : Measure E) x).integral_comp
          (Homeomorph.subLeft x).measurableEmbedding (φ.normed volume)
    rw [hsub]
    exact φ.integral_normed
  have hP_prob : IsProbabilityMeasure P := by
    apply IsProbabilityMeasure.mk
    change (volume.withDensity (fun y => ENNReal.ofReal (ρ y))) univ = 1
    rw [MeasureTheory.withDensity_apply (fun y => ENNReal.ofReal (ρ y)) MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_integrable (ae_of_all _ hρ_nn)]
    simpa using congrArg ENNReal.ofReal hρ_int
  let _ : IsProbabilityMeasure P := hP_prob
  have hρ_support : Function.support ρ ⊆ closedBall x φ.rOut := by
    intro y hy
    change φ.normed volume (x - y) ≠ 0 at hy
    have hyball : x - y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq] at hyball
    rw [Metric.mem_ball] at hyball
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    simpa [dist_eq_norm] using le_of_lt hyball
  have hball_cthick : closedBall x φ.rOut ⊆ cthickening r S := by
    intro y hy
    change infEDist y S ≤ ENNReal.ofReal r
    have hdist : dist y x ≤ φ.rOut := by exact Metric.mem_closedBall.mp hy
    calc
      infEDist y S ≤ edist y x := Metric.infEDist_le_edist_of_mem hx
      _ = ENNReal.ofReal (dist y x) := by rw [edist_dist]
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (hdist.trans hφ)
  have hT : MeasurableSet (cthickening r S) := Metric.isClosed_cthickening.measurableSet
  have hfC' : ∀ᵐ y ∂(volume : Measure E), y ∈ cthickening r S → (fun k => f k y) ∈ C := by
    exact (ae_restrict_iff' hT).mp hfC
  have hae_mem : ∀ᵐ y ∂P, (fun k => f k y) ∈ C := by
    rw [ae_withDensity_iff hρ_meas.ennreal_ofReal]
    filter_upwards [hfC'] with y hyT hyρ
    exact
      hyT
        (hball_cthick
          (hρ_support
            (by
              intro hzero
              apply hyρ
              simp [hzero])))
  have hfi (k : ι) : Integrable (f k) P := by
    rw [integrable_withDensity_iff hρ_meas.ennreal_ofReal
        (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    have hi := (hf k).integrable_smul_left_of_hasCompactSupport hρ_cont hρ_comp
    have hfun : (fun y => f k y * (ENNReal.ofReal (ρ y)).toReal) = (fun y => ρ y • f k y) := by
      funext y
      rw [ENNReal.toReal_ofReal (hρ_nn y)]
      simp [smul_eq_mul, mul_comm]
    rw [hfun]
    exact hi
  have hvec_int : Integrable (fun y => fun k => f k y) P := by
    rw [integrable_pi_iff]
    intro k
    exact hfi k
  have havg : (∫ y, (fun k => f k y) ∂P) ∈ C := hCc.integral_mem hCcl hae_mem hvec_int
  have hcoord (k : ι) :
    (∫ y, (fun j => f j y) ∂P) k =
      convolution (φ.normed volume) (f k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    have hproj : (∫ y, (fun j => f j y) ∂P) k = ∫ y, f k y ∂P := by
      let L : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
      simpa [L] using (L.integral_comp_comm hvec_int).symm
    calc
      (∫ y, (fun j => f j y) ∂P) k = ∫ y, f k y ∂P := hproj
      _ = ∫ y, f k y * ρ y ∂(volume : Measure E) := by
        change
          (∫ y, f k y ∂(volume.withDensity (fun y => ENNReal.ofReal (ρ y)))) =
            ∫ y, f k y * ρ y ∂(volume : Measure E)
        rw [integral_withDensity_eq_integral_toReal_smul hρ_meas.ennreal_ofReal
            (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [] with y
        rw [ENNReal.toReal_ofReal (hρ_nn y)]
        simp [smul_eq_mul, mul_comm]
      _ = convolution (φ.normed volume) (f k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
        rw [convolution_eq_swap (ContinuousLinearMap.lsmul ℝ ℝ)]
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [ρ, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        ring
  have havg' : (fun k => (∫ y, (fun j => f j y) ∂P) k) ∈ C := by
    change (∫ y, (fun k => f k y) ∂P) ∈ C
    exact havg
  simpa only [hcoord] using havg'

end FunctionalInequalities.Analysis

end ConvexRangeMollification
