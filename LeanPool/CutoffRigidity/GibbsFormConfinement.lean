/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.L2FatouBounds
public import LeanPool.CutoffRigidity.GibbsSobolevClassical
public import LeanPool.CutoffRigidity.GibbsSobolevApproximation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import LeanPool.CutoffRigidity.RealL2Identities

/-!
# Actual weighted form confinement

Compact weighted integration by parts and strong convexity control the
spatial second moment of the squared function by its genuine gradient
energy and L² norm. Compact embedding still requires a separate local
Rellich argument and is not asserted here.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual gradient has the radial coercivity forced by the Hessian bound. -/
theorem gibbs_radial_gradient_lower {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    ρ * ‖x‖ ^ 2 ≤ inner ℝ x (gradient V x) + ‖gradient V 0‖ * ‖x‖ := by
  have hm := gradient_strongly_monotone_of_hessian_bound hV ρ hHess x 0
  simp only [sub_zero, inner_sub_left] at hm
  have hi : -inner ℝ (gradient V 0) x ≤ ‖gradient V 0‖ * ‖x‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  rw [real_inner_comm x (gradient V x)] at hm
  linarith

/-- The exact radial compact Gibbs IBP identity. -/
theorem compact_gibbs_radial_identity {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, inner ℝ x (gradient V x) * f x ^ 2 ∂gibbsMeasure volume V) =
      d * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) +
        2 * (∫ x, f x * inner ℝ x (gradient f x) ∂gibbsMeasure volume V) := by
  let μ := gibbsMeasure volume V
  have hff : ContDiff ℝ 1 (fun x => f x ^ 2) := (hf.pow 2).of_le (by norm_num)
  have hffc : HasCompactSupport (fun x => f x ^ 2) :=
    hfc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hDf (i : Fin d) := c1_coordinateDerivative_of_c2 hf i
  have hDV (i : Fin d) := c1_coordinateDerivative_of_c2 hV i
  have hDfsq (i : Fin d) (x : E) : coordinateDerivative i (fun y => f y ^ 2) x =
      2 * f x * coordinateDerivative i f x := by
    unfold coordinateDerivative
    rw [fderiv_fun_pow 2 (hf.differentiable (by norm_num) x)]
    simp only [smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul]
    norm_num
  have hcoord (i : Fin d) : ContDiff ℝ 1 (fun x : E => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hcoordD (i : Fin d) (x : E) : coordinateDerivative i (fun y : E => y i) x = 1 := by
    unfold coordinateDerivative
    rw [show (fun y : E => y i) = (EuclideanSpace.proj i) from rfl,
      (EuclideanSpace.proj i : E →L[ℝ] ℝ).fderiv]
    simp
  have hA (i : Fin d) : Integrable (fun x : E => f x ^ 2 * (x i * coordinateDerivative i V x)) μ :=
    integrable_cutoff_square_mul_continuous hV.continuous hf.continuous hfc (by fun_prop)
  have hB (i : Fin d) : Integrable (fun x : E => f x * (x i * coordinateDerivative i f x)) μ :=
    integrable_cutoff_mul_continuous hV.continuous hf.continuous hfc (by fun_prop)
  have hN : Integrable (fun x => f x ^ 2) μ :=
    integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (hf.continuous.pow 2) hffc
  have hrow (i : Fin d) : (∫ x, f x ^ 2 * (x i * coordinateDerivative i V x) ∂μ) =
      (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, f x * (x i * coordinateDerivative i f x) ∂μ) := by
    have hi := compact_directional_gibbs_ibp hV hff (hcoord i) hffc i
    simp_rw [hcoordD, mul_one, coordinateWeightedAdjoint, hDfsq] at hi
    have hp (x : E) : (2 * f x * coordinateDerivative i f x - f x ^ 2 * coordinateDerivative i V x)
      * x i =
        2 * (f x * (x i * coordinateDerivative i f x)) - f x ^ 2 * (x i * coordinateDerivative i V
          x) := by ring
    simp_rw [hp] at hi
    rw [integral_sub ((hB i).const_mul 2) (hA i), integral_const_mul] at hi
    linarith
  have hiV (x : E) : inner ℝ x (gradient V x) = ∑ i : Fin d, x i * coordinateDerivative i V x := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  have hif (x : E) : inner ℝ x (gradient f x) = ∑ i : Fin d, x i * coordinateDerivative i f x := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  simp_rw [hiV, hif, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hA i),
    integral_finsetSum _ (fun i _ => hB i)]
  simp_rw [show ∀ i : Fin d, (∫ x, x i * coordinateDerivative i V x * f x ^ 2 ∂gibbsMeasure volume
    V) =
      (∫ x, f x ^ 2 ∂gibbsMeasure volume V) +
        2 * (∫ x, f x * (x i * coordinateDerivative i f x) ∂gibbsMeasure volume V) from
      fun i => by simpa only [μ, mul_comm, mul_left_comm, mul_assoc] using hrow i]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rfl

/-- The pointwise polynomial inequality behind weighted form confinement. -/
theorem gibbs_confinement_pointwise {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    ρ ^ 2 * (‖x‖ ^ 2 * f x ^ 2) ≤
      2 * ρ * (inner ℝ x (gradient V x) * f x ^ 2) -
        4 * ρ * (f x * inner ℝ x (gradient f x)) + 8 * ‖gradient f x‖ ^ 2 +
          2 * ‖gradient V 0‖ ^ 2 * f x ^ 2 := by
  have hr := mul_le_mul_of_nonneg_right (gibbs_radial_gradient_lower hV ρ hHess x)
    (mul_nonneg hρ.le (sq_nonneg (f x)))
  have hb : f x * inner ℝ x (gradient f x) ≤ |f x| * (‖x‖ * ‖gradient f x‖) := by
    calc
      _ ≤ |f x * inner ℝ x (gradient f x)| := le_abs_self _
      _ = |f x| * |inner ℝ x (gradient f x)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
  have hy1 : 2 * ρ * (f x * inner ℝ x (gradient f x)) ≤
      ρ ^ 2 / 4 * (‖x‖ ^ 2 * f x ^ 2) + 4 * ‖gradient f x‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * ρ)
    rw [← sq_abs (f x)]
    nlinarith [sq_nonneg (ρ * |f x| * ‖x‖ / 2 - 2 * ‖gradient f x‖)]
  have hy2 : ρ * ‖gradient V 0‖ * ‖x‖ * f x ^ 2 ≤
      ρ ^ 2 / 4 * (‖x‖ ^ 2 * f x ^ 2) + ‖gradient V 0‖ ^ 2 * f x ^ 2 := by
    have hh := mul_nonneg (sq_nonneg (ρ * ‖x‖ / 2 - ‖gradient V 0‖)) (sq_nonneg (f x))
    nlinarith
  nlinarith

/-- A genuine compact-test quadratic moment bound, with explicit constants
from the actual potential and curvature. No weighted-product integrability
is assumed: compact support proves every term integrable. -/
theorem compact_gibbs_form_confinement {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ρ ^ 2 * (∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂gibbsMeasure volume V) ≤
      2 * (ρ * d + ‖gradient V 0‖ ^ 2) * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) +
        8 * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) := by
  let μ := gibbsMeasure volume V
  have hGf : Continuous (gradient f) := continuous_gradient_of_c1 (hf.of_le (by norm_num))
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hfc2 : HasCompactSupport (fun x => f x ^ 2) :=
    hfc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hQ : Integrable (fun x : E => ‖x‖ ^ 2 * f x ^ 2) μ := by
    have h := integrable_cutoff_square_mul_continuous hV.continuous hf.continuous hfc
      (g := fun x : E => ‖x‖ ^ 2) (by fun_prop)
    simpa only [mul_comm] using h
  have hD : Integrable (fun x => inner ℝ x (gradient V x) * f x ^ 2) μ := by
    have h := integrable_cutoff_square_mul_continuous hV.continuous hf.continuous hfc
      (g := fun x => inner ℝ x (gradient V x)) (by fun_prop)
    simpa only [mul_comm] using h
  have hC : Integrable (fun x => f x * inner ℝ x (gradient f x)) μ :=
    integrable_cutoff_mul_continuous hV.continuous hf.continuous hfc (by fun_prop)
  have hN : Integrable (fun x => f x ^ 2) μ :=
    integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (hf.continuous.pow 2) hfc2
  have hE : Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    exact ((hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)).comp_left
      (g := fun z : E => ‖z‖ ^ 2) (by simp)
  have hi := integral_mono (hQ.const_mul (ρ ^ 2))
    ((((hD.const_mul (2 * ρ)).sub (hC.const_mul (4 * ρ))).add (hE.const_mul 8)).add
      (hN.const_mul (2 * ‖gradient V 0‖ ^ 2))) (gibbs_confinement_pointwise hV ρ hρ hHess)
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  have ha1 := integral_add
    (((hD.const_mul (2 * ρ)).sub (hC.const_mul (4 * ρ))).add (hE.const_mul 8))
    (hN.const_mul (2 * ‖gradient V 0‖ ^ 2))
  have ha2 := integral_add ((hD.const_mul (2 * ρ)).sub (hC.const_mul (4 * ρ))) (hE.const_mul 8)
  have hs := integral_sub (hD.const_mul (2 * ρ)) (hC.const_mul (4 * ρ))
  simp only [Pi.add_apply, Pi.sub_apply] at ha1 ha2 hs
  rw [integral_const_mul, ha1, ha2, hs, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hid := compact_gibbs_radial_identity hV hf hfc
  change (∫ x, inner ℝ x (gradient V x) * f x ^ 2 ∂μ) = _ at hid
  rw [hid] at hi
  nlinarith

/-- Weighted squared moments are lower semicontinuous under actual L²
convergence. Fatou is applied to an actual almost-everywhere subsequence. -/
theorem weighted_sq_lintegral_le_of_L2_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {fn : ℕ → α →₂[μ] ℝ} {f : α →₂[μ] ℝ} (hfn : Tendsto fn atTop (𝓝 f))
    (w : α → ℝ) (hw : Measurable w) (bn : ℕ → ℝ) (b : ℝ)
    (hb : Tendsto bn atTop (𝓝 b))
    (hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (w x * fn n x ^ 2) ∂μ) ≤ ENNReal.ofReal (bn n)) :
    (∫⁻ x, ENNReal.ofReal (w x * f x ^ 2) ∂μ) ≤ ENNReal.ofReal b := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfn).exists_seq_tendsto_ae'
  let F (n : ℕ) (x : α) := ENNReal.ofReal (w x * fn (ns n) x ^ 2)
  have hFm (n : ℕ) : Measurable (F n) := by
    exact (hw.mul ((Lp.stronglyMeasurable (fn (ns n))).measurable.pow_const 2)).ennreal_ofReal
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (w x * f x ^ 2))) := by
    filter_upwards [hae] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hx.pow 2).const_mul (w x))
  have hblim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hb.comp hns)
  exact lintegral_le_of_ae_tendsto_bounds (fun n => (hFm n).aemeasurable) hpoint
    (fun n => hbound (ns n)) hblim

/-- The actual compact generator graph satisfies confinement in terms of
its genuine L² input and gradient norms. -/
theorem compactGradient_graph_confinement {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : compactGibbsGeneratorDomain V) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2 * (u : E →₂[gibbsMeasure volume V] ℝ) x ^ 2) ∂gibbsMeasure
      volume V) ≤
      ENNReal.ofReal ((2 * (ρ * d + ‖gradient V 0‖ ^ 2) * ‖(u : E →₂[gibbsMeasure volume V] ℝ)‖ ^ 2
        +
        8 * ‖compactGibbsGradientMap hV.continuous hprob u‖ ^ 2) / ρ ^ 2) := by
  let f := compactGibbsRepresentative V u
  have hf := (compactGibbsRepresentative_spec V u).1
  have hfc := (compactGibbsRepresentative_spec V u).2.1
  have hQ : Integrable (fun x : E => ‖x‖ ^ 2 * f x ^ 2) (gibbsMeasure volume V) := by
    have hi := integrable_cutoff_square_mul_continuous hV.continuous hf.continuous hfc
      (g := fun x : E => ‖x‖ ^ 2) (by fun_prop)
    simpa only [mul_comm] using hi
  have hN : ‖(u : E →₂[gibbsMeasure volume V] ℝ)‖ ^ 2 =
      ∫ x, f x ^ 2 ∂gibbsMeasure volume V :=
    lp_real_norm_sq_eq_integral (compactGibbsRepresentative_spec V u).2.2.symm
  have hE : ‖compactGibbsGradientMap hV.continuous hprob u‖ ^ 2 =
      ∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V :=
    norm_toLp_norm_sq (compactGibbsGradient_memLp hprob u)
  have hae : (fun x => ENNReal.ofReal (‖x‖ ^ 2 * (u : E →₂[gibbsMeasure volume V] ℝ) x ^ 2))
    =ᵐ[gibbsMeasure volume V]
      (fun x => ENNReal.ofReal (‖x‖ ^ 2 * f x ^ 2)) := by
    filter_upwards [(compactGibbsRepresentative_spec V u).2.2] with x hx
    rw [← hx]
  rw [lintegral_congr_ae hae]
  rw [← ofReal_integral_eq_lintegral_ofReal hQ
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)), hN, hE]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  have h := compact_gibbs_form_confinement hV ρ hρ hHess hf hfc
  nlinarith

/-- The actual closed H¹ domain inherits confinement by graph approximation,
L² almost-everywhere subsequences, and Fatou. No compact embedding is assumed. -/
theorem gibbsSobolev_form_confinement {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hprob) :
    Integrable (fun x => ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2) (gibbsMeasure volume
      V) ∧
      (∫ x, ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2 ∂gibbsMeasure volume V) ≤
        (2 * (ρ * d + ‖gradient V 0‖ ^ 2) * ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 +
          8 * gibbsDirichletEnergy hV hprob u u) / ρ ^ 2 := by
  let μ := gibbsMeasure volume V
  let G := compactGibbsGradient hV.continuous hprob
  let a := 2 * (ρ * d + ‖gradient V 0‖ ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨p, hp, hfirst, hsecond⟩ := gibbsSobolev_strong_approximation_seq hV hprob u
  let bn (n : ℕ) : ℝ := (a * ‖(p n).1‖ ^ 2 + 8 * ‖(p n).2‖ ^ 2) / ρ ^ 2
  let b : ℝ := (a * ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 +
    8 * ‖gibbsSobolevDerivative hV hprob u‖ ^ 2) / ρ ^ 2
  have hbn : Tendsto bn atTop (𝓝 b) :=
    (((hfirst.norm.pow 2).const_mul a).add ((hsecond.norm.pow 2).const_mul 8)).div_const (ρ ^ 2)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbound (n : ℕ) : (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2 * (p n).1 x ^ 2) ∂μ) ≤ ENNReal.ofReal (bn n)
    := by
    obtain ⟨v, hv1, hv2⟩ := G.mem_graph_iff.mp (hp n)
    dsimp only [bn]
    rw [← hv1, ← hv2]
    exact compactGradient_graph_confinement hV hprob ρ hρ hHess v
  have hENN := weighted_sq_lintegral_le_of_L2_tendsto hfirst
    (fun x : E => ‖x‖ ^ 2) (by fun_prop) bn b hbn hbound
  have hQm : AEStronglyMeasurable
      (fun x : E => ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2) μ :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (gibbsSobolevInclusion hV hprob u)).pow 2)
  have hQ0 (x : E) : 0 ≤ ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hQ : Integrable (fun x => ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2) μ := by
    refine ⟨hQm, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).2
    exact lt_of_le_of_lt hENN ENNReal.ofReal_lt_top
  refine ⟨hQ, ?_⟩
  have hi := ofReal_integral_eq_lintegral_ofReal hQ (Filter.Eventually.of_forall hQ0)
  rw [← hi] at hENN
  have hh := (ENNReal.ofReal_le_ofReal_iff hb0).mp hENN
  change (∫ x, ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2 ∂μ) ≤ _
  simpa only [b, a, gibbsDirichletEnergy, real_inner_self_eq_norm_sq] using hh

/-- An explicit confinement constant for the genuine graph energy norm. -/
@[expose] noncomputable def gibbsFormConfinementConstant (V : E → ℝ) (ρ : ℝ) : ℝ :=
  (2 * (ρ * d + ‖gradient V 0‖ ^ 2) + 8) / ρ ^ 2

/-- The weighted second moment is uniformly bounded by the actual H¹ norm. -/
theorem gibbsSobolev_weighted_moment_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hprob) :
    (∫ x, ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2 ∂gibbsMeasure volume V) ≤
      gibbsFormConfinementConstant V ρ * ‖u‖ ^ 2 := by
  have hh := (gibbsSobolev_form_confinement hV hprob ρ hρ hHess u).2
  apply hh.trans
  rw [gibbsSobolev_norm_sq hV hprob u]
  unfold gibbsFormConfinementConstant
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg ρ)
  have hE := gibbsDirichletEnergy_nonneg hV hprob u
  have hN := sq_nonneg ‖gibbsSobolevInclusion hV hprob u‖
  have ha : 0 ≤ 2 * (ρ * d + ‖gradient V 0‖ ^ 2) := by positivity
  nlinarith

/-- Actual spatial L² tails decay like R⁻² uniformly on graph-energy balls. -/
theorem gibbsSobolev_tail_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hprob) (R : ℝ) (hR : 0 < R) :
    (∫ x in {x : E | R ≤ ‖x‖}, (gibbsSobolevInclusion hV hprob u x) ^ 2 ∂gibbsMeasure volume V) ≤
      gibbsFormConfinementConstant V ρ * ‖u‖ ^ 2 / R ^ 2 := by
  let μ := gibbsMeasure volume V
  let S := {x : E | R ≤ ‖x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_norm.measurable
  have hN : Integrable (fun x => (gibbsSobolevInclusion hV hprob u x) ^ 2) μ :=
    (Lp.memLp (gibbsSobolevInclusion hV hprob u)).integrable_sq
  have hQ := (gibbsSobolev_form_confinement hV hprob ρ hρ hHess u).1
  have hi := integral_mono ((hN.indicator hS).const_mul (R ^ 2)) hQ
    (show ∀ x : E, R ^ 2 * S.indicator (fun y => (gibbsSobolevInclusion hV hprob u y) ^ 2) x ≤
        ‖x‖ ^ 2 * (gibbsSobolevInclusion hV hprob u x) ^ 2 from fun x => by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hxR : R ≤ ‖x‖ := hx
        nlinarith [norm_nonneg x]
      · rw [Set.indicator_of_notMem hx]
        simp only [mul_zero]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [integral_const_mul, integral_indicator hS] at hi
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hh := gibbsSobolev_weighted_moment_bound hV hprob ρ hρ hHess u
  nlinarith

/-- Uniform confinement on every bounded-energy family in the actual
Sobolev graph norm. The missing local Rellich theorem remains separate. -/
theorem gibbsSobolev_uniform_tail_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (M : ℝ) (u : gibbsSobolevGraph hV hprob) (hu : ‖u‖ ≤ M)
    (R : ℝ) (hR : 0 < R) :
    (∫ x in {x : E | R ≤ ‖x‖}, (gibbsSobolevInclusion hV hprob u x) ^ 2 ∂gibbsMeasure volume V) ≤
      gibbsFormConfinementConstant V ρ * M ^ 2 / R ^ 2 := by
  apply (gibbsSobolev_tail_bound hV hprob ρ hρ hHess u R hR).trans
  have hC : 0 ≤ gibbsFormConfinementConstant V ρ := by
    unfold gibbsFormConfinementConstant
    positivity
  gcongr

end CutoffRigidity
