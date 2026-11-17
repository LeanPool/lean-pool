/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Inverse
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Regular log-concave laws

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12): a log-concave probability measure is
regular if its density is `e^{-V}` with `V` smooth, every derivative of `V` of polynomial growth,
and
`a Id ≤ ∇²V ≤ b Id` for some `a, b > 0`. `RegularPotential V a b` records exactly these source
assumptions (and nothing derived). The law is `volume.tilted (-V)`, with density `e^{-V}/Z`,
`Z = ∫ e^{-V}`; the paper's normalized potential is `V + log Z`, which has the same derivatives, so
nothing is lost by not normalizing `V` itself. From them we derive the analytic premises of the
general tilt,
integration-by-parts and Bochner identities: `e^{-V}` is Lebesgue integrable with positive integral,
`volume.tilted (-V)` is a probability measure with Gaussian tails and all exponential moments, and
`∇V` grows polynomially. The general identities then hold for the regular law with these premises
discharged.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The source's regular potential (BKL (12)): `V` smooth with every derivative of polynomial growth
(Mathlib's `HasTemperateGrowth`) and `a ‖v‖² ≤ ∇²V(x)(v, v) ≤ b ‖v‖²` with `a > 0`. The source also
asks `b > 0`; in positive dimension it follows from the two Hessian bounds (`a ≤ b`), while in
dimension `0` the structure allows any `b`. -/
structure RegularPotential (V : E → ℝ) (a b : ℝ) : Prop where
  temperate : V.HasTemperateGrowth
  pos : 0 < a
  lower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v
  upper : ∀ x v, bilinearIteratedFDerivTwo ℝ V x v v ≤ b * ‖v‖ ^ 2

namespace RegularPotential

variable {V : E → ℝ} {a b : ℝ}

section QuadraticGrowth

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Strong convexity, as the tangent bound at the base point `0`:
`V x ≥ V 0 + ⟪∇V(0), x⟫ + (a/2) ‖x‖²`. -/
theorem quadratic_lower (hV : RegularPotential V a b) (x : E) :
    V 0 + ⟪gradient V 0, x⟫ + a / 2 * ‖x‖ ^ 2 ≤ V x := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let c : ℝ := a / 2 * ‖x‖ ^ 2
  let q : ℝ → ℝ := fun t => f t - c * t ^ 2
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hf (t : ℝ) : HasDerivAt f (fderiv ℝ V (t • x) x) t :=
    (hV2.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hq (t : ℝ) : HasDerivAt q (fderiv ℝ V (t • x) x - c * (2 * t)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hf t).fun_sub ((hasDerivAt_pow 2 t).const_mul c)
  have hqderiv : deriv q = fun t => fderiv ℝ V (t • x) x - c * (2 * t) :=
    funext fun t => (hq t).deriv
  have hq2 (t : ℝ) :
    HasDerivAt (deriv q) (bilinearIteratedFDerivTwo ℝ V (t • x) x x - 2 * c) t := by
    rw [hqderiv]
    have hsecond :=
      (differentiable_fderiv_apply hV2 x (t • x)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hV2] at hsecond
    convert hsecond.sub (((hasDerivAt_id t).const_mul 2).const_mul c) using 1 <;>
      first
      | rfl
      | ring
  have hconv : ConvexOn ℝ Set.univ q :=
    convexOn_of_deriv2_nonneg' convex_univ
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hq2 t).differentiableAt.differentiableWithinAt)
      (fun t _ => by
        rw [Function.iterate_succ_apply, Function.iterate_one, (hq2 t).deriv]
        have hh := hV.lower (t • x) x
        dsimp [c]
        linarith)
  have hs :=
    hconv.le_slope_of_hasDerivAt (by simp) (by simp) (show (0 : ℝ) < 1 by norm_num) (hq 0)
  simp [slope_def_field, q, f, c] at hs
  rw [inner_gradient_left]
  linarith

/-- Gaussian domination of the density: `e^{-V(x)} ≤ C e^{-(a/4)‖x‖²}`. -/
theorem exp_neg_le_gaussian (hV : RegularPotential V a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Real.exp ((-V) x) ≤ C * Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
    refine ⟨Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a), le_of_lt (Real.exp_pos _), ?_⟩
    intro x
    have hinner' := real_inner_le_norm (-gradient V 0) x
    have hinner :
        -⟪gradient V 0, x⟫ ≤ ‖gradient V 0‖ * ‖x‖ := by
      simpa using hinner'
    have hamgm :
        ‖gradient V 0‖ * ‖x‖ ≤
          ‖gradient V 0‖ ^ 2 / a + a / 4 * ‖x‖ ^ 2 := by
      have hs :
          0 ≤ (a * ‖x‖ - 2 * ‖gradient V 0‖) ^ 2 :=
        sq_nonneg (a * ‖x‖ - 2 * ‖gradient V 0‖)
      have ha : a ≠ 0 := ne_of_gt hV.pos
      calc
        ‖gradient V 0‖ * ‖x‖ ≤
            (‖gradient V 0‖ ^ 2 + a ^ 2 / 4 * ‖x‖ ^ 2) / a := by
          apply (le_div_iff₀ hV.pos).2
          nlinarith [hs]
        _ = ‖gradient V 0‖ ^ 2 / a + a / 4 * ‖x‖ ^ 2 := by
          field_simp [ha]
    have hexp :
        (-V) x ≤
          -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2 := by
      change -V x ≤
        -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2
      have hq := hV.quadratic_lower x
      linarith
    calc
      Real.exp ((-V) x) ≤
          Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2) :=
        Real.exp_le_exp.mpr hexp
      _ = Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a) *
          Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
        rw [show
          -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2 =
            (-V 0 + ‖gradient V 0‖ ^ 2 / a) +
              (-(a / 4) * ‖x‖ ^ 2) by ring]
        rw [Real.exp_add]

end QuadraticGrowth

/-- `e^{-V}` is Lebesgue integrable. -/
theorem integrable_exp_neg (hV : RegularPotential V a b) :
    Integrable (fun x => Real.exp ((-V) x)) (volume : Measure E) := by
  obtain ⟨C, hC0, hC⟩ := hV.exp_neg_le_gaussian
  have ha4 : 0 < a / 4 := by linarith [hV.pos]
  have hb : 0 < ((a / 4 : ℝ) : ℂ).re := by simpa using ha4
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) hb 0 0).norm
  have hgauss : Integrable (fun x : E => Real.exp (-(a / 4) * ‖x‖ ^ 2)) (volume : Measure E) := by
    refine hg.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have hcont : Continuous fun x => Real.exp ((-V) x) :=
    Real.continuous_exp.comp hV.temperate.1.continuous.neg
  refine
    (hgauss.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hC x

/-- The normalizing constant is positive. -/
theorem integral_exp_neg_pos (hV : RegularPotential V a b) :
    0 < ∫ x, Real.exp ((-V) x) ∂(volume : Measure E) := by
    apply integral_exp_pos
    exact integrable_exp_neg hV

/-- The regular law `volume.tilted (-V)` is a probability measure. -/
theorem isProbabilityMeasure (hV : RegularPotential V a b) :
    IsProbabilityMeasure ((volume : Measure E).tilted (-V)) := by
    exact MeasureTheory.isProbabilityMeasure_tilted (integrable_exp_neg hV)

omit [CompleteSpace E] in
private theorem regularMoment_gaussian_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c * ‖x‖ ^ 2)) (volume : Measure E) := by
  have hb : 0 < (c : ℂ).re := by simpa using hc
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

/-- The regular law has all exponential moments. -/
theorem integrable_exp_mul_norm (hV : RegularPotential V a b) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) ((volume : Measure E).tilted (-V)) := by
  obtain ⟨C, hC, hdom⟩ := hV.exp_neg_le_gaussian
  let K : ℝ := 2 * r ^ 2 / a
  have hlin (x : E) : r * ‖x‖ ≤ a / 8 * ‖x‖ ^ 2 + K := by
    have hp := sq_nonneg (a * ‖x‖ - 4 * r)
    have he : K * a = 2 * r ^ 2 := div_mul_cancel₀ _ hV.pos.ne'
    apply (mul_le_mul_iff_right₀ hV.pos).mp
    nlinarith
  apply (integrable_tilted_iff hV.integrable_exp_neg _).2
  change Integrable (fun x => Real.exp ((-V) x) * Real.exp (r * ‖x‖))
    (volume : Measure E)
  refine ((regularMoment_gaussian_integrable (E := E) (c := a / 8)
    (div_pos hV.pos (by norm_num))).const_mul (C * Real.exp K)).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp hV.temperate.1.continuous.neg).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_norm))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    calc
      Real.exp ((-V) x) * Real.exp (r * ‖x‖) ≤
          (C * Real.exp (-(a / 4) * ‖x‖ ^ 2)) * Real.exp (r * ‖x‖) :=
        mul_le_mul_of_nonneg_right (hdom x) (Real.exp_pos _).le
      _ = C * Real.exp (r * ‖x‖ - a / 4 * ‖x‖ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ C * Real.exp (K + (-(a / 8) * ‖x‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        linarith [hlin x]
      _ = (C * Real.exp K) * Real.exp (-(a / 8) * ‖x‖ ^ 2) := by
        rw [Real.exp_add]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `∇V` grows polynomially. -/
theorem exists_norm_gradient_le (hV : RegularPotential V a b) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖) ^ k := by
    obtain ⟨k, C, hC⟩ := hV.temperate.2 1
    refine ⟨C, k, ?_⟩
    intro x
    rw [norm_gradient_eq_norm_iteratedFDeriv_one]
    exact hC x

/-- The regular law as a probability measure. -/
def law (hV : RegularPotential V a b) : ProbabilityMeasure E :=
  ⟨(volume : Measure E).tilted (-V), hV.isProbabilityMeasure⟩

theorem logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge hW hV.pos.le hV.lower)

theorem interior_support_law (hV : RegularPotential V a b) :
    (interior ((hV.law : ProbabilityMeasure E) : Measure E).support).Nonempty := by
    change
      (interior
        (((volume : Measure E).tilted (-V)).support)).Nonempty
    exact
      FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted
        (volume : Measure E) (ν := hV.law) rfl

/-! ### The general identities for regular laws -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **BKL Lemma 3.6, (50)**, for a regular law and a tensor-valued `u ∈ 𝒜`, with every analytic
premise derived from (12). -/
theorem taylorTensor_neg_weightedLaplacianVec (hV : RegularPotential V a b) {f : E → F}
    (hf : f.HasTemperateGrowth) (d : ℕ) :
    taylorTensor ((volume : Measure E).tilted (-V)) (fun x => -weightedLaplacianVec V f x)
        (d + 1) =
      symmetrizeML
        (taylorTensor ((volume : Measure E).tilted (-V)) (fderiv ℝ f) d).uncurryRight := by
  obtain ⟨CV, kV, hVg⟩ := hV.exists_norm_gradient_le
  exact
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor_neg_weightedLaplacianVec
      (volume : Measure E) (hV.temperate.1.of_le (by simp)) hVg (hV.integrable_exp_mul_norm) hf
      d

/-- **BKL Lemma 3.6, (49)**, for a regular law and a tensor-valued `u ∈ 𝒜`. -/
theorem taylorTensor_one_neg_weightedLaplacianVec (hV : RegularPotential V a b) {f : E → F}
    (hf : f.HasTemperateGrowth) (h : Fin 1 → E) :
    taylorTensor ((volume : Measure E).tilted (-V)) (fun x => -weightedLaplacianVec V f x) 1 h =
      (∫ x, fderiv ℝ f x ∂((volume : Measure E).tilted (-V))) (h 0) := by
    let : IsProbabilityMeasure ((volume : Measure E).tilted (-V)) :=
      hV.isProbabilityMeasure
    rw [taylorTensor_neg_weightedLaplacianVec hV hf 0]
    simp [taylorTensor, symmetrizeML, tiltAverage, expTilt]

/-- **BKL (48)** for a regular law and a tensor-valued `u ∈ 𝒜`. -/
theorem tiltAverage_neg_weightedLaplacianVec (hV : RegularPotential V a b) {f : E → F}
    (hf : f.HasTemperateGrowth) (z : E) :
    tiltAverage ((volume : Measure E).tilted (-V)) (fun x => -weightedLaplacianVec V f x) z =
      tiltAverage ((volume : Measure E).tilted (-V)) (fderiv ℝ f) z z := by
    rcases hV.exists_norm_gradient_le with ⟨C, k, hC⟩
    apply FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacianVec
    · exact hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
    · exact hC
    · exact hV.integrable_exp_mul_norm
    · exact hf

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **BKL (15)** for a regular law and tensor fields of temperate growth. -/
theorem integral_inner_weightedLaplacianVec_eq_neg (hV : RegularPotential V a b) {f g : E → G}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, ⟪weightedLaplacianVec V f x, g x⟫ ∂((volume : Measure E).tilted (-V)) =
      -∫ x,
          ∑ i,
            ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
              fderiv ℝ g x (stdOrthonormalBasis ℝ E i)⟫ ∂((volume : Measure E).tilted (-V)) := by
  have hV1 : ContDiff ℝ 1 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg1 : ContDiff ℝ 1 g := hg.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hexp : Integrable (fun x : E => Real.exp ((-V) x)) (volume : Measure E) :=
    hV.integrable_exp_neg
  have hpos : 0 < ∫ x, Real.exp ((-V) x) ∂(volume : Measure E) := hV.integral_exp_neg_pos
  have hprob : IsProbabilityMeasure ((volume : Measure E).tilted (-V)) :=
    hV.isProbabilityMeasure
  have hmom :
    ∀ r : ℝ, Integrable (fun x : E => Real.exp (r * ‖x‖)) ((volume : Measure E).tilted (-V)) :=
    hV.integrable_exp_mul_norm
  obtain ⟨CV, kV, hgrad⟩ := hV.exists_norm_gradient_le
  apply FunctionalInequalities.Analysis.BakryEmery.integral_inner_weightedLaplacianVec_eq_neg
  all_goals
    first
    | exact hV1
    | exact hf
    | exact hg
    | exact hmom
    | exact hgrad

/-- **BKL (16)** with the curvature bound `a` of (12), for a regular law and a tensor field of
temperate growth: `∫ ‖∇²u‖²_HS + a ∫ ‖∇u‖²_HS ≤ ∫ ‖ℒu‖²` (the inequality of Lemma 3.4). -/
theorem integral_hessian_add_le_norm_sq_weightedLaplacianVec (hV : RegularPotential V a b)
    {f : E → G} (hf : f.HasTemperateGrowth) :
    ∫ x,
          ∑ i,
            ∑ j,
              ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
                2 ∂((volume : Measure E).tilted (-V)) +
        a *
          ∫ x,
            ∑ i,
              ‖fderiv ℝ f x (stdOrthonormalBasis ℝ E i)‖ ^
                2 ∂((volume : Measure E).tilted (-V)) ≤
      ∫ x, ‖weightedLaplacianVec V f x‖ ^ 2 ∂((volume : Measure E).tilted (-V)) := by
  exact
    FunctionalInequalities.Analysis.BakryEmery.integral_hessian_add_le_norm_sq_weightedLaplacianVec
      (volume : Measure E) hV.temperate hV.integrable_exp_mul_norm hf hV.lower (ρ := a)

/-- **BKL Lemma 2.1, operator-domain part, for a regular law**: with `C = 1/a`, every centered
`g ∈ L²` has a unique centered preimage under the closed generator, `‖u‖ ≤ a⁻¹ ‖g‖`. -/
theorem existsUnique_centered_adjointComp_eq (hV : RegularPotential V a b)
    (g : Lp ℝ 2 ((hV.law : ProbabilityMeasure E) : Measure E)) (hg : L2.mean hV.law g = 0) :
    ∃! u : (Analysis.Semigroup.adjointComp
        ((hV.logConcave_law).closedWeightedOperator (volume : Measure E)
          (ContinuousLinearMap.id ℝ E) hV.interior_support_law)).domain,
      L2.mean hV.law (u : Lp ℝ 2 ((hV.law : ProbabilityMeasure E) : Measure E)) = 0 ∧
        Analysis.Semigroup.adjointComp
          ((hV.logConcave_law).closedWeightedOperator (volume : Measure E)
            (ContinuousLinearMap.id ℝ E) hV.interior_support_law) u = g ∧
          ‖(u : Lp ℝ 2 ((hV.law : ProbabilityMeasure E) : Measure E))‖ ≤ a⁻¹ * ‖g‖ := by
    simpa [law] using
      (FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_of_hessian
        (volume : Measure E) hV.logConcave_law hV.interior_support_law rfl
        (hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top))
        hV.pos hV.lower g hg)

/-- **BKL Lemma 2.1, operator-domain part, componentwise tensor lift, for a regular law**: with
`C = 1/a`, for centered `g ∈ L²(μ; G)` and an orthonormal basis `e` of `G` there is exactly one
family
of centered `u_k` in the generator domain with `A u_k = ⟪e k, g⟫`, and `Σ_k ‖u_k‖² ≤ a⁻² ‖g‖²`. -/
theorem existsUnique_centered_adjointComp_eq_components (hV : RegularPotential V a b)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ G)
    (g : Lp G 2 ((hV.law : ProbabilityMeasure E) : Measure E))
    (hg : ∫ x, g x ∂((hV.law : ProbabilityMeasure E) : Measure E) = 0) :
    ∃! u :
      ι →
        (Analysis.Semigroup.adjointComp
            ((hV.logConcave_law).closedWeightedOperator (volume : Measure E)
              (ContinuousLinearMap.id ℝ E) hV.interior_support_law)).domain,
      (∀ k, L2.mean hV.law (u k : Lp ℝ 2 ((hV.law : ProbabilityMeasure E) : Measure E)) = 0) ∧
        (∀ k,
            Analysis.Semigroup.adjointComp
                ((hV.logConcave_law).closedWeightedOperator (volume : Measure E)
                  (ContinuousLinearMap.id ℝ E) hV.interior_support_law)
                (u k) =
              (innerSL ℝ (e k)).compLp g) ∧
          ∑ k, ‖(u k : Lp ℝ 2 ((hV.law : ProbabilityMeasure E) : Measure E))‖ ^ 2 ≤
            a⁻¹ ^ 2 * ‖g‖ ^ 2 :=
  FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_components_of_hessian
    (volume : Measure E) hV.logConcave_law hV.interior_support_law rfl
    (hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hV.pos hV.lower e g hg

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
**Regular potential from a convex temperate potential with bounded Hessian**: if `f` is convex with
`Function.HasTemperateGrowth` and `∇²f ≤ B`, then `f + δ/2‖·‖²` is a regular potential with
curvature
bounds `δ ≤ ∇² ≤ B + δ` (BKL Section 2, p. 5, the quadratic tilt step of the regular approximation).
-/
theorem of_convexOn_hasTemperateGrowth {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hc : ConvexOn ℝ Set.univ f) {B δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ x v, bilinearIteratedFDerivTwo ℝ f x v v ≤ B * ‖v‖ ^ 2) :
    RegularPotential (fun y => f y + δ / 2 * ‖y‖ ^ 2) δ (B + δ)
    where
  temperate := by
    have hq :=
      (Function.HasTemperateGrowth.const (δ / 2 : ℝ)).mul
        (Function.hasTemperateGrowth_norm_sq E)
    exact hf.add hq
  pos := hδ
  lower x
    v := by
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic
        (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))]
    have h :=
      Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn
        (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)) hc x v
    linarith
  upper x
    v := by
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic
        (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))]
    have h := hb x v
    nlinarith

/--
Lower curvature constant of `V ∘ (L · + c)`: `a / (1 + ‖L⁻¹‖)²` (positive in every dimension). -/
noncomputable def affineLowerConstant (a : ℝ) (L : E ≃L[ℝ] E) : ℝ :=
  a / (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2

/-- Upper curvature constant of `V ∘ (L · + c)`: `max b 1 · (1 + ‖L‖)²`. -/
noncomputable def affineUpperConstant (b : ℝ) (L : E ≃L[ℝ] E) : ℝ :=
  max b 1 * (1 + ‖(L : E →L[ℝ] E)‖) ^ 2

section AffineBounds

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem affineLowerConstant_pos {a : ℝ} (ha : 0 < a) (L : E ≃L[ℝ] E) :
    0 < affineLowerConstant a L := by
  unfold affineLowerConstant
  exact div_pos ha (sq_pos_of_pos (by positivity))

theorem affineUpperConstant_pos (b : ℝ) (L : E ≃L[ℝ] E) : 0 < affineUpperConstant b L := by
  unfold affineUpperConstant
  exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right b 1)) (sq_pos_of_pos (by positivity))

/--
**Regular potentials are preserved by affine changes of variables**: `V ∘ (L · + c)` is regular with
constants `affineLowerConstant a L`, `affineUpperConstant b L` (positive also in dimension zero). -/
theorem comp_affine {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) (L : E ≃L[ℝ] E)
    (c : E) :
    KLS.RegularPotential (fun x => V (L x + c)) (affineLowerConstant a L)
      (affineUpperConstant b L) := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨?_, affineLowerConstant_pos hV.pos L, ?_, ?_⟩
  · exact hV.temperate.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))
  · intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine hV2 L c x v v]
    have hbase := hV.lower (L x + c) (L v)
    have hinv : ‖v‖ ≤ (1 + ‖(L.symm : E →L[ℝ] E)‖) * ‖L v‖ := by
      calc
        ‖v‖ = ‖L.symm (L v)‖ := by rw [L.symm_apply_apply]
        _ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖L v‖ := (L.symm : E →L[ℝ] E).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hsq : ‖v‖ ^ 2 ≤ (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2 * ‖L v‖ ^ 2 := by
      simpa only [← pow_two, mul_pow] using mul_self_le_mul_self (norm_nonneg v) hinv
    have hdiv : ‖v‖ ^ 2 / (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2 ≤ ‖L v‖ ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).2
      simpa only [mul_comm] using hsq
    have hmul := mul_le_mul_of_nonneg_left hdiv hV.pos.le
    apply le_trans _ hbase
    simpa only [affineLowerConstant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hmul
  · intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine hV2 L c x v v]
    have hbase := hV.upper (L x + c) (L v)
    have hnorm : ‖L v‖ ≤ (1 + ‖(L : E →L[ℝ] E)‖) * ‖v‖ :=
      ((L : E →L[ℝ] E).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have hsq : ‖L v‖ ^ 2 ≤ (1 + ‖(L : E →L[ℝ] E)‖) ^ 2 * ‖v‖ ^ 2 := by
      simpa only [← pow_two, mul_pow] using mul_self_le_mul_self (norm_nonneg _) hnorm
    calc
      bilinearIteratedFDerivTwo ℝ V (L x + c) (L v) (L v) ≤ b * ‖L v‖ ^ 2 := hbase
      _ ≤ max b 1 * ‖L v‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left b 1) (sq_nonneg _)
      _ ≤ max b 1 * ((1 + ‖(L : E →L[ℝ] E)‖) ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (le_trans zero_le_one (le_max_right b 1))
      _ = affineUpperConstant b L * ‖v‖ ^ 2 := by unfold affineUpperConstant; ring

end AffineBounds


end RegularPotential

end FunctionalInequalities.KLS
