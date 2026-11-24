/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentLebesgue
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MeasureLocality

/-!
# Semicontinuity of the absolutely continuous part of positive currents (Boucksom)

Blueprint `ana:ac-density-liminf` (`blueprint/src/analytic.tex`; TN.5, route item 5 of
    `ana:volume-semicontinuity`).
Source: Boucksom, *On the volume of a line bundle* (2002), proof of
[Lemma 3.5](https://arxiv.org/pdf/math/0201031#page=11) (published Proposition 2.1).
The proof first shows `det(T_ac)^{1/n} ≥ liminf_k det(T_{k,ac})^{1/n}` almost everywhere
for weakly convergent positive `(1,1)`-currents. The proposition states a `limsup` bound.
This file generalizes the `liminf` estimate to infima over strongly positive test forms.

Let `U ⊆ ℂⁿ` be open and `T` a positive current of bidimension `(q,q)` on `U`
    (`LocalProductCurrents.IsPositive`), with the
pointwise density form `L_x` and the absolutely continuous weight `w = dσ_T/dλ` of
    `LocalCurrentLebesgue`, so that
`T_ac(γ) = w L_x(γ) λ`.

* **Mollified values** (`bump m`, `mol m x y = ρ_m(x - y)` with `ρ_m` a normed smooth bump of
    radius `1/(m+1)`, and the test
  function `bumpTest` it defines when the ball lies in `U`): for Lebesgue-almost every `x ∈ U` and
    every constant form `γ`,
  `T(γ)(ρ_m(x - ·)) → w(x) L_x(γ)` (`ae_tendsto_apply_bumpTest`): the absolutely continuous part
    by the Lebesgue
  differentiation theorem for mollifiers (`ae_tendsto_integral_mol_mul`), the singular part by
    Besicovitch's differentiation
  theorem (`ae_tendsto_integral_mol_singular`).
* **The functional** `acInf T C x = inf_{c ∈ C} w(x) L_x(c)` (in `ℝ≥0∞`) for a set `C` of strongly
    positive constant forms.
  For `q = n - 1` and `C` the forms `β^{n-1}/n!` of the positive definite `(1,1)`-forms `β` with
    `β^n = ω₀^n`, this is
  `det(T_ac)^{1/n}` (AM-GM); the statement here is for every `C`.
* **Semicontinuity** (`ae_liminf_acInf_le`): if positive currents `T_k → T` weakly (`T_k(γ)(φ)
    → T(γ)(φ)` for all constant
  forms and test functions), then `acInf T C x ≥ liminf_k acInf T_k C x` for Lebesgue-almost every
    `x ∈ U`.

The proof follows Boucksom's: for a mollifier `ρ` centred at `x`,
    `T_k(c)(ρ) ≥ T_{k,ac}(c)(ρ) ≥ ∫ ρ · acInf T_k C` (the
singular part is positive, and `acInf ≤ w L(c)` pointwise), so by Fatou
    `∫ ρ · liminf_k acInf T_k C ≤ T(c)(ρ)` for every
`c ∈ C`; letting `ρ` shrink, the left side tends to `liminf_k acInf T_k C (x)` (the left side
    bounds the local integrals, so
the liminf is locally integrable) and the right side to `w(x) L_x(c)`.  The concavity of
    `det^{1/n}` used by Boucksom is
replaced by the infimum over `C`: an infimum of linear functionals passes through integrals and
    limits directly. The conclusion is the `liminf` estimate obtained before the
subsequence step in Boucksom's proof.

Sorry-free.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ENNReal Convolution

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentSemicontinuity

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  SGPT.Foundations.Analysis.MeasureLocality

variable {n : ℕ}

local notation "E" => ComplexModel n

/-! ### Mollifiers -/

section Mollifier

variable (n) in
/-- The smooth bump function of radii `1/(2(m+1)) < 1/(m+1)` centred at `0`. -/
def bump (m : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (2 * ((m : ℝ) + 1))
  rOut := 1 / ((m : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

theorem bump_rOut (m : ℕ) : (bump n m).rOut = 1 / ((m : ℝ) + 1) := rfl

theorem bump_rOut_le (m : ℕ) : (bump n m).rOut ≤ 2 * (bump n m).rIn := by
  change 1 / ((m : ℝ) + 1) ≤ 2 * (1 / (2 * ((m : ℝ) + 1)))
  have h : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  field_simp
  exact le_rfl

theorem tendsto_bump_rOut : Tendsto (fun m => (bump n m).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Eventually the radius is below any positive number. -/
theorem eventually_bump_rOut_lt {r : ℝ} (hr : 0 < r) : ∀ᶠ m in atTop, (bump n m).rOut < r :=
  (tendsto_order.1 (tendsto_bump_rOut (n := n))).2 r hr

variable (n) in
/-- **The mollifier centred at `x`**: `y ↦ ρ_m(x - y)`. -/
def mol (m : ℕ) (x y : E) : ℝ := (bump n m).normed volume (x - y)

theorem mol_nonneg (m : ℕ) (x y : E) : 0 ≤ mol n m x y := (bump n m).nonneg_normed _

theorem contDiff_mol {k : ℕ∞} (m : ℕ) (x : E) : ContDiff ℝ k (mol n m x) :=
  (bump n m).contDiff_normed.comp (contDiff_const.sub contDiff_id)

theorem continuous_mol (m : ℕ) (x : E) : Continuous (mol n m x) := (contDiff_mol (k := 0)
    m x).continuous

theorem mol_eq_zero {m : ℕ} {x y : E} (hy : (bump n m).rOut ≤ dist y x) : mol n m x y = 0 := by
  rw [mol, ← Function.notMem_support, (bump n m).support_normed_eq, mem_ball, dist_zero_right,
    ← dist_eq_norm,
    dist_comm, not_lt]
  exact hy

theorem dist_lt_of_mol_ne_zero {m : ℕ} {x y : E} (hy : mol n m x y ≠ 0) : dist y x < (bump n
    m).rOut := by
  by_contra h
  exact hy (mol_eq_zero (not_lt.mp h))

theorem integral_mol (m : ℕ) (x : E) : ∫ y, mol n m x y = 1 := by
  simp only [mol]
  rw [integral_sub_left_eq_self (fun z => (bump n m).normed volume z) volume x]
  exact (bump n m).integral_normed

theorem integrable_mol (m : ℕ) (x : E) : Integrable (mol n m x) := by
  have h := (bump n m).integrable_normed (μ := (volume : Measure E))
  exact h.comp_sub_left x

theorem hasCompactSupport_mol (m : ℕ) (x : E) : HasCompactSupport (mol n m x) :=
  HasCompactSupport.intro (isCompact_closedBall x (bump n m).rOut) fun _ hy =>
    mol_eq_zero (le_of_lt (by simpa [mem_closedBall] using hy))

theorem tsupport_mol_subset (m : ℕ) (x : E) : tsupport (mol n m x) ⊆ closedBall x (bump n m).rOut
    :=
  closure_minimal (fun _ hy => mem_closedBall.mpr (dist_lt_of_mol_ne_zero hy).le)
    isClosed_closedBall

/-- **The mollifier as a test function on `U`**, when the closed ball lies in `U`. -/
def bumpTest (U : Opens E) (m : ℕ) (x : E) (h : closedBall x (bump n m).rOut ⊆ U) : 𝓓(U, ℝ) where
  toFun := mol n m x
  contDiff' := contDiff_mol m x
  hasCompactSupport' := hasCompactSupport_mol m x
  tsupport_subset' := (tsupport_mol_subset m x).trans h

@[simp] theorem bumpTest_apply (U : Opens E) (m : ℕ) (x : E) (h : closedBall x (bump n m).rOut ⊆
    U) (y : E) :
    bumpTest U m x h y = mol n m x y := rfl

/-- Eventually the mollifier at a point of an open set is a test function on it. -/
theorem eventually_closedBall_subset {U : Opens E} {x : E} (hx : x ∈ U) :
    ∀ᶠ m in atTop, closedBall x (bump n m).rOut ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  filter_upwards [eventually_bump_rOut_lt (n := n) hε] with m hm
  exact (closedBall_subset_ball hm).trans hεU

end Mollifier

/-! ### Mollified functions and measures -/

section Differentiation

/-- **Lebesgue's differentiation theorem for the mollifiers, on an open set**: if `g` is
    integrable on a closed ball around
every point of the open set `U` inside `U`, then `∫ ρ_m(x - y) g(y) dy → g(x)` for almost every
    `x ∈ U`. -/
theorem ae_tendsto_integral_mol_mul {U : Set E} {g : E → ℝ}
    (hg : ∀ z ∈ U, ∃ r > 0, IntegrableOn g (closedBall z r)) :
    ∀ᵐ x, x ∈ U → Tendsto (fun m => ∫ y, mol n m x y * g y) atTop (𝓝 (g x)) := by
  refine ae_of_forall_ball fun z hz => ?_
  obtain ⟨r, hr, hgr⟩ := hg z hz
  refine ⟨r / 2, by positivity, ?_⟩
  set g' : E → ℝ := (closedBall z r).indicator g with hg'def
  have hg'i : Integrable g' := (integrable_indicator_iff measurableSet_closedBall).mpr hgr
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := (volume : Measure
    E))
    (φ := fun m => bump n m) (l := atTop) (K := 2) tendsto_bump_rOut
    (Eventually.of_forall fun m => bump_rOut_le m) hg'i.locallyIntegrable
  filter_upwards [h] with x hx hxz
  have hxz' : x ∈ closedBall z r := ball_subset_closedBall (ball_subset_ball (by linarith) hxz)
  have hgx : g' x = g x := indicator_of_mem hxz' g
  rw [hgx] at hx
  refine hx.congr' ?_
  filter_upwards [eventually_bump_rOut_lt (n := n) (half_pos hr)] with m hm
  rw [convolution_eq_swap]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  by_cases hy : mol n m x y = 0
  · simp only [mol] at hy ⊢
    rw [hy, zero_mul, zero_mul]
  · have hyx := dist_lt_of_mol_ne_zero hy
    have hyz : y ∈ closedBall z r := by
      rw [mem_closedBall]
      rw [mem_ball] at hxz
      linarith [dist_triangle y x z]
    rw [hg'def, indicator_of_mem hyz]
    rfl

/-- **The mollified values of a measure singular with respect to Lebesgue measure tend to `0`
    almost everywhere** on an open
set on whose compact subsets it is finite, also after multiplication by a bounded measurable
    function. -/
theorem ae_tendsto_integral_mol_singular {U : Set E} (hU : IsOpen U) {ν : Measure E} (hν : ν ⟂ₘ
    volume)
    (hfin : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) {f : E → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) :
    ∀ᵐ x, x ∈ U → Tendsto (fun m => ∫ y, mol n m x y * f y ∂ν) atTop (𝓝 0) := by
  refine ae_of_forall_ball fun z hz => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  set r := ε / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrU : closedBall z r ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  set νz : Measure E := ν.restrict (closedBall z r) with hνz
  have : IsFiniteMeasure νz := isFiniteMeasure_restrict.mpr (hfin _ (isCompact_closedBall z r)
    hrU).ne
  have hνzs : νz ⟂ₘ volume := hν.restrict _
  have hrn : νz.rnDeriv volume =ᵐ[volume] 0 := hνzs.rnDeriv_ae_eq_zero
  have hB := Besicovitch.ae_tendsto_rnDeriv νz (volume : Measure E)
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [hB, hrn] with x hx hx0 hxz
  rw [hx0, Pi.zero_apply] at hx
  -- the ratio along the radii `1/(m+1)`
  have hrad : Tendsto (fun m => (bump n m).rOut) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_bump_rOut, Eventually.of_forall fun m => (bump n
      m).rOut_pos⟩
  have hratio := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hx.comp hrad)
  simp only [ENNReal.toReal_zero, Function.comp_def] at hratio
  set K : ℝ := (2 : ℝ) ^ Module.finrank ℝ E with hK
  have hbound : Tendsto (fun m => |C| * K * (νz (closedBall x (bump n m).rOut) /
      volume (closedBall x (bump n m).rOut)).toReal) atTop (𝓝 0) := by
    simpa using hratio.const_mul (|C| * K)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_bump_rOut_lt (n := n) (half_pos hr)] with m hm
  have hsub : closedBall x (bump n m).rOut ⊆ closedBall z r := by
    intro y hy
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hxz
    linarith [dist_triangle y x z]
  -- the integrand vanishes off `closedBall x rOut ⊆ closedBall z r`
  have hint : ∫ y, mol n m x y * f y ∂ν = ∫ y, mol n m x y * f y ∂νz := by
    rw [hνz, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [mol_eq_zero, zero_mul]
    by_contra h
    exact hy (hsub (mem_closedBall.mpr (not_le.mp h).le))
  rw [hint, Real.norm_eq_abs]
  have hmolle : ∀ y, mol n m x y ≤ K / volume.real (closedBall x (bump n m).rOut) := by
    intro y
    have h := (bump n m).normed_le_div_measure_closedBall_rOut (μ := (volume : Measure E)) 2
      (bump_rOut_le m) (x - y)
    rwa [Measure.addHaar_real_closedBall_center volume (0 : E), ←
      Measure.addHaar_real_closedBall_center volume x]
      at h
  calc |∫ y, mol n m x y * f y ∂νz|
      ≤ ∫ y, |C| * ((K / volume.real (closedBall x (bump n m).rOut)) *
          (closedBall x (bump n m).rOut).indicator 1 y) ∂νz := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) ?_ (Eventually.of_forall fun y => ?_))
        · have hInd : Integrable ((closedBall x (bump n m).rOut).indicator
              (1 : E → ℝ)) νz :=
            (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
          exact (hInd.const_mul _).const_mul _
        · dsimp only
          rw [abs_mul, abs_of_nonneg (mol_nonneg m x y), mul_comm]
          by_cases hy : y ∈ closedBall x (bump n m).rOut
          · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
            exact mul_le_mul ((hf y).trans (le_abs_self C)) (hmolle y) (mol_nonneg m x y)
              (abs_nonneg C)
          · rw [indicator_of_notMem hy, mul_zero, mul_zero, mol_eq_zero, mul_zero]
            exact (not_le.mp (by simpa [mem_closedBall] using hy)).le
    _ = |C| * K * (νz.real (closedBall x (bump n m).rOut) / volume.real (closedBall x (bump n
      m).rOut)) := by
        rw [integral_const_mul, integral_const_mul, integral_indicator_one
          measurableSet_closedBall]
        ring
    _ = |C| * K * (νz (closedBall x (bump n m).rOut) / volume (closedBall x (bump n
      m).rOut)).toReal := by
        rw [ENNReal.toReal_div]
        rfl

end Differentiation

/-! ### Mollified values of a positive current -/

section Current

variable {U : Opens (ComplexModel n)} {q : ℕ}

attribute [local instance] addCommGroupFormSpan

/-- **The value of a positive current on a mollifier**: its absolutely continuous part,
    an integral against Lebesgue measure,
plus its singular part. -/
theorem apply_bumpTest {T : LocalProductCurrent n U q} (hT : IsPositive T) (γ : formSpan n q)
    {m : ℕ} {x : E}
    (h : closedBall x (bump n m).rOut ⊆ U) :
    T γ (bumpTest U m x h) = (∫ y, mol n m x y * (acWeight hT y * densityForm hT y γ)) +
      ∫ y, mol n m x y * densityForm hT y γ ∂(sgMeasure hT) := by
  conv_lhs => rw [← sgPart_add_acPart hT]
  rw [LinearMap.add_apply, _root_.add_apply, acPart_apply, sgPart, ofMeasure_apply, add_comm]
  rfl

/-- **The mollified values of a positive current converge almost everywhere to its absolutely
    continuous density**:
for every constant form `γ` and Lebesgue-almost every `x ∈ U`,
    `T(γ)(ρ_m(x - ·)) → (dσ_T/dλ)(x) L_x(γ)` (written through
`apply_bumpTest`, which holds as soon as the ball lies in `U`). -/
theorem ae_tendsto_apply_bumpTest {T : LocalProductCurrent n U q} (hT : IsPositive T)
    (γ : formSpan n q) :
    ∀ᵐ x, x ∈ U → Tendsto (fun m => (∫ y, mol n m x y * (acWeight hT y * densityForm hT y γ)) +
      ∫ y, mol n m x y * densityForm hT y γ ∂(sgMeasure hT)) atTop
      (𝓝 (acWeight hT x * densityForm hT x γ)) := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  have hac := ae_tendsto_integral_mol_mul (n := n) (U := (U : Set E))
    (g := fun y => acWeight hT y * densityForm hT y γ) fun z hz => by
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp U.isOpen z hz
      exact ⟨ε / 2, by positivity, (locallyIntegrableOn_acDensity hT γ).integrableOn_compact_subset
        ((closedBall_subset_ball (by linarith)).trans hεU) (isCompact_closedBall z _)⟩
  have hsg := ae_tendsto_integral_mol_singular (n := n) U.isOpen (sgMeasure_mutuallySingular hT)
    (fun K hK hKU => (Measure.le_iff'.mp (sgMeasure_le hT) K).trans_lt (hT.traceMeasure_lt_top hK
      hKU)) hC
  filter_upwards [hac, hsg] with x h1 h2 hx
  simpa using (h1 hx).add (h2 hx)

/-! ### The infimum functional and its semicontinuity -/

/-- **The infimum over `C` of the absolutely continuous density**:
    `inf_{c ∈ C} (dσ_T/dλ)(x) L_x(c)` in `ℝ≥0∞`.  For
`q = n - 1` and `C` the forms `β^{n-1}/n!` of the positive definite `(1,1)`-forms `β` with
    `β^n = ω₀^n` this is
`det(T_ac)^{1/n}` relative to `ω₀` (AM-GM). -/
def acInf {T : LocalProductCurrent n U q} (hT : IsPositive T) (C : Set (formSpan n q)) (x : E)
    : ℝ≥0∞ :=
  ⨅ c ∈ C, ENNReal.ofReal (acWeight hT x * densityForm hT x c)

variable {T : LocalProductCurrent n U q}

theorem acInf_le (hT : IsPositive T) {C : Set (formSpan n q)} {c : formSpan n q} (hc : c ∈ C)
    (x : E) :
    acInf hT C x ≤ ENNReal.ofReal (acWeight hT x * densityForm hT x c) :=
  biInf_le (fun c => ENNReal.ofReal (acWeight hT x * densityForm hT x c)) hc

/-- **The infimum over a set is the infimum over a dense subset** (the density form is
    continuous). -/
theorem acInf_eq_of_subset_closure (hT : IsPositive T) {C D : Set (formSpan n q)} (hDC : D ⊆ C)
    (hCD : C ⊆ closure D) (x : E) : acInf hT C x = acInf hT D x := by
  refine le_antisymm (biInf_mono hDC) (le_iInf₂ fun c hc => ?_)
  have hcont : Continuous fun c : formSpan n q => ENNReal.ofReal (acWeight hT x * densityForm hT x
    c) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (densityForm hT
      x).continuous_of_finiteDimensional)
  have hclosed : IsClosed {c : formSpan n q | acInf hT D x ≤ ENNReal.ofReal (acWeight hT x *
    densityForm hT x c)} :=
    isClosed_le continuous_const hcont
  exact closure_minimal (fun d hd => acInf_le hT hd x) hclosed (hCD hc)

theorem measurable_acInf (hT : IsPositive T) {D : Set (formSpan n q)} (hD : D.Countable)
    : Measurable (acInf hT D) :=
  Measurable.biInf D hD fun c _ => ENNReal.measurable_ofReal.comp ((measurable_acWeight hT).mul
    (measurable_densityForm hT c))

/-- **The mollified infimum is below the value of the current** (Boucksom's first two
    inequalities): for `c ∈ C` and a
mollifier `ρ` whose ball lies in `U`, `∫ ρ · inf_C T_ac ≤ T_ac(c)(ρ) ≤ T(c)(ρ)`. -/
theorem lintegral_mol_mul_acInf_le (hT : IsPositive T) {C : Set (formSpan n q)} (hC : C ⊆ posCone
    n q)
    {c : formSpan n q} (hc : c ∈ C) {m : ℕ} {x : E} (h : closedBall x (bump n m).rOut ⊆ U) :
    ∫⁻ y, ENNReal.ofReal (mol n m x y) * acInf hT C y ≤ ENNReal.ofReal (T c (bumpTest U m x h))
      := by
  have hsg : 0 ≤ sgPart hT c (bumpTest U m x h) :=
    (isPositive_sgPart hT).positiveDistribution (hC hc) _ fun y => mol_nonneg m x y
  have hTc : acPart hT c (bumpTest U m x h) ≤ T c (bumpTest U m x h) := by
    conv_rhs => rw [← sgPart_add_acPart hT]
    rw [LinearMap.add_apply, _root_.add_apply]
    linarith
  have hint : Integrable (fun y => mol n m x y * (acWeight hT y * densityForm hT y c)) := by
    have hK := (locallyIntegrableOn_acDensity hT c).integrableOn_compact_subset h
      (isCompact_closedBall x _)
    have h1 := hK.continuousOn_mul (continuous_mol m x).continuousOn (isCompact_closedBall x _)
    refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).mp h1
    exact mem_closedBall.mpr (dist_lt_of_mol_ne_zero (left_ne_zero_of_mul hy)).le
  have hnn : 0 ≤ᵐ[volume] fun y => mol n m x y * (acWeight hT y * densityForm hT y c) := by
    filter_upwards [ae_volume_acDensity_nonneg hT] with y hy
    exact mul_nonneg (mol_nonneg m x y) (hy c (hC hc))
  calc ∫⁻ y, ENNReal.ofReal (mol n m x y) * acInf hT C y
      ≤ ∫⁻ y, ENNReal.ofReal (mol n m x y * (acWeight hT y * densityForm hT y c)) := by
        refine lintegral_mono fun y => ?_
        rw [ENNReal.ofReal_mul (mol_nonneg m x y)]
        exact mul_le_mul_right (acInf_le hT hc y) _
    _ = ENNReal.ofReal (acPart hT c (bumpTest U m x h)) := by
        rw [acPart_apply, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
        rfl
    _ ≤ ENNReal.ofReal (T c (bumpTest U m x h)) := ENNReal.ofReal_le_ofReal hTc

/-- **Liminf estimate for the absolutely continuous part** (`ana:ac-density-liminf`): let
    positive currents
`T_k` of bidimension `(q,q)` on `U` converge weakly to the positive current `T` (`T_k(γ)(φ)
    → T(γ)(φ)` for every constant form
`γ` and every test function `φ`), and let `C` be a set of strongly positive constant forms.  Then
    for Lebesgue-almost every
`x ∈ U`, `liminf_k inf_{c ∈ C} T_{k,ac}(c)(x) ≤ inf_{c ∈ C} T_ac(c)(x)` (densities with respect to
    Lebesgue measure). -/
theorem ae_liminf_acInf_le {T : ℕ → LocalProductCurrent n U q} {T₀ : LocalProductCurrent n U q}
    (hT : ∀ k, IsPositive (T k)) (hT₀ : IsPositive T₀)
    (hconv : ∀ γ φ, Tendsto (fun k => T k γ φ) atTop (𝓝 (T₀ γ φ))) {C : Set (formSpan n q)}
    (hC : C ⊆ posCone n q) :
    ∀ᵐ x, x ∈ U → liminf (fun k => acInf (hT k) C x) atTop ≤ acInf hT₀ C x := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact Eventually.of_forall fun x _ => by simp [acInf]
  obtain ⟨D, hDC, hDc, hCD⟩ := (IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have hDne : D.Nonempty := by
    obtain ⟨c, hc⟩ := hCne
    by_contra hD
    rw [not_nonempty_iff_eq_empty] at hD
    have := hCD hc
    rw [hD, closure_empty] at this
    exact this
  obtain ⟨c₀, hc₀⟩ := hDne
  have hDP : D ⊆ posCone n q := hDC.trans hC
  simp_rw [acInf_eq_of_subset_closure _ hDC hCD]
  set G : E → ℝ≥0∞ := fun y => liminf (fun k => acInf (hT k) D y) atTop with hGdef
  have hGm : Measurable G := Measurable.liminf fun k => measurable_acInf (hT k) hDc
  -- Fatou: the mollified liminf is below the values of the limit current
  have hfatou : ∀ (z : E) (m : ℕ) (h : closedBall z (bump n m).rOut ⊆ U), ∀ c ∈ D,
      ∫⁻ y, ENNReal.ofReal (mol n m z y) * G y ≤ ENNReal.ofReal (T₀ c (bumpTest U m z h)) := by
    intro z m h c hc
    calc ∫⁻ y, ENNReal.ofReal (mol n m z y) * G y
        = ∫⁻ y, liminf (fun k => ENNReal.ofReal (mol n m z y) * acInf (hT k) D y) atTop := by
          refine lintegral_congr fun y => ?_
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (mol n m z y) * acInf (hT k) D y) atTop :=
          lintegral_liminf_le fun k =>
            (ENNReal.measurable_ofReal.comp (continuous_mol m z).measurable).mul (measurable_acInf
              (hT k) hDc)
      _ ≤ liminf (fun k => ENNReal.ofReal (T k c (bumpTest U m z h))) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => lintegral_mol_mul_acInf_le (hT k)
            hDP hc h)
      _ = ENNReal.ofReal (T₀ c (bumpTest U m z h)) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp (hconv c _)).liminf_eq
  -- the liminf is integrable on small closed balls around every point of `U`
  have hGloc : ∀ z ∈ (U : Set E), ∃ r > 0, ∫⁻ y in closedBall z r, G y ≠ ⊤ := by
    intro z hz
    obtain ⟨m, hm⟩ := (eventually_closedBall_subset (n := n) hz).exists
    refine ⟨(bump n m).rIn, (bump n m).rIn_pos, ?_⟩
    set a : ℝ := 1 / ∫ y, (bump n m) y ∂(volume : Measure E) with hadef
    have ha : 0 < a := one_div_pos.mpr (bump n m).integral_pos
    have hmol : ∀ y ∈ closedBall z (bump n m).rIn, mol n m z y = a := by
      intro y hy
      rw [mol, ContDiffBump.normed_def, (bump n m).one_of_mem_closedBall, hadef]
      rw [mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm]
      exact mem_closedBall.mp hy
    have h0 : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr ha
    refine ne_top_of_le_ne_top (b := (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (T₀ c₀ (bumpTest U m z
      hm)))
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h0) ENNReal.ofReal_ne_top) ?_
    calc ∫⁻ y in closedBall z (bump n m).rIn, G y
        ≤ ∫⁻ y in closedBall z (bump n m).rIn, (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (mol n m z
          y) * G y) := by
          refine setLIntegral_mono' measurableSet_closedBall fun y hy => ?_
          rw [hmol y hy, ← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ ∫⁻ y, (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (mol n m z y) * G y) :=
        setLIntegral_le_lintegral _ _
      _ = (ENNReal.ofReal a)⁻¹ * ∫⁻ y, ENNReal.ofReal (mol n m z y) * G y :=
          lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp (continuous_mol m
            z).measurable).mul hGm)
      _ ≤ (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (T₀ c₀ (bumpTest U m z hm)) := by
          gcongr
          exact hfatou z m hm c₀ hc₀
  choose! r hr hGr using hGloc
  -- almost everywhere on `U`: `G` is finite, and its mollifications converge to it
  have hGfin : ∀ᵐ x, x ∈ U → G x < ⊤ := by
    refine ae_of_forall_ball fun z hz => ⟨r z, hr z hz, ?_⟩
    have h := ae_lt_top hGm (hGr z hz)
    rw [ae_restrict_iff' measurableSet_closedBall] at h
    filter_upwards [h] with x hx hxz
    exact hx (ball_subset_closedBall hxz)
  have hGconv := ae_tendsto_integral_mol_mul (n := n) (U := (U : Set E)) (g := fun y => (G
    y).toReal)
    fun z hz => ⟨r z, hr z hz, integrable_toReal_of_lintegral_ne_top hGm.aemeasurable (hGr z hz)⟩
  have hT₀conv : ∀ᵐ x, ∀ c ∈ D, x ∈ U → Tendsto (fun m => (∫ y, mol n m x y * (acWeight hT₀ y *
    densityForm hT₀ y c)) +
      ∫ y, mol n m x y * densityForm hT₀ y c ∂(sgMeasure hT₀)) atTop (𝓝 (acWeight hT₀ x *
        densityForm hT₀ x c)) :=
    (ae_ball_iff hDc).mpr fun c _ => ae_tendsto_apply_bumpTest hT₀ c
  filter_upwards [hGfin, hGconv, hT₀conv] with x hfin hconvG hconvT hx
  refine le_iInf₂ fun c hc => ?_
  change G x ≤ _
  rw [← ENNReal.ofReal_toReal (hfin hx).ne]
  refine ENNReal.ofReal_le_ofReal (le_of_tendsto_of_tendsto (hconvG hx) (hconvT c hc hx) ?_)
  filter_upwards [eventually_closedBall_subset (n := n) hx] with m hm
  have hpos : 0 ≤ T₀ c (bumpTest U m x hm) :=
    hT₀.positiveDistribution (hDP hc) _ fun y => mol_nonneg m x y
  have hlin : ∫⁻ y, ENNReal.ofReal (mol n m x y) * G y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfatou x m hm c hc)
  rw [← apply_bumpTest hT₀ c hm]
  calc ∫ y, mol n m x y * (G y).toReal
      = (∫⁻ y, ENNReal.ofReal (mol n m x y * (G y).toReal)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => mul_nonneg (mol_nonneg m
          x y)
          ENNReal.toReal_nonneg) ((continuous_mol m x).measurable.mul
            hGm.ennreal_toReal).aestronglyMeasurable
    _ ≤ (∫⁻ y, ENNReal.ofReal (mol n m x y) * G y).toReal := by
        refine ENNReal.toReal_mono hlin (lintegral_mono fun y => ?_)
        rw [ENNReal.ofReal_mul (mol_nonneg m x y)]
        exact mul_le_mul_right ENNReal.ofReal_toReal_le _
    _ ≤ (ENNReal.ofReal (T₀ c (bumpTest U m x hm))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfatou x m hm c hc)
    _ = T₀ c (bumpTest U m x hm) := ENNReal.toReal_ofReal hpos

end Current

end SGPT.Foundations.Analysis.Pending.LocalCurrentSemicontinuity
