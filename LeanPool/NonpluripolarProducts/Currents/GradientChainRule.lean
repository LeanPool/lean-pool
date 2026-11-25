/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Currents.GradientCauchySchwarz

/-!
# Chain rule, gradient energy and the cutoff estimate against closed positive currents

Source: Xia, *Foundations of pluripotential theory*, `lem:bounded-psh-current-chain-rule`
(`eq:bounded-current-chain-rule`, `eq:bounded-current-gradient-measure`,
`eq:current-gradient-cauchy-schwarz`) and the gradient bound in the proof of
`thm:nonpluripolar-product-closed`.

Let `T` be a positive **closed** current of bidimension `(q+1,q+1)` on an open `U ⊆ ℂⁿ`,
`γ` a constant strongly positive `(q,q)`-form, `ℓ` a real linear form and `φ` a test function.
Closedness of `T` is tested on the forms `d(ψ ℓ ∧ γ)`, whose `(q+1,q+1)`-part is
`∑_a ∂_a ψ γ ∧ Π₁₁(e^a ∧ ℓ)` (`IsClosedCurrent`).  For a cutoff `c = ζ ∘ w` we estimate the
*closedness defect*
`D_T(c) = ∑_a ⟨c T, ∂_a φ γ ∧ Π₁₁(e^a ∧ ℓ)⟩ = ∑_a ∫ ∂_a φ · c · L_x(γ ∧ Π₁₁(e^a ∧ ℓ)) dσ_T`,
the pairing of `d(c T)` with `φ ℓ ∧ γ`.

* `sum_integral_dTest_mul_comp` — **the chain rule** `d(ζ(g) T) = ζ'(g) dg ∧ T` for smooth `g`:
  `D_T(ζ ∘ g) = ∫ φ ζ'(g) L_x(Q(∂g, η_ℓ)) dσ_T`.
* `integral_mul_densityForm_quadForm_grad_le` — **the gradient energy bound**: for smooth `g ≥ 0`
  psh near the support of `τ ≥ 0`,
  `∫ τ dg ∧ d^c g ∧ γ ∧ T ≤ ½ ∫ g² |dd^c τ| ∧ γ ∧ T`, from
  `dg ∧ d^c g ∧ T = ½ dd^c(g² T) - g dd^c g ∧ T` (FPT `eq:bounded-current-gradient-measure`)
  and `g dd^c g ∧ T ≥ 0`.
* `abs_sum_integral_le_of_contDiff` — **the Cauchy–Schwarz estimate**
  `|D_T(ζ ∘ g)| ≤ (t/4) ∫ g² A_τ dσ_T + (1/2t) ∫ φ² ζ'(g)² L_x(Q(η_ℓ, η_ℓ)) dσ_T` for `t > 0`,
  where `τ = 1` on the support of `φ` and `A_τ = ∑ |∂_b∂_a τ| |L_x(γ ∧ P_{ab})|`.
* `abs_sum_integral_le` — the same estimate for **locally bounded psh** `w ≥ 0`
  (FPT `eq:current-gradient-cauchy-schwarz` with `a = ζ'(w)`, combined with the gradient bound),
  by decreasing smooth psh approximation `w_j ↓ w` (TN's
  `exists_decreasingMollifierApproximation`) and dominated convergence in each term.  In contrast
  to FPT we never need the limit current `dw ∧ T` itself: the estimate is applied to the
  approximants and only the three integrals in it are passed to the limit.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Currents.Gradient

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Calculus of smooth functions in coordinates -/

section Calculus

/-- The coordinate gradient `(∂_a g(x))_a` in the real basis. -/
def gradVec (g : (ComplexModel n) → ℝ) (x : (ComplexModel n)) : Fin (n * 2) → ℝ := fun a => dFun
    (realBasis n a) g x

theorem dFun_comp {ζ : ℝ → ℝ} {g : (ComplexModel n) → ℝ} (hζ : Differentiable ℝ ζ)
    (hg : Differentiable ℝ g)
    (v x : (ComplexModel n)) : dFun v (fun y => ζ (g y)) x = deriv ζ (g x) * dFun v g x := by
  have h : HasFDerivAt (fun y => ζ (g y)) (deriv ζ (g x) • fderiv ℝ g x) x :=
    (hζ (g x)).hasDerivAt.comp_hasFDerivAt x (hg x).hasFDerivAt
  simp only [dFun, h.fderiv, _root_.smul_apply, smul_eq_mul]

theorem hessFun_mul_self {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Fin (n * 2))
    (x : (ComplexModel n)) :
    hessFun a b (fun y => g y * g y) x =
      2 * (dFun (realBasis n a) g x * dFun (realBasis n b) g x) + 2 * (g x * hessFun a b g x) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hdb : Differentiable ℝ (dFun (realBasis n b) g) :=
    (contDiff_dFun hg _).differentiable (by simp)
  have h1 : dFun (realBasis n b) (fun y => g y * g y) =
      fun y => dFun (realBasis n b) g y * g y + g y * dFun (realBasis n b) g y := by
    funext y
    have hy : HasFDerivAt (fun y => g y * g y) (g y • fderiv ℝ g y + g y • fderiv ℝ g y) y :=
      (hd y).hasFDerivAt.mul (hd y).hasFDerivAt
    simp only [dFun, hy.fderiv, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have h2 : HasFDerivAt (fun y => dFun (realBasis n b) g y * g y + g y * dFun (realBasis n b) g y)
      ((dFun (realBasis n b) g x • fderiv ℝ g x + g x • fderiv ℝ (dFun (realBasis n b) g) x) +
        (g x • fderiv ℝ (dFun (realBasis n b) g) x + dFun (realBasis n b) g x • fderiv ℝ g x)) x :=
    ((hdb x).hasFDerivAt.mul (hd x).hasFDerivAt).add ((hd x).hasFDerivAt.mul (hdb x).hasFDerivAt)
  change dFun (realBasis n a) (dFun (realBasis n b) (fun y => g y * g y)) x = _
  rw [h1]
  change fderiv ℝ (fun y => dFun (realBasis n b) g y * g y + g y * dFun (realBasis n b) g y) x
    (realBasis n a) = _
  rw [h2.fderiv]
  simp only [hessFun, dFun, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

end Calculus

/-! ### Double sums of integrals -/

theorem integral_sum_sum {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
    [Fintype κ] {f : ι → κ → α → ℝ} (hf : ∀ i j, Integrable (f i j) μ) :
    ∫ x, ∑ i, ∑ j, f i j x ∂μ = ∑ i, ∑ j, ∫ x, f i j x ∂μ := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf i j]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hf i j

/-! ### The chain rule against a closed current -/

section ChainRule

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U (q + 1)}

/-- **The chain rule** `d(ζ(g) T) = ζ'(g) dg ∧ T` for a closed current `T` and smooth `g`, `ζ`,
tested against `φ ℓ ∧ γ`: `D_T(ζ ∘ g) = ∫ φ ζ'(g) L_x(Q(∂g, η_ℓ)) dσ_T`. -/
theorem sum_integral_dTest_mul_comp (hT : IsPositive T) (hTc : IsClosedCurrent T)
    (γ : formSpan n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (φ : 𝓓(U, ℝ)) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞
      ζ)
    {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∑ a, ∫ x, dTest (realBasis n a) φ x * (ζ (g x) * densityForm hT x (testWedge γ ℓ a))
        ∂hT.traceMeasure =
      ∫ x, φ x * deriv ζ (g x) * densityForm hT x (quadForm q γ (gradVec g x) (dualCoeff ℓ))
        ∂hT.traceMeasure := by
  have hc : ContDiff ℝ ∞ (fun y => ζ (g y)) := hζ.comp hg
  have hclosed := hTc.apply_eq_zero ℓ γ (mulTest hc φ)
  simp only [dTest_mulTest, map_add, Finset.sum_add_distrib] at hclosed
  have hL : ∀ a, ∫ x, dTest (realBasis n a) φ x * (ζ (g x) * densityForm hT x (testWedge γ ℓ a))
      ∂hT.traceMeasure = T (testWedge γ ℓ a) (mulTest hc (dTest (realBasis n a) φ)) := by
    intro a
    rw [apply_eq_integral_densityForm hT]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [mulTest_apply]
    ring
  have hR : ∀ a, T (testWedge γ ℓ a) (mulTest (contDiff_dFun hc (realBasis n a)) φ) =
      ∫ x, φ x * deriv ζ (g x) * (gradVec g x a * densityForm hT x (testWedge γ ℓ a))
        ∂hT.traceMeasure := by
    intro a
    rw [apply_eq_integral_densityForm hT]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [mulTest_apply, gradVec,
      dFun_comp (hζ.differentiable (by simp)) (hg.differentiable (by simp))]
    ring
  simp_rw [hL]
  have e : ∑ a, T (testWedge γ ℓ a) (mulTest hc (dTest (realBasis n a) φ)) =
      -∑ a, T (testWedge γ ℓ a) (mulTest (contDiff_dFun hc (realBasis n a)) φ) := by
    change ∑ a, T (testWedge γ ℓ a) (mulTest hc (dTest (realBasis n a) φ)) +
      ∑ a, T (testWedge γ ℓ a) (mulTest (contDiff_dFun hc (realBasis n a)) φ) = 0 at hclosed
    linarith
  rw [e]
  simp_rw [hR]
  rw [← integral_finsetSum, ← integral_neg]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Finset.mul_sum, sum_mul_densityForm_testWedge]
    ring
  · intro a _
    have h := (integrable_densityForm hT le_rfl (testWedge γ ℓ a)
      (mulTest (contDiff_dFun hc (realBasis n a)) φ))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [mulTest_apply, gradVec,
      dFun_comp (hζ.differentiable (by simp)) (hg.differentiable (by simp))]
    ring

end ChainRule

/-! ### The gradient energy -/

section Energy

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U (q + 1)}

/-- The weight `A_τ(x) = ∑_{a,b} |∂_b∂_a τ(x)| |L_x(γ ∧ P_{ab})|` (a bound for the coefficients of
`dd^c τ ∧ γ ∧ T`). -/
def hessWeight (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ)) (x : (ComplexModel n)) : ℝ :=
  ∑ a, ∑ b, |dTest (realBasis n b) (dTest (realBasis n a) τ) x| *
    |densityForm hT x (coeffWedge γ a b)|

theorem hessWeight_nonneg (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ)) (x : (ComplexModel
    n)) :
    0 ≤ hessWeight hT γ τ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem hessWeight_eq_zero (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ))
    {x : (ComplexModel n)}
    (hx : x ∉ tsupport τ) : hessWeight hT γ τ x = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have h : x ∉ tsupport (dTest (realBasis n b) (dTest (realBasis n a) τ)) := fun h =>
    hx (((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)) h)
  rw [image_eq_zero_of_notMem_tsupport h, abs_zero, zero_mul]

theorem measurable_hessWeight (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ)) :
    Measurable (hessWeight hT γ τ) := by
  unfold hessWeight
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (continuous_abs.measurable.comp
    (dTest (realBasis n b) (dTest (realBasis n a) τ)).continuous.measurable).mul
    (continuous_abs.measurable.comp (measurable_densityForm hT _))

theorem integrable_hessWeight (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ)) :
    Integrable (hessWeight hT γ τ) hT.traceMeasure := by
  unfold hessWeight
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  set ψ := dTest (realBasis n b) (dTest (realBasis n a) τ)
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT (coeffWedge γ a b)
  have h := hT.integrable_mul_of_bounded (ψ := fun x => |ψ x|) (w := fun x =>
    |densityForm hT x (coeffWedge γ a b)|) ψ.continuous.abs ψ.hasCompactSupport.abs
    ((tsupport_comp_subset (abs_zero (α := ℝ)) _).trans ψ.tsupport_subset)
    (continuous_abs.measurable.comp (measurable_densityForm hT _)).aestronglyMeasurable
    ⟨C, fun x _ => by rw [abs_abs]; exact hC x⟩
  exact h

/-- `L_x(Q(ξ, ξ)) τ` as a sum of coefficient integrands of `T` against test functions. -/
theorem mul_densityForm_quadForm_grad_eq (hT : IsPositive T) (γ : formSpan n q) (τ : 𝓓(U, ℝ))
    {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) (x : (ComplexModel n)) :
    τ x * densityForm hT x (quadForm q γ (gradVec g x) (gradVec g x)) =
      ∑ a, ∑ b, -(mulTest ((contDiff_dFun hg (realBasis n a)).mul (contDiff_dFun hg
        (realBasis n b))) τ x * densityForm hT x (coeffWedge γ a b)) := by
  rw [densityForm_quadForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mulTest_apply, gradVec]
  ring

theorem integrable_mul_densityForm_quadForm_grad (hT : IsPositive T) (γ : formSpan n q)
    (τ : 𝓓(U, ℝ)) {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) :
    Integrable (fun x => τ x * densityForm hT x (quadForm q γ (gradVec g x) (gradVec g x)))
      hT.traceMeasure := by
  have h := integrable_finsetSum (μ := hT.traceMeasure) Finset.univ fun a _ =>
    integrable_finsetSum Finset.univ fun b _ =>
      (integrable_densityForm hT le_rfl (coeffWedge γ a b) (mulTest ((contDiff_dFun hg
        (realBasis n a)).mul (contDiff_dFun hg (realBasis n b))) τ)).fun_neg
  refine h.congr (Eventually.of_forall fun x => ?_)
  exact (mul_densityForm_quadForm_grad_eq hT γ τ hg x).symm

/-- **The gradient energy bound** (FPT `eq:bounded-current-gradient-measure` and the gradient
bound in `thm:nonpluripolar-product-closed`): for a closed positive `T`, a test function `τ ≥ 0`
and a smooth `g`, nonnegative and psh at the points of the support of `τ`,
`∫ τ L_x(Q(∂g, ∂g)) dσ_T ≤ ½ ∫ g² A_τ dσ_T`. -/
theorem integral_mul_densityForm_quadForm_grad_le (hT : IsPositive T) (hTc : IsClosedCurrent T)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (τ : 𝓓(U, ℝ)) (hτ0 : ∀ x, 0 ≤ τ x)
    {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ tsupport τ, 0 ≤ g x)
    (hgp : ∀ x ∈ tsupport τ, IsSemipositiveOneOne (smoothDDC g x)) :
    ∫ x, τ x * densityForm hT x (quadForm q γ (gradVec g x) (gradVec g x)) ∂hT.traceMeasure ≤
      1 / 2 * ∫ x, g x ^ 2 * hessWeight hT γ τ x ∂hT.traceMeasure := by
  set σ := hT.traceMeasure
  have hg2 : ContDiff ℝ ∞ (fun y => g y * g y) := hg.mul hg
  have hp : ∀ a b : Fin (n * 2), ContDiff ℝ ∞
      (fun y => dFun (realBasis n a) g y * dFun (realBasis n b) g y) := fun a b =>
    (contDiff_dFun hg _).mul (contDiff_dFun hg _)
  -- Step 1: the integral as a sum of values of `T`
  have h1 : ∫ x, τ x * densityForm hT x (quadForm q γ (gradVec g x) (gradVec g x)) ∂σ =
      ∑ a, ∑ b, -(T (coeffWedge γ a b) (mulTest (hp a b) τ)) := by
    set G : Fin (n * 2) → Fin (n * 2) → (ComplexModel n) → ℝ := fun a b x =>
      -(mulTest (hp a b) τ x * densityForm hT x (coeffWedge γ a b)) with hG
    calc ∫ x, τ x * densityForm hT x (quadForm q γ (gradVec g x) (gradVec g x)) ∂σ =
          ∫ x, ∑ a, ∑ b, G a b x ∂σ :=
          integral_congr_ae (Eventually.of_forall fun x =>
            mul_densityForm_quadForm_grad_eq hT γ τ hg x)
      _ = ∑ a, ∑ b, ∫ x, G a b x ∂σ :=
          integral_sum_sum fun a b => (integrable_densityForm hT le_rfl _ _).fun_neg
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hG, integral_neg, apply_eq_integral_densityForm hT]
  -- Step 2: `∂_a g ∂_b g = ½ ∂_a∂_b(g²) - g ∂_a∂_b g`
  have h2 : ∀ a b, mulTest (hp a b) τ = (1 / 2 : ℝ) • mulTest (contDiff_hessFun hg2 a b) τ -
      mulTest (contDiff_hessFun hg a b) (mulTest hg τ) := by
    intro a b
    ext x
    simp only [mulTest_apply, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hessFun_mul_self hg a b x]
    ring
  -- Step 3: the term `g dd^c g ∧ γ ∧ T` is positive
  have h3 : ∑ a, ∑ b, T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg a b) (mulTest hg τ)) ≤
      0 := by
    have h := IsPositive.sum_hess_nonneg hT hg (fun _ : Unit => γ) (fun _ => mulTest hg τ)
      (fun x => by
        simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
          mulTest_apply]
        refine smul_mem_spCone hγ ?_
        by_cases hx : x ∈ tsupport τ
        · exact mul_nonneg (hτ0 x) (hg0 x hx)
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      (fun x ⟨_, hx⟩ => by
        simp only [mulTest_apply] at hx
        exact hgp x (subset_tsupport _ (left_ne_zero_of_mul hx)))
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
    simp_rw [← Finset.mul_sum] at h
    have hc : -(1 / (4 * Real.pi)) < 0 := by
      have : 0 < 1 / (4 * Real.pi) := by positivity
      linarith
    exact nonpos_of_mul_nonneg_right h hc
  -- Step 4: integration by parts in `dd^c(g²) ∧ γ ∧ T`
  set F : Fin (n * 2) → Fin (n * 2) → (ComplexModel n) → ℝ := fun a b x =>
    (dTest (realBasis n b) (dTest (realBasis n a) τ) x * (g x * g x)) *
      densityForm hT x (coeffWedge γ a b) with hF
  have h4 : ∑ a, ∑ b, T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg2 a b) τ) =
      ∑ a, ∑ b, ∫ x, F a b x ∂σ := by
    rw [show (∑ a, ∑ b, T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg2 a b) τ)) =
        ∑ a, ∑ b, T (wedgeLM q (isOneOne_coeffForm a b) γ) (mulTest (contDiff_hessFun hg2 a b) τ)
        from rfl, ← hTc.sum_mulTest_dTest hg2 γ τ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [apply_eq_integral_densityForm hT]
    rfl
  -- Step 5: the bound by the Hessian weight
  have hint : ∀ a b, Integrable (F a b) σ := fun a b =>
    integrable_densityForm hT le_rfl (coeffWedge γ a b)
      (mulTest hg2 (dTest (realBasis n b) (dTest (realBasis n a) τ)))
  have h5 : -(∑ a, ∑ b, ∫ x, F a b x ∂σ) ≤ ∫ x, g x ^ 2 * hessWeight hT γ τ x ∂σ := by
    have e : ∫ x, g x ^ 2 * hessWeight hT γ τ x ∂σ = ∫ x, ∑ a, ∑ b, |F a b x| ∂σ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hessWeight, Finset.mul_sum, hF]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [abs_mul, abs_mul, abs_mul_self]
      ring
    rw [e, integral_sum_sum fun a b => (hint a b).abs, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun b _ => (neg_le_abs _).trans (abs_integral_le_integral_abs)
  rw [h1]
  simp_rw [h2, map_sub, map_smul, smul_eq_mul]
  have e : ∑ a, ∑ b, -(1 / 2 * T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg2 a b) τ) -
      T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg a b) (mulTest hg τ))) =
      -(1 / 2 * ∑ a, ∑ b, T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg2 a b) τ)) +
        ∑ a, ∑ b, T (coeffWedge γ a b) (mulTest (contDiff_hessFun hg a b) (mulTest hg τ)) := by
    simp only [neg_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [e, h4]
  nlinarith [h3, h5]

end Energy

end SGPT.Currents.Gradient
