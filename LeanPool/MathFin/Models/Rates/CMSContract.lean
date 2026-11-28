/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Caplet
public import LeanPool.MathFin.Models.Rates.CMS

/-!
# CMS contracts, priced under the annuity measure

A **constant-maturity swap** pays, at a fixing date `T₀`, the then-prevailing par swap rate
`S = (P(T₀, T₀) − P(T₀, Tₙ)) / A(T₀)` of a swap on the dates `T 1, …, T n`, with annuity
`A = δ Σᵢ P(T₀, Tᵢ)`. `S` is a quotient whose meaning needs a positive annuity, so `Payoff` has no
division node: the swap rate is an **observed underlying** `σ`, and `SwapModel` ties it to the bond
prices `P(T₀, Tᵢ)` (observed processes, versions of `bondPrice` of the stochastic discount factor)
and to the annuity, as `BondModel` does for the forward rate of a caplet.

* The CMS caplet, floorlet and swaplet (`cmsCaplet`, `cmsFloorlet`, `cmsSwaplet`) are one-cash-flow
  contracts on `σ`.
* **Annuity-measure pricing.** A payoff `g(S)` paid at `T₀` is worth `A(0) · 𝔼^A[g(S) / A(T₀)]`
  (`value_pay_swapRate`), where `𝔼^A` is the annuity measure `swapAnnuityMeasure` and
  `A(0) = δ Σ P(0, Tᵢ)` is the annuity of the zero curve. This is `annuityMeasure_price`
  (`Models/Rates/CMS.lean`) for the discount factor `D (T 0)`.
* **The forward swap rate is the annuity-measure mean of the swap rate**
  (`SwapModel.integral_swapRate`): `𝔼^A[S] = (P(0, T₀) − P(0, Tₙ)) / A(0)`, the par rate of the
  zero curve. The annuity repricing condition `𝔼[D · A(T₀)] = A(0)` that makes `Qᴬ` a probability
  is the tower property (`SwapModel.integral_annuity_mul`), not a hypothesis.

## What is not here

The swap rate is tied to the bond prices by a hypothesis (`rate_eq`) and the bond prices by
`hasBondPrice`; no term-structure model is asserted. Payments at `T₀` only: a CMS rate paid at a
later date `Tₚ` needs the change of measure to the `Tₚ`-forward measure.

## Main definitions

* `cmsCaplet`, `cmsFloorlet`, `cmsSwaplet`, `swapCurve`, `SwapModel`, `swapAnnuityMeasure`.

## Main results

* `SwapModel.integral_annuity_mul`,
  `SwapModel.isProbabilityMeasure`, `value_pay_swapRate`, `value_cmsCaplet`,
  `value_cmsFloorlet`, `value_cmsSwaplet`, `SwapModel.integral_swapRate`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  sections 1.6 and 13.8
* [P. S. Hagan, *Convexity conundrums: pricing CMS swaps, caps, and floors*][Hagan2003]
* [Musiela and Rutkowski, *Martingale Methods in Financial Modelling*][MusielaRutkowski], ch. 13

## Tags

constant maturity swap, CMS caplet, annuity measure, swap measure, par swap rate, swaption,
MSC 91G30, JEL G12, JEL E43
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The contracts and the model -/

/-- A **CMS caplet**: pays `(S − K)⁺` at the fixing date `T₀`, where the underlying `σ` carries the
par swap rate `S`, observed at `T₀`. -/
noncomputable def cmsCaplet (σ : ι) (T₀ : ℝ≥0) (K : ℝ) : Contract ι :=
  .pay T₀ (.max (.sub (.obs σ T₀) (.const K)) (.const 0))

/-- A **CMS floorlet**: pays `(K − S)⁺` at the fixing date `T₀`. -/
noncomputable def cmsFloorlet (σ : ι) (T₀ : ℝ≥0) (K : ℝ) : Contract ι :=
  .pay T₀ (.max (.sub (.const K) (.obs σ T₀)) (.const 0))

/-- A **CMS swaplet**: pays the par swap rate `S` at the fixing date `T₀`. -/
noncomputable def cmsSwaplet (σ : ι) (T₀ : ℝ≥0) : Contract ι :=
  .pay T₀ (.obs σ T₀)

/-- The curve state at the fixing date: `ω ↦ (i ↦ P(T₀, Tᵢ))`, read off the observed bond prices
`b i`. -/
def swapCurve (X : ι → ℝ≥0 → Ω → ℝ) (b : ℕ → ι) (T₀ : ℝ≥0) : Ω → ℕ → ℝ :=
  fun ω i ↦ X (b i) T₀ ω

/-- **A model with a swap rate.** The underlying `b i` carries the bond price `P(T₀, Tᵢ)` at
`T₀ = T 0`, for the payment dates `i = 1, …, n`: a (positive, measurable) version of `bondPrice`
of the stochastic discount factor `D` (`HasBondPrice`), whose value at the fixing date is positive
and integrable. The underlying
`σ` carries the par swap rate at `T₀`, which is the par rate `(1 − P(T₀, Tₙ))/A` of the annuity
`A = δ Σᵢ P(T₀, Tᵢ)` (`parSwapRate`, `annuityRandom`) almost surely. -/
structure SwapModel (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (σ : ι) (b : ℕ → ι) (T : ℕ → ℝ≥0) (n : ℕ) (δ : ℝ) : Prop where
  δ_pos : 0 < δ
  n_pos : 0 < n
  hasBondPrice : ∀ i ∈ Finset.Icc 1 n, HasBondPrice Q 𝓕 D X (b i) (T 0) (T i)
  D_meas : Measurable (D (T 0))
  integrable_D0 : Integrable (D (T 0)) Q
  bond_pos : ∀ ω, ∀ i ∈ Finset.Icc 1 n, 0 < X (b i) (T 0) ω
  bond_meas : ∀ i ∈ Finset.Icc 1 n, Measurable (X (b i) (T 0))
  rate_eq : X σ (T 0) =ᵐ[Q] fun ω ↦ parSwapRate 1 (X (b n) (T 0) ω)
    (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)

/-- **The annuity measure of a swap model**: `CMS.annuityMeasure` for the discount factor `D (T 0)`
and the curve `P(T₀, ·)`, normalised by the annuity `A(0) = δ Σᵢ P(0, Tᵢ)` of the zero curve. -/
noncomputable def swapAnnuityMeasure (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ) (X : ι → ℝ≥0 → Ω → ℝ)
    (b : ℕ → ι) (T : ℕ → ℝ≥0) (n : ℕ) (δ : ℝ) : Measure Ω :=
  CMS.annuityMeasure Q (D (T 0)) δ (swapCurve X b (T 0)) (Finset.Icc 1 n)
    (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {σ : ι} {b : ℕ → ι} {T : ℕ → ℝ≥0} {n : ℕ} {δ : ℝ}

/-! ### The tower property, for the curve -/

omit [IsProbabilityMeasure Q] in
theorem SwapModel.D_pos (h : SwapModel Q 𝓕 D X σ b T n δ) (ω : Ω) : 0 < D (T 0) ω :=
  (h.hasBondPrice 1 (Finset.mem_Icc.2 ⟨le_rfl, h.n_pos⟩)).D_pos ω

omit [IsProbabilityMeasure Q] in
theorem SwapModel.annuity_pos (h : SwapModel Q 𝓕 D X σ b T n δ) (ω : Ω) :
    0 < CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω :=
  MathFin.annuity_pos h.δ_pos (fun i hi ↦ h.bond_pos ω i hi)
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, h.n_pos⟩⟩

omit [IsProbabilityMeasure Q] in
theorem SwapModel.annuity_meas (h : SwapModel Q 𝓕 D X σ b T n δ) :
    Measurable (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n)) :=
  (Finset.measurable_sum _ h.bond_meas).const_mul δ

omit [IsProbabilityMeasure Q] in
theorem SwapModel.integrable_annuity_mul (h : SwapModel Q 𝓕 D X σ b T n δ) :
    Integrable (fun ω ↦ CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
      * D (T 0) ω) Q := by
  have := (integrable_finsetSum _ fun i hi ↦
      (h.hasBondPrice i hi).integrable_discount_mul).const_mul δ
  refine this.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [CMS.annuityRandom, annuity, swapCurve]
  rw [mul_assoc, Finset.sum_mul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)

/-- **The annuity repricing condition is the tower property**: `𝔼[D (T 0) · A(T₀)] = A(0)`, the
annuity `δ Σᵢ P(0, Tᵢ)` of the zero curve. -/
theorem SwapModel.integral_annuity_mul (h : SwapModel Q 𝓕 D X σ b T n δ) :
    ∫ ω, CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω * D (T 0) ω ∂Q
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n) := by
  have e : ∀ ω, CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω * D (T 0) ω
      = δ * ∑ i ∈ Finset.Icc 1 n, D (T 0) ω * X (b i) (T 0) ω := fun ω ↦ by
    simp only [CMS.annuityRandom, annuity, swapCurve]
    rw [mul_assoc, Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)
  simp_rw [e]
  rw [integral_const_mul, integral_finsetSum _ fun i hi ↦
      (h.hasBondPrice i hi).integrable_discount_mul,
    annuity]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦ (h.hasBondPrice i hi).integral_discount)

theorem SwapModel.annuity0_pos (h : SwapModel Q 𝓕 D X σ b T n δ) :
    0 < annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n) := by
  rw [← h.integral_annuity_mul]
  refine (integral_pos_iff_support_of_nonneg (fun ω ↦ ?_) h.integrable_annuity_mul).2 ?_
  · exact (mul_pos (h.annuity_pos ω) (h.D_pos ω)).le
  · rw [show Function.support _ = Set.univ from Set.eq_univ_of_forall fun ω ↦
      (mul_pos (h.annuity_pos ω) (h.D_pos ω)).ne']
    simp

/-- **The annuity measure of a swap model is a probability measure.** -/
theorem SwapModel.isProbabilityMeasure (h : SwapModel Q 𝓕 D X σ b T n δ) :
    IsProbabilityMeasure (swapAnnuityMeasure Q D X b T n δ) :=
  CMS.annuityMeasure_isProbabilityMeasure (D (T 0)) δ _ _ _ h.D_pos h.δ_pos
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, h.n_pos⟩⟩ h.bond_pos h.annuity0_pos h.integrable_annuity_mul
    h.integral_annuity_mul

/-! ### Annuity-measure pricing of a payoff on the swap rate -/

/-- **Annuity-measure pricing in a swap model**: `A(0) · 𝔼^A[S] = 𝔼[D (T 0) · S · A(T₀)]`, the
annuity-settled payoff `S · A(T₀)` (`annuityMeasure_price`). -/
theorem SwapModel.annuity0_mul_integral (h : SwapModel Q 𝓕 D X σ b T n δ) (S : Ω → ℝ) :
    annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, S ω ∂(swapAnnuityMeasure Q D X b T n δ)
      = ∫ ω, D (T 0) ω
          * (S ω * CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω) ∂Q :=
  CMS.annuityMeasure_price (D (T 0)) δ (swapCurve X b (T 0)) (Finset.Icc 1 n) _ S h.D_pos
    h.D_meas h.δ_pos ⟨1, Finset.mem_Icc.2 ⟨le_rfl, h.n_pos⟩⟩ h.bond_pos h.annuity0_pos
    h.annuity_meas

/-- **A payoff on the swap rate, paid at the fixing date, is an annuity-measure expectation.** If
`φ` is `g` of the swap rate observed at `T₀`, the contract paying `φ` at `T₀` is worth
`A(0) · 𝔼^A[g(S) / A(T₀)]`: `annuityMeasure_price` with the annuity-settled payoff `g(S)`. -/
theorem value_pay_swapRate (h : SwapModel Q 𝓕 D X σ b T n δ) {φ : Payoff ι} {g : ℝ → ℝ}
    (hφ : ∀ s : Scenario ι, φ.eval s = g (s σ (T 0))) :
    (Contract.pay (T 0) φ).value Q D X
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, g (X σ (T 0) ω) / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
          ∂(swapAnnuityMeasure Q D X b T n δ) := by
  rw [h.annuity0_mul_integral
    (fun ω ↦ g (X σ (T 0) ω) / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω),
    Contract.value_pay]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  beta_reduce
  rw [hφ, div_mul_cancel₀ _ (h.annuity_pos ω).ne']
  rfl

/-- **A CMS caplet is an annuity-measure call on the swap rate**: the caplet paying `(S − K)⁺` at
`T₀` is worth `A(0) · 𝔼^A[(S − K)⁺ / A(T₀)]`. -/
theorem value_cmsCaplet (h : SwapModel Q 𝓕 D X σ b T n δ) (K : ℝ) :
    (cmsCaplet σ (T 0) K).value Q D X
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, max (X σ (T 0) ω - K) 0
            / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
          ∂(swapAnnuityMeasure Q D X b T n δ) :=
  value_pay_swapRate h (g := fun x ↦ max (x - K) 0) fun _ ↦ rfl

/-- **A CMS floorlet is an annuity-measure put on the swap rate**: the floorlet paying `(K − S)⁺`
at `T₀` is worth `A(0) · 𝔼^A[(K − S)⁺ / A(T₀)]`. -/
theorem value_cmsFloorlet (h : SwapModel Q 𝓕 D X σ b T n δ) (K : ℝ) :
    (cmsFloorlet σ (T 0) K).value Q D X
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, max (K - X σ (T 0) ω) 0
            / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
          ∂(swapAnnuityMeasure Q D X b T n δ) :=
  value_pay_swapRate h (g := fun x ↦ max (K - x) 0) fun _ ↦ rfl

/-- **A CMS swaplet is worth `A(0) · 𝔼^A[S / A(T₀)]`.** -/
theorem value_cmsSwaplet (h : SwapModel Q 𝓕 D X σ b T n δ) :
    (cmsSwaplet σ (T 0)).value Q D X
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, X σ (T 0) ω / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
          ∂(swapAnnuityMeasure Q D X b T n δ) :=
  value_pay_swapRate h (g := id) fun _ ↦ rfl

/-! ### The forward swap rate -/

/-- **The forward swap rate is the annuity-measure mean of the swap rate**:
`𝔼^A[S] = (P(0, T₀) − P(0, Tₙ)) / A(0)`, the par swap rate of the zero curve (`parSwapRate`).
No adjustment at the fixing date: the `Qᴬ`-mean of the swap rate is the time-0 par rate. -/
theorem SwapModel.integral_swapRate (h : SwapModel Q 𝓕 D X σ b T n δ) :
    ∫ ω, X σ (T 0) ω ∂(swapAnnuityMeasure Q D X b T n δ)
      = parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
          (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)) := by
  have hn : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨h.n_pos, le_rfl⟩
  rw [parSwapRate, eq_div_iff h.annuity0_pos.ne', mul_comm, h.annuity0_mul_integral]
  have e : ∀ᵐ ω ∂Q, D (T 0) ω * (X σ (T 0) ω
      * CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)
      = D (T 0) ω - D (T 0) ω * X (b n) (T 0) ω := by
    filter_upwards [h.rate_eq] with ω hω
    rw [hω, parSwapRate, div_mul_cancel₀ _ (h.annuity_pos ω).ne']
    ring
  rw [integral_congr_ae e, integral_sub (h.integrable_D0)
    ((h.hasBondPrice n hn).integrable_discount_mul), (h.hasBondPrice n hn).integral_discount]
  rfl

/-! ### The convexity adjustment, for a rate paid at its fixing date -/

section Adjustment

variable {c : ℕ → ℝ}

omit [IsProbabilityMeasure Q] in
/-- When the bond prices other than the last are known constants `c i`, the annuity is
`δ (C + P(T₀, Tₙ))`, `C = Σ c i`. -/
theorem SwapModel.annuity_ae_eq (h : SwapModel Q 𝓕 D X σ b T n δ)
    (hc : ∀ i ∈ (Finset.Icc 1 n).erase n, ∀ᵐ ω ∂Q, X (b i) (T 0) ω = c i) :
    CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) =ᵐ[Q] fun ω ↦
      δ * ((∑ i ∈ (Finset.Icc 1 n).erase n, c i) + X (b n) (T 0) ω) := by
  have hn : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨h.n_pos, le_rfl⟩
  filter_upwards [(Filter.eventually_all_finset _).2 hc] with ω hω'
  have hsum : ∑ i ∈ Finset.Icc 1 n, swapCurve X b (T 0) ω i
      = (∑ i ∈ (Finset.Icc 1 n).erase n, c i) + X (b n) (T 0) ω := by
    rw [← Finset.sum_erase_add _ _ hn]
    exact congrArg (· + _) (Finset.sum_congr rfl hω')
  simp only [CMS.annuityRandom, annuity, hsum]

omit [IsProbabilityMeasure Q] in
/-- The swap rate is the `cmsCurveRate` of the last bond price when the other bond prices are
known constants: the bridge to the Jensen-gap results of `CMS.lean`. -/
theorem SwapModel.rate_eq_cmsCurveRate (h : SwapModel Q 𝓕 D X σ b T n δ)
    (hc : ∀ i ∈ (Finset.Icc 1 n).erase n, ∀ᵐ ω ∂Q, X (b i) (T 0) ω = c i) :
    X σ (T 0) =ᵐ[Q] fun ω ↦
      CMS.cmsCurveRate 1 δ (∑ i ∈ (Finset.Icc 1 n).erase n, c i) (X (b n) (T 0) ω) := by
  filter_upwards [h.rate_eq, h.annuity_ae_eq hc] with ω hω hA
  rw [hω, parSwapRate, hA]
  rfl

/-- **The swap rate at the mean final bond price is at most the forward swap rate** (the Jensen
gap of the rate functional, for the contract's underlying). If the bond prices other than
`P(T₀, Tₙ)` are known constants `c i`, `C = Σ c i > 0`, then
`cmsCurveRate 1 δ C (𝔼^A[P(T₀, Tₙ)]) ≤ 𝔼^A[S] = (P(0, T₀) − P(0, Tₙ))/A(0)`:
`cmsCurveRate_jensenGap_nonneg` of `Models/Rates/CMS.lean` with `x₀` the annuity-measure mean. -/
theorem SwapModel.cmsCurveRate_integral_le_forwardSwapRate (h : SwapModel Q 𝓕 D X σ b T n δ)
    (hc : ∀ i ∈ (Finset.Icc 1 n).erase n, ∀ᵐ ω ∂Q, X (b i) (T 0) ω = c i)
    (hC : 0 < ∑ i ∈ (Finset.Icc 1 n).erase n, c i)
    (hW : Integrable (X (b n) (T 0)) (swapAnnuityMeasure Q D X b T n δ))
    (hS : Integrable (X σ (T 0)) (swapAnnuityMeasure Q D X b T n δ)) :
    CMS.cmsCurveRate 1 δ (∑ i ∈ (Finset.Icc 1 n).erase n, c i)
        (∫ ω, X (b n) (T 0) ω ∂(swapAnnuityMeasure Q D X b T n δ))
      ≤ parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
          (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)) := by
  have := h.isProbabilityMeasure
  have hn : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨h.n_pos, le_rfl⟩
  have hac : swapAnnuityMeasure Q D X b T n δ ≪ Q := withDensity_absolutelyContinuous _ _
  have hae := hac.ae_eq (h.rate_eq_cmsCurveRate hc)
  have hj : CMS.cmsCurveRate 1 δ (∑ i ∈ (Finset.Icc 1 n).erase n, c i)
        (∫ ω, X (b n) (T 0) ω ∂(swapAnnuityMeasure Q D X b T n δ))
      ≤ ∫ ω, CMS.cmsCurveRate 1 δ (∑ i ∈ (Finset.Icc 1 n).erase n, c i) (X (b n) (T 0) ω)
          ∂(swapAnnuityMeasure Q D X b T n δ) := CMS.cmsCurveRate_jensenGap_nonneg (D (T 0)) δ 1
    (∑ i ∈ (Finset.Icc 1 n).erase n, c i) _ _ (swapCurve X b (T 0)) (Finset.Icc 1 n)
    (X (b n) (T 0)) h.D_pos h.δ_pos hC (by linarith) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, h.n_pos⟩⟩
    h.bond_pos h.annuity0_pos h.integrable_annuity_mul h.integral_annuity_mul
    (fun ω ↦ (h.bond_pos ω n hn).le) hW (hS.congr hae) rfl
  rwa [← integral_congr_ae hae, h.integral_swapRate] at hj

/-- **The mean of the reciprocal annuity**: `A(0) · 𝔼^A[1 / A(T₀)] = P(0, T₀)`. -/
theorem SwapModel.annuity0_mul_integral_inv (h : SwapModel Q 𝓕 D X σ b T n δ) :
    annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
      * ∫ ω, (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)⁻¹
          ∂(swapAnnuityMeasure Q D X b T n δ) = zeroCurve Q D (T 0) := by
  rw [h.annuity0_mul_integral
    (fun ω ↦ (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)⁻¹)]
  exact integral_congr_ae (ae_of_all _ fun ω ↦ by
    beta_reduce
    rw [inv_mul_cancel₀ (h.annuity_pos ω).ne', mul_one])

/-- **The CMS swaplet, paid at its fixing date, is the forward swap rate plus a covariance.**
`value = P(0, T₀) · S₀ + A(0) · Cov^A(S, 1/A(T₀))`, with `S₀` the forward swap rate and the
covariance written out: the contract is worth `A(0) 𝔼^A[S/A]`, and `A(0) 𝔼^A[1/A] = P(0, T₀)`,
`𝔼^A[S] = S₀`. -/
theorem SwapModel.value_cmsSwaplet_eq (h : SwapModel Q 𝓕 D X σ b T n δ) :
    (cmsSwaplet σ (T 0)).value Q D X
      = zeroCurve Q D (T 0) * parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
            (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))
        + annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
          * (∫ ω, X σ (T 0) ω / CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
              ∂(swapAnnuityMeasure Q D X b T n δ)
            - (∫ ω, X σ (T 0) ω ∂(swapAnnuityMeasure Q D X b T n δ))
              * ∫ ω, (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)⁻¹
                  ∂(swapAnnuityMeasure Q D X b T n δ)) := by
  rw [value_cmsSwaplet h, ← h.integral_swapRate, ← h.annuity0_mul_integral_inv]
  ring

/-- **The convexity adjustment of a CMS swaplet paid at its fixing date is nonnegative.** If the
bond prices other than `P(T₀, Tₙ)` are known constants, the swap rate is affine in the reciprocal
annuity, `S = (1 + C)/A − 1/δ` (`C = Σ c i`, `1 + C ≥ 0`), so
`Cov^A(S, 1/A) = (1 + C) Var^A(1/A) ≥ 0`: the swaplet is worth at least `P(0, T₀)` times the forward
swap rate. The reciprocal annuity is assumed square-integrable under the annuity measure. -/
theorem SwapModel.zeroCurve_mul_forwardSwapRate_le_value_cmsSwaplet
    (h : SwapModel Q 𝓕 D X σ b T n δ)
    (hc : ∀ i ∈ (Finset.Icc 1 n).erase n, ∀ᵐ ω ∂Q, X (b i) (T 0) ω = c i)
    (hC : 0 ≤ 1 + ∑ i ∈ (Finset.Icc 1 n).erase n, c i)
    (hg : Integrable (fun ω ↦
      (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)⁻¹)
      (swapAnnuityMeasure Q D X b T n δ))
    (hg2 : Integrable (fun ω ↦
      (CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω)⁻¹ ^ 2)
      (swapAnnuityMeasure Q D X b T n δ)) :
    zeroCurve Q D (T 0) * parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
        (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))
      ≤ (cmsSwaplet σ (T 0)).value Q D X := by
  have := h.isProbabilityMeasure
  set A := CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) with hA
  set μ := swapAnnuityMeasure Q D X b T n δ with hμ
  set C := ∑ i ∈ (Finset.Icc 1 n).erase n, c i
  have hac : μ ≪ Q := withDensity_absolutelyContinuous _ _
  -- the swap rate is affine in `1/A`
  have hS : X σ (T 0) =ᵐ[μ] fun ω ↦ (1 + C) * (A ω)⁻¹ - δ⁻¹ := by
    refine hac.ae_eq ?_
    filter_upwards [h.rate_eq, h.annuity_ae_eq hc] with ω hω hAω
    have hδ := h.δ_pos.ne'
    have hAp : A ω ≠ 0 := (h.annuity_pos ω).ne'
    rw [hω, parSwapRate]
    change (1 - X (b n) (T 0) ω) / A ω = _
    have hW : X (b n) (T 0) ω = A ω / δ - C := by
      field_simp
      linarith [hAω]
    rw [hW]
    field_simp
    ring
  have hSA : (fun ω ↦ X σ (T 0) ω / A ω) =ᵐ[μ] fun ω ↦ (1 + C) * (A ω)⁻¹ ^ 2 - δ⁻¹ * (A ω)⁻¹ := by
    filter_upwards [hS] with ω hω
    rw [hω, div_eq_mul_inv]
    ring
  set I := ∫ ω, (A ω)⁻¹ ∂μ
  have hJ : ∫ ω, X σ (T 0) ω ∂μ = (1 + C) * I - δ⁻¹ := by
    rw [integral_congr_ae hS, integral_sub (hg.const_mul _) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have hK : ∫ ω, X σ (T 0) ω / A ω ∂μ = (1 + C) * ∫ ω, (A ω)⁻¹ ^ 2 ∂μ - δ⁻¹ * I := by
    rw [integral_congr_ae hSA, integral_sub (hg2.const_mul _) (hg.const_mul _),
      integral_const_mul, integral_const_mul]
  have hvar : 0 ≤ ∫ ω, (A ω)⁻¹ ^ 2 ∂μ - I ^ 2 := by
    have hm : MemLp (fun ω ↦ (A ω)⁻¹) 2 μ :=
      (memLp_two_iff_integrable_sq h.annuity_meas.inv.aestronglyMeasurable).2 hg2
    have := ProbabilityTheory.variance_nonneg (fun ω ↦ (A ω)⁻¹) μ
    rwa [ProbabilityTheory.variance_eq_sub hm] at this
  rw [h.value_cmsSwaplet_eq]
  refine le_add_of_nonneg_right (mul_nonneg h.annuity0_pos.le ?_)
  rw [hK, hJ]
  nlinarith [mul_nonneg hC hvar]

end Adjustment

/-! ### The payer swaption, and Black's formula -/

/-- The sum `Σᵢ₌₁ⁿ` of the observations `b i` at time `t`, as a payoff. -/
noncomputable def Payoff.obsSum (b : ℕ → ι) (t : ℝ≥0) : ℕ → Payoff ι
  | 0 => .const 0
  | k + 1 => .add (obsSum b t k) (.obs (b (k + 1)) t)

theorem Payoff.eval_obsSum (s : Scenario ι) (b : ℕ → ι) (t : ℝ≥0) (n : ℕ) :
    (Payoff.obsSum b t n).eval s = ∑ i ∈ Finset.Icc 1 n, s (b i) t := by
  induction n with
  | zero => simp [Payoff.obsSum, Payoff.eval]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    simp [Payoff.obsSum, Payoff.eval]

/-- A **payer swaption**: pays, at the expiry `T₀`, the positive part of the value of the payer
swap on the dates `T 1, …, T n` with fixed rate `K` and accrual `δ`,
`(1 − P(T₀, Tₙ) − K δ Σᵢ P(T₀, Tᵢ))⁺` (`payerSwapValue`), where `b i` carries `P(T₀, Tᵢ)`. -/
noncomputable def payerSwaption (b : ℕ → ι) (T₀ : ℝ≥0) (n : ℕ) (δ K : ℝ) : Contract ι :=
  .pay T₀ (.max (.sub (.sub (.const 1) (.obs (b n) T₀))
    (.mul (.const (K * δ)) (Payoff.obsSum b T₀ n))) (.const 0))

/-- **A payer swaption is `A(0)` times an annuity-measure call on the swap rate**:
`value = A(0) · 𝔼^A[(S − K)⁺]`. The payoff is `A(T₀)(S − K)⁺`, the annuity-settled payoff of
`annuityMeasure_price`. -/
theorem value_payerSwaption (h : SwapModel Q 𝓕 D X σ b T n δ) (K : ℝ) :
    (payerSwaption b (T 0) n δ K).value Q D X
      = annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)
        * ∫ ω, max (X σ (T 0) ω - K) 0 ∂(swapAnnuityMeasure Q D X b T n δ) := by
  rw [h.annuity0_mul_integral (fun ω ↦ max (X σ (T 0) ω - K) 0)]
  simp only [payerSwaption, Contract.value_pay, Payoff.eval, Payoff.eval_obsSum, scenarioAt]
  refine integral_congr_ae ?_
  filter_upwards [h.rate_eq] with ω hω
  have hA := h.annuity_pos ω
  have hAe : CMS.annuityRandom δ (swapCurve X b (T 0)) (Finset.Icc 1 n) ω
      = δ * ∑ i ∈ Finset.Icc 1 n, X (b i) (T 0) ω := rfl
  congr 1
  rw [max_mul_of_nonneg _ _ hA.le, zero_mul]
  congr 1
  rw [hω, parSwapRate, sub_mul, div_mul_cancel₀ _ hA.ne', hAe]
  ring

/-- **Black's swaption formula.** If the swap rate is lognormal under the annuity measure `Qᴬ`,
`S = bsTerminal F 0 σ' T' Z` with `Z` standard normal there, the payer swaption is worth
`blackPayerSwaption A(0) F K σ' T'`, `A(0) [F Φ(d₁) − K Φ(d₂)]`; `black_futures_formula` on `Qᴬ`.
The lognormality of the swap rate under its annuity measure is a hypothesis, the standard
assumption of Black's swaption model, and not derived from a term-structure model. -/
theorem value_payerSwaption_black (h : SwapModel Q 𝓕 D X σ b T n δ)
    {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = swapAnnuityMeasure Q D X b T n δ) {F K σ' T' : ℝ} {Z : Ω → ℝ}
    (hZ : BSCallHyp Q' F K 0 σ' T' Z)
    (hS : X σ (T 0) =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ' T' (Z ω)) :
    (payerSwaption b (T 0) n δ K).value Q D X
      = blackPayerSwaption (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))
          F K σ' T' := by
  subst hQ'
  have e : ∀ᵐ ω ∂swapAnnuityMeasure Q D X b T n δ, max (X σ (T 0) ω - K) 0
      = max (bsTerminal F 0 σ' T' (Z ω) - K) 0 := hS.mono fun ω hω ↦ by rw [hω]
  rw [value_payerSwaption h, integral_congr_ae e, blackPayerSwaption]
  simpa using congrArg (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n) * ·)
    (black_futures_formula hZ 0)

/-- **Black's swaption formula, at the forward swap rate of the zero curve.** Under the
hypotheses of `value_payerSwaption_black`, `F` is the par swap rate of the zero curve,
`(P(0, T₀) − P(0, Tₙ))/A(0)`: the annuity-measure mean of a lognormal is its centre. -/
theorem value_payerSwaption_black_forwardSwapRate (h : SwapModel Q 𝓕 D X σ b T n δ)
    {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = swapAnnuityMeasure Q D X b T n δ) {K σ' T' F : ℝ} {Z : Ω → ℝ}
    (hZ : BSCallHyp Q' F K 0 σ' T' Z)
    (hS : X σ (T 0) =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ' T' (Z ω)) :
    (payerSwaption b (T 0) n δ K).value Q D X
      = blackPayerSwaption (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))
          (parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
            (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n))) K σ' T' := by
  have hF : F = parSwapRate (zeroCurve Q D (T 0)) (zeroCurve Q D (T n))
      (annuity δ (fun i ↦ zeroCurve Q D (T i)) (Finset.Icc 1 n)) := by
    rw [← h.integral_swapRate, ← hQ', integral_congr_ae hS]
    simpa using (discounted_terminal_eq_S0 hZ).symm
  rw [← hF]
  exact value_payerSwaption_black h hQ' hZ hS

end MathFin.Contracts
