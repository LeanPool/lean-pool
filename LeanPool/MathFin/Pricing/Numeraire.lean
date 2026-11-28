/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Martingales.ChangeOfMeasure
public import LeanPool.MathFin.Probability.Martingales.EquivMeasure

/-!
# The change of numéraire

A **numéraire** is a strictly positive traded asset taken as the unit of
account. Fix a pricing measure `Q` associated to a reference numéraire `B` (the
money market): the arbitrage-free price of a terminal claim `X` is

  `price(X) = B₀ · 𝔼^Q[X / B_T]`.

Given a second numéraire `N` — strictly positive, with `N/B` a `Q`-martingale
(the tradeability/normalization condition `𝔼^Q[N_T/B_T] = N₀/B₀`) — define the
**numéraire measure** `Q^N` by the Radon–Nikodym density

  `dQ^N/dQ := (N_T · B₀) / (N₀ · B_T)`.

The **change-of-numéraire theorem** (`changeOfNumeraire`) is that price is
numéraire-invariant:

  `N₀ · 𝔼^{Q^N}[X / N_T] = B₀ · 𝔼^Q[X / B_T]`.

The proof is a one-line cancellation: transporting the `Q^N`-expectation back to
`Q` multiplies the integrand `X/N_T` by the density `(N_T·B₀)/(N₀·B_T)`, and the
`N_T` cancels, leaving `(B₀/N₀)·(X/B_T)`; the leading `N₀` cancels the `1/N₀`.
Notably the identity needs **no integrability hypothesis** — it is a pure
measure-transport identity (`integral_withDensity_eq_integral_toReal_smul`)
followed by scalar algebra, so it holds verbatim whether or not the claim is
square-integrable.

This is the abstract backbone of every concrete numéraire change in the library.
The stock numéraire (`Models.BlackScholes.StockNumeraire`: `Φ(d₁)` as the stock-measure
exercise probability) is the instance `B_T = e^{rT}`, `B₀ = 1`, `N = S`; the
second-asset numéraire of the exchange option (`Models.BlackScholes.ExchangeOption`)
and the forward/annuity numéraires of the Garman normal form
(`Models.BlackScholes.GarmanNormalForm`) are further instances — each recovered by
choosing `B`, `N` and reading off the density.

## Main definitions

* `numeraireDensity`: the `[0, ∞]`-valued Radon–Nikodym derivative `(N_T · B₀) / (N₀ · B_T)`.
* `numeraireMeasure`: the measure `Q^N = Q.withDensity` of that density.

## Main results

* `MathFin.numeraireMeasure_isEquivProbMeasure` — `Q^N` is a probability measure
  equivalent to `Q` (`Q^N ≪ Q` and `Q ≪ Q^N`), under the martingale/normalization
  condition `𝔼^Q[N_T/B_T] = N₀/B₀`; `numeraireMeasure_isProbabilityMeasure` is its first
  component.
* `MathFin.changeOfNumeraire` — price invariance
  `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]`.
* `MathFin.changeOfNumeraire_setIntegral_eq` — the **dynamic** change of numéraire: if
  `t ↦ (B₀/N₀)(X_t/B_t)` and `t ↦ (B₀/N₀)(N_t/B_t)` are `Q`-martingales (and the mixed product is
  integrable) then `X/N` has the set-integral martingale property under `Q^N`. Obtained by
  instantiating the Bayes engine `changeOfMeasure_setIntegral_eq` at density process
  `Z_t = (N_t·B₀)/(N₀·B_t)` and payoff `D_t = X_t/N_t` — wiring the numéraire seam to the Girsanov
  engine.

## References

* [H. Geman, N. El Karoui and J. C. Rochet, *Changes of numéraire, changes of probability measure
  and option pricing*][GemanElKarouiRochet1995]

## Tags

change of numéraire, numeraire measure, Radon–Nikodym density, risk-neutral measure,
forward measure, price invariance, Geman–El Karoui–Rochet, MSC 91G20, MSC 60G44, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*}

/-- **The numéraire-change density** `dQ^N/dQ = (N_T · B₀)/(N₀ · B_T)`, as a
`[0,∞]`-valued Radon–Nikodym derivative. Nonnegative whenever the numéraires are
positive. -/
noncomputable def numeraireDensity (BT NT : Ω → ℝ) (B0 N0 : ℝ) : Ω → ℝ≥0∞ :=
  fun ω ↦ ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))

/-- The numéraire density is a nonnegative real when both numéraires are
positive. -/
lemma numeraireDensity_toReal_nonneg {BT NT : Ω → ℝ} {B0 N0 : ℝ}
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω)
    (hB0 : 0 ≤ B0) (hN0 : 0 < N0) (ω : Ω) :
    0 ≤ NT ω * B0 / (N0 * BT ω) :=
  div_nonneg (mul_nonneg (hNTpos ω).le hB0) (mul_nonneg hN0.le (hBTpos ω).le)

/-- **The numéraire measure** `Q^N := Q.withDensity((N_T·B₀)/(N₀·B_T))`: the
pricing measure attached to numéraire `N`. -/
noncomputable def numeraireMeasure [MeasurableSpace Ω]
    (Q : Measure Ω) (BT NT : Ω → ℝ) (B0 N0 : ℝ) : Measure Ω :=
  Q.withDensity (numeraireDensity BT NT B0 N0)

section

variable [MeasurableSpace Ω] {Q : Measure Ω} {BT NT : Ω → ℝ} {B0 N0 : ℝ}

/-- **The numéraire measure is an equivalent probability measure.** Under the tradeability /
normalization condition `𝔼^Q[N_T/B_T] = N₀/B₀` (equivalently: `N/B` is a `Q`-martingale), the
density `(N_T·B₀)/(N₀·B_T)` is strictly positive with `Q`-mean `(B₀/N₀)·(N₀/B₀) = 1`, so
`Q^N` is a probability measure with `Q^N ≪ Q` and `Q ≪ Q^N` (`isEquivProbMeasure_withDensity`). -/
theorem numeraireMeasure_isEquivProbMeasure
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω) (hB0 : 0 < B0) (hN0 : 0 < N0)
    (hint : Integrable (fun ω ↦ NT ω / BT ω) Q)
    (hmart : ∫ ω, NT ω / BT ω ∂Q = N0 / B0) :
    IsEquivProbMeasure Q (numeraireMeasure Q BT NT B0 N0) := by
  have heq : (fun ω ↦ NT ω * B0 / (N0 * BT ω)) = fun ω ↦ (B0 / N0) * (NT ω / BT ω) := by
    funext ω; ring
  refine isEquivProbMeasure_withDensity Q (g := fun ω ↦ NT ω * B0 / (N0 * BT ω))
    (fun ω ↦ div_pos (mul_pos (hNTpos ω) hB0) (mul_pos hN0 (hBTpos ω)))
    (by rw [heq]; exact hint.const_mul _) ?_
  rw [heq, integral_const_mul, hmart]
  field_simp

/-- **The numéraire measure is a probability measure** — the first component of
`numeraireMeasure_isEquivProbMeasure`, under the same normalization condition
`𝔼^Q[N_T/B_T] = N₀/B₀`. -/
theorem numeraireMeasure_isProbabilityMeasure
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω) (hB0 : 0 < B0) (hN0 : 0 < N0)
    (hint : Integrable (fun ω ↦ NT ω / BT ω) Q)
    (hmart : ∫ ω, NT ω / BT ω ∂Q = N0 / B0) :
    IsProbabilityMeasure (numeraireMeasure Q BT NT B0 N0) :=
  (numeraireMeasure_isEquivProbMeasure hNTpos hBTpos hB0 hN0 hint hmart).isProb

/-- **The change-of-numéraire theorem.** Price is numéraire-invariant:

  `N₀ · 𝔼^{Q^N}[X / N_T] = B₀ · 𝔼^Q[X / B_T]`,

where `Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))`. The proof transports the
`Q^N`-integral back to `Q` (multiplying by the density) and cancels `N_T`; no
integrability hypothesis is needed. -/
theorem changeOfNumeraire (X : Ω → ℝ)
    (hNTmeas : Measurable NT) (hBTmeas : Measurable BT)
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω) (hB0 : 0 ≤ B0) (hN0 : 0 < N0) :
    N0 * ∫ ω, X ω / NT ω ∂(numeraireMeasure Q BT NT B0 N0)
      = B0 * ∫ ω, X ω / BT ω ∂Q := by
  have hden : numeraireMeasure Q BT NT B0 N0
      = Q.withDensity (fun ω ↦ ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))) := rfl
  have hdmeas : Measurable fun ω ↦ NT ω * B0 / (N0 * BT ω) :=
    (hNTmeas.mul measurable_const).div (measurable_const.mul hBTmeas)
  rw [hden, integral_withDensity_eq_integral_toReal_smul hdmeas.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hcongr : ∀ ω, (ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))).toReal • (X ω / NT ω)
      = (B0 / N0) * (X ω / BT ω) := by
    intro ω
    rw [ENNReal.toReal_ofReal (numeraireDensity_toReal_nonneg hNTpos hBTpos hB0 hN0 ω),
      smul_eq_mul]
    field_simp [(hNTpos ω).ne', (hBTpos ω).ne', hN0.ne']
  simp_rw [hcongr, integral_const_mul]
  have hcancel : N0 * (B0 / N0 * ∫ ω, X ω / BT ω ∂Q) = B0 * ∫ ω, X ω / BT ω ∂Q := by
    field_simp [hN0.ne']
  exact hcancel

end

section Dynamic

open scoped NNReal

variable {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration Q 𝓕]
  {B N X : ℝ≥0 → Ω → ℝ} {B0 N0 : ℝ}

omit [IsFiniteMeasure Q] in
/-- **The dynamic change-of-numéraire theorem** (set-integral form). Fix a pricing
measure `Q` for the reference numéraire `B` and a second strictly positive numéraire
`N`, both adapted, with the normalisation process `t ↦ (B₀/N₀)(N_t/B_t)` a
`Q`-martingale (`hNB` — the dynamic form of `𝔼^Q[N_T/B_T] = N₀/B₀`). If the discounted
claim `t ↦ (B₀/N₀)(X_t/B_t)` is a `Q`-martingale (`hXB`), then `X/N` has the
`Q^N`-martingale (set-integral) property under the numéraire measure
`Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q^N`-integrals of `X_t/N_t` and `X_s/N_s` over `A` agree.

This is the **Bayes engine** `changeOfMeasure_setIntegral_eq` instantiated at the
density process `Z_t = (N_t·B₀)/(N₀·B_t)` and payoff process `D_t = X_t/N_t`, whose
product `Z_t·D_t = (B₀/N₀)(X_t/B_t)` is exactly `hXB` (the `N_t` cancels). It wires the
change-of-numéraire seam to the Girsanov change-of-measure engine. The tilted measure
is definitionally `numeraireMeasure Q (B T) (N T) B0 N0`. -/
theorem changeOfNumeraire_setIntegral_eq (T : ℝ≥0)
    (hNpos : ∀ u ω, 0 < N u ω) (hBpos : ∀ u ω, 0 < B u ω)
    (hB0 : 0 ≤ B0) (hN0 : 0 < N0)
    (hNmeas : ∀ u, Measurable (N u)) (hBmeas : ∀ u, Measurable (B u))
    (hDsm : ∀ u, StronglyMeasurable[𝓕 u] (fun ω ↦ X u ω / N u ω))
    (hNB : Martingale (fun t ω ↦ (B0 / N0) * (N t ω / B t ω)) 𝓕 Q)
    (hXB : Martingale (fun t ω ↦ (B0 / N0) * (X t ω / B t ω)) 𝓕 Q)
    (hmix : ∀ u, u ≤ T →
      Integrable (fun ω ↦ X u ω / N u ω * (N T ω * B0 / (N0 * B T ω))) Q)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, X t ω / N t ω
        ∂(Q.withDensity (fun ω ↦ ENNReal.ofReal (N T ω * B0 / (N0 * B T ω))))
      = ∫ ω in A, X s ω / N s ω
        ∂(Q.withDensity (fun ω ↦ ENNReal.ofReal (N T ω * B0 / (N0 * B T ω)))) := by
  -- The density `Z_T = (N_T·B₀)/(N₀·B_T)` is measurable and nonnegative.
  have hZmeasT : Measurable (fun ω ↦ N T ω * B0 / (N0 * B T ω)) :=
    ((hNmeas T).mul measurable_const).div (measurable_const.mul (hBmeas T))
  have hZpos : ∀ ω, 0 ≤ N T ω * B0 / (N0 * B T ω) := fun ω ↦
    div_nonneg (mul_nonneg (hNpos T ω).le hB0) (mul_nonneg hN0.le (hBpos T ω).le)
  -- `Z_t = (N_t·B₀)/(N₀·B_t) = (B₀/N₀)(N_t/B_t)` is the normalisation martingale `hNB`.
  have hZ : Martingale (fun u ω ↦ N u ω * B0 / (N0 * B u ω)) 𝓕 Q := by
    have hfeq : (fun u (ω : Ω) ↦ N u ω * B0 / (N0 * B u ω))
        = fun u ω ↦ (B0 / N0) * (N u ω / B u ω) := by
      funext u ω; ring
    rw [hfeq]; exact hNB
  -- `Z_t·D_t = (B₀/N₀)(X_t/B_t)` — the `N_t` cancels — is the martingale `hXB`.
  have hZD : Martingale
      (fun t ω ↦ N t ω * B0 / (N0 * B t ω) * (X t ω / N t ω)) 𝓕 Q := by
    have hfeq : (fun t (ω : Ω) ↦ N t ω * B0 / (N0 * B t ω) * (X t ω / N t ω))
        = fun t ω ↦ (B0 / N0) * (X t ω / B t ω) := by
      funext u ω
      field_simp [hN0.ne', (hNpos u ω).ne', (hBpos u ω).ne']
    rw [hfeq]; exact hXB
  -- Instantiate the Bayes engine at `Z_t = (N_t·B₀)/(N₀·B_t)`, `D_t = X_t/N_t`.
  exact changeOfMeasure_setIntegral_eq (Z := fun u ω ↦ N u ω * B0 / (N0 * B u ω))
    (D := fun u ω ↦ X u ω / N u ω) T hZmeasT hZpos hDsm hZ hZD hmix hst htT hA

end Dynamic

end MathFin
