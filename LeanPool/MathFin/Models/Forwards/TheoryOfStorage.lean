/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.NoArbitrageDerivations

/-!
# Theory of storage: convenience yield and the canonical-storage price kink

The **theory of storage** (Kaldor 1939, Working 1949) models the commodity spot
price as a kinked function of "availability" `A` (current stock plus expected
supply). For availability below the kink point `A*` (scarcity) the price tracks
the inverse demand-for-storage curve `f⁻¹(A)`, which falls as availability
rises; at and above `A*` storage is profitable and the market sits at the
investment-regime price floor `Sbar = E[S_{t+1}] − C`:

  `S(A) = max(Sbar, f⁻¹(A))`                         (canonical-storage price)
  `Y(A) = max(f⁻¹(A) − Sbar, 0)`                      (convenience yield)

By definition the convenience yield is positive exactly where `f⁻¹(A) > Sbar`
and zero elsewhere; for a decreasing `f⁻¹` that is where scarcity bites, below
the kink. The definitions here take any `f⁻¹ : ℝ → ℝ`: no monotonicity of `f⁻¹`
is assumed, and nothing is proved about `A` below or above `A*`. The two
functions are two faces of the same kink: `Y(A) = S(A) − Sbar` always.

The forward is derived, not posited, from the library's no-arbitrage forward
(`forward_price_from_no_arbitrage`, `Pricing/NoArbitrageDerivations.lean`). In a
finite-state market with state prices `q` and discount factor `DF = ∑ q`, suppose holding one
unit of the stored commodity to the delivery date is priced at the spot `S₀`: it delivers
the commodity `S_T`, the convenience yield `Y`, and costs the storage `C`, both `Y` and `C`
deterministic and paid at delivery (`∑ q·(S_T − C + Y) = S₀`). Then the forward strike
with zero value is `F = S₀/DF + C − Y` (`storageForward_from_no_arbitrage`). With zero rates
(`DF = 1`), spot `S₀ = S(A)` and `Y = Y(A)`, this gives `F = Sbar + C` at every availability
(`storageForward_at_availability`), and the cost-of-carry identity — the spot price `S(A)`
plus the finance/storage cost `C` net of the convenience-yield benefit — is the kink
identity rearranged:

  `F − S(A) = C − Y(A)`

(convenience yield *reduces* net carry cost — high-yield, near-backwardation
markets have `Y(A)` large relative to `C`. This is the standard sign
convention in the literature: convenience yield is a benefit to the holder
of physical stock, so it subtracts from the holder's net financing cost,
i.e. from `C`).

For an isoelastic demand-for-storage curve
`f⁻¹(A) = p_ref · (a_ref / A) ^ ε` (flexibility `ε = −d ln p / d ln A`,
reference availability `a_ref`, reference price `p_ref`), a kink point `A*`
with `f⁻¹(A*) = Sbar` is

  `A* = a_ref · (p_ref / Sbar) ^ {1/ε}`

for `a_ref, p_ref, Sbar > 0` and `ε ≠ 0` (`kinkPoint_spec`); that it is the
only crossing is not stated.

## Main definitions

* `storageSpotPrice`: the canonical-storage spot price `max Sbar (invDemand A)` at availability
  `A`, for any `invDemand : ℝ → ℝ`.
* `convenienceYield`: `max (invDemand A - Sbar) 0`.
* `invDemandIsoelastic`: the isoelastic inverse demand for storage `p_ref * (a_ref/A)^ε`.
* `kinkPoint`: the availability at which the isoelastic curve meets the floor `Sbar`.

## Main results

* `convenienceYield_eq_storageSpotPrice_sub` : `Y(A) = S(A) − Sbar`.
* `carry_identity_at_availability` : `(Sbar + C) − S(A) = C − Y(A)`, the
  cost-of-carry identity at the kink functions
  (`convenienceYield_eq_storageSpotPrice_sub` rearranged).
* `storageForward_from_no_arbitrage` : in a finite-state market whose stored commodity
  is priced with storage cost `C` and convenience yield `Y` paid at delivery, the
  zero-value forward strike is `F = S₀/DF + C − Y`.
* `storageForward_at_availability` : with zero rates, spot `S(A)` and convenience
  yield `Y(A)`, the zero-value forward strike is `Sbar + C` at every availability `A`.
* `invDemandIsoelastic`, `kinkPoint`, `kinkPoint_spec` : the isoelastic
  demand-for-storage curve and a kink point solving `f⁻¹(A*) = Sbar`, for
  `a_ref, p_ref, Sbar > 0` and `ε ≠ 0`.

## References

* [N. Kaldor, *Speculation and economic stability*][Kaldor1939].
* [H. Working, *The theory of price of storage*][Working1949].
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 5

## Tags

theory of storage, convenience yield, Kaldor–Working, cost of carry, backwardation,
commodity forward, MSC 91G20, JEL Q02, JEL G13
-/

@[expose] public section

namespace MathFin

/-! ### Canonical-storage spot price and convenience yield -/

/-- **Canonical-storage spot price**: the price sits at the investment-regime
floor `Sbar` when the inverse demand-for-storage curve `f⁻¹` would call for
less, else tracks it. -/
noncomputable def storageSpotPrice (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max Sbar (invDemand A)

/-- **Convenience yield**: positive exactly where scarcity pushes the
demand-for-storage price above the investment-regime floor (`f⁻¹(A) > Sbar`),
zero where it does not. -/
noncomputable def convenienceYield (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max (invDemand A - Sbar) 0

/-- The convenience yield is exactly how far the canonical-storage price sits
above the floor `Sbar` — the two kinks are one and the same. -/
theorem convenienceYield_eq_storageSpotPrice_sub (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) :
    convenienceYield Sbar invDemand A = storageSpotPrice Sbar invDemand A - Sbar := by
  unfold convenienceYield storageSpotPrice
  rw [max_comm Sbar (invDemand A), ← max_sub_sub_right, sub_self]

/-! ### Cost-of-carry identity -/

/-- **Carry identity at a given availability**: at the forward `F = Sbar + C` (cost of
carry off the investment-regime floor; derived from no-arbitrage in
`storageForward_at_availability`), the carry spread against the canonical-storage spot
price is exactly `C − Y(A)` — convenience yield subtracts from the carry cost `C`, the
standard theory-of-storage sign convention (convenience yield is a benefit to the holder of
physical stock). The identity is `convenienceYield_eq_storageSpotPrice_sub` rearranged. -/
theorem carry_identity_at_availability (Sbar C : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) :
    (Sbar + C) - storageSpotPrice Sbar invDemand A = C - convenienceYield Sbar invDemand A := by
  rw [convenienceYield_eq_storageSpotPrice_sub]; ring

/-! ### The forward from no-arbitrage -/

/-- **Cost of carry with storage cost and convenience yield, from no-arbitrage.** In a
finite-state market with state prices `q`, discount factor `∑ q = DF ≠ 0`, terminal commodity
prices `S`, and the stored commodity priced at the spot `S₀` as the claim on
`S_T − C + Y` (the commodity, less the storage cost `C`, plus the convenience yield `Y`, both
deterministic and paid at delivery), the forward with strike `F` has zero value exactly when
`F = S₀/DF + C − Y`. The library's forward `forward_price_from_no_arbitrage` applied to the
stored-commodity claim, shifted by the deterministic carry `Y − C`. -/
theorem storageForward_from_no_arbitrage {ι : Type*} (s : Finset ι) (q S : ι → ℝ)
    (DF S₀ C Y F : ℝ) (hDF : DF ≠ 0) (h_bond : ∑ i ∈ s, q i = DF)
    (h_carry : ∑ i ∈ s, q i * (S i - C + Y) = S₀) :
    (∑ i ∈ s, q i * (S i - F) = 0) ↔ F = S₀ / DF + C - Y := by
  have hsum : ∑ i ∈ s, q i * (S i - F) = ∑ i ∈ s, q i * ((S i - C + Y) - (F - C + Y)) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum]
  refine (forward_price_from_no_arbitrage s q (fun i ↦ S i - C + Y) DF S₀ (F - C + Y) hDF
    h_bond h_carry).trans ?_
  constructor <;> intro h <;> linarith

/-- **The forward does not see availability.** With zero rates (`∑ q = 1`), the spot at the
canonical-storage price `S(A)` and the convenience yield `Y(A)` of the same kink, the
zero-value forward strike is `Sbar + C` at every availability `A`: the convenience yield
offsets exactly the scarcity premium of the spot over the floor. This derives the forward
`F = Sbar + C` at which `carry_identity_at_availability` is stated. -/
theorem storageForward_at_availability {ι : Type*} (s : Finset ι) (q S : ι → ℝ)
    (Sbar C F : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) (h_bond : ∑ i ∈ s, q i = 1)
    (h_carry : ∑ i ∈ s, q i * (S i - C + convenienceYield Sbar invDemand A)
      = storageSpotPrice Sbar invDemand A) :
    (∑ i ∈ s, q i * (S i - F) = 0) ↔ F = Sbar + C := by
  rw [storageForward_from_no_arbitrage s q S 1 _ C _ F one_ne_zero h_bond h_carry,
    convenienceYield_eq_storageSpotPrice_sub, div_one]
  constructor <;> intro h <;> linarith

/-! ### Isoelastic demand for storage and its kink point -/

/-- **Isoelastic inverse demand for storage**: `f⁻¹(A) = p_ref · (a_ref/A)^ε`,
flexibility `ε = −d ln p / d ln A` against reference availability `a_ref` and
price `p_ref`. -/
noncomputable def invDemandIsoelastic (a_ref p_ref ε A : ℝ) : ℝ :=
  p_ref * (a_ref / A) ^ ε

/-- **Kink point**: the availability `A*` at which the isoelastic
demand-for-storage curve meets the investment-regime floor `Sbar`. -/
noncomputable def kinkPoint (a_ref p_ref Sbar ε : ℝ) : ℝ :=
  a_ref * (p_ref / Sbar) ^ (1 / ε)

/-- **Kink-point equation**: `f⁻¹(A*) = Sbar`, i.e. the isoelastic
demand-for-storage curve meets the floor at `kinkPoint` (uniqueness of the
crossing is not stated). -/
theorem kinkPoint_spec (a_ref p_ref Sbar ε : ℝ)
    (ha : 0 < a_ref) (hp : 0 < p_ref) (hS : 0 < Sbar) (hε : ε ≠ 0) :
    invDemandIsoelastic a_ref p_ref ε (kinkPoint a_ref p_ref Sbar ε) = Sbar := by
  unfold invDemandIsoelastic kinkPoint
  have hx : (0:ℝ) ≤ p_ref / Sbar := le_of_lt (div_pos hp hS)
  have step1 : a_ref / (a_ref * (p_ref / Sbar) ^ (1 / ε)) = (Sbar / p_ref) ^ (1 / ε) := by
    rw [div_mul_eq_div_div, div_self (ne_of_gt ha), one_div, ← Real.inv_rpow hx, inv_div]
  have step2 : ((Sbar / p_ref) ^ (1 / ε)) ^ ε = Sbar / p_ref := by
    rw [← Real.rpow_mul (le_of_lt (div_pos hS hp)), one_div, inv_mul_cancel₀ hε, Real.rpow_one]
  rw [step1, step2]
  field_simp

end MathFin
