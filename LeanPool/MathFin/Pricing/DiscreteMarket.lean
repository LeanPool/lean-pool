/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Parity
public import LeanPool.MathFin.Pricing.FTAP.DalangMortonWillinger
public import LeanPool.MathFin.Pricing.FTAP.FTAPDiscrete
public import LeanPool.MathFin.Pricing.Market
public import LeanPool.MathFin.Probability.Martingales.TimeChange

/-!
# The discrete-time market on the trunk

A model for the instruments of `Contracts/Instruments/Options.lean`, its fundamental theorems of
asset pricing read on the trunk's `Market`, and the seam between the contracts layer and the
multi-period FTAP. A one-asset discrete-time market on a general filtered probability space, a price
`S : ℕ → Ω → ℝ` with an equivalent martingale measure `IsEMM 𝓕 P S T Q`, is a contract model
map: between integer dates the underlying is constant, `discreteAssets S T () t = S ⌊t⌋₊` frozen
at the horizon `T` (the price is a `Q`-martingale only up to `T`). The price `S` is quoted in
units of the numeraire, so cash is not discounted, `D ≡ 1`.

The filtration of the model is `floorFiltration 𝓕`, `t ↦ 𝓕 ⌊t⌋₊`, the time change of `𝓕` along
the step count `t ↦ ⌊t⌋₊` (`Filtration.comp`), and the frozen price is a martingale for it
(`Martingale.comp`). The risk-neutral lemmas of `Pricing/Parity.lean` then
apply as they stand: the forward is worth `S₀ − K` and call minus put is `S₀ − K` at every
maturity (`value_forward`, `value_europeanCall_sub_put`); at an integer maturity `n` the
underlying is `S (min n T)` (`discreteAssets_natCast`). Parity is not re-proved here.

The discrete market is a `Market` (`toMarket`): the frozen price, the floor filtration and the
unit numéraire. An equivalent martingale measure is a pricing measure of it
(`isPricingMeasure_toMarket_of_isEMM`), and a pricing measure, which is equivalent to `P` only on
the information at the horizon, agrees there with an equivalent martingale measure
(`isPricingMeasure_toMarket_iff`, the converse direction through `Martingale.of_comp` and
`Market.IsPricingMeasure.exists_isEquivProbMeasure`). Its price is the contract value with `D ≡ 1`
(`price_toMarket`).

**The fundamental theorem on the trunk.** A pricing measure rules out arbitrage
(`Market.IsPricingMeasure.noArbitrage_toMarket`). On a finite sample space with full support, no
arbitrage is equivalent to the existence of a pricing measure
(`noArbitrage_iff_exists_isPricingMeasure_of_finite`, Harrison–Pliska through `ftap_discrete`); on
a general space the same holds **assuming `ConditionalOnePeriodFTAP`** (the conditional one-period
FTAP, not proved in this library; `noArbitrage_iff_exists_isPricingMeasure`, through the
Dalang–Morton–Willinger reduction). The composite `exists_isPricingMeasure_parity` adds parity:
under that hypothesis an arbitrage-free adapted integrable market has one pricing measure `Q` under
which, for every strike and maturity, the forward's price is `S₀ − K` and the call's price less the
put's is `S₀ − K`.

## Main definitions

* `floorFiltration`: the continuous-time filtration `t ↦ 𝓕 ⌊t⌋₊` of a discrete one, the time
  change `𝓕.comp Nat.floor_mono`.
* `discreteAssets`: the discrete market as a contract model map, frozen at the horizon.
* `toMarket`: the discrete market as a `Market`, with the unit numéraire.

## Main results

* `value_forward`, `value_europeanCall_sub_put`: forward value and put–call parity under an `IsEMM`.
* `isPricingMeasure_toMarket_iff`: the pricing measures of `toMarket` are the measures that agree
  with an `IsEMM` on the information at the horizon.
* `noArbitrage_iff_exists_isPricingMeasure_of_finite`: the finite-`Ω` FTAP on the trunk.
* `noArbitrage_iff_exists_isPricingMeasure`: the FTAP on the trunk, given
  `ConditionalOnePeriodFTAP`.
* `exists_isPricingMeasure_parity`: no arbitrage gives a pricing measure under which parity holds,
  given `ConditionalOnePeriodFTAP`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

discrete-time market, equivalent martingale measure, put–call parity, forward price,
contract model, Dalang–Morton–Willinger, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.DiscreteMarket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The continuous-time filtration `t ↦ 𝓕 ⌊t⌋₊` of a discrete-time one: its time change along the
step count. -/
noncomputable abbrev floorFiltration (𝓕 : Filtration ℕ mΩ) : Filtration ℝ≥0 mΩ :=
  𝓕.comp (Nat.floor_mono (R := ℝ≥0))

/-- A discrete-time price as a contract model map: constant between integer dates and frozen at
the horizon `T`. -/
noncomputable def discreteAssets (S : ℕ → Ω → ℝ) (T : ℕ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ t ω ↦ S (min ⌊t⌋₊ T) ω

/-- At an integer date `n` the underlying is the price at `min n T`. -/
theorem discreteAssets_natCast (S : ℕ → Ω → ℝ) (T n : ℕ) (ω : Ω) :
    discreteAssets S T () (n : ℝ≥0) ω = S (min n T) ω := by
  simp [discreteAssets]

variable {𝓕 : Filtration ℕ mΩ} {P Q : Measure Ω} {S : ℕ → Ω → ℝ} {T : ℕ} {S₀ : ℝ}

/-- Under an equivalent martingale measure the model's (undiscounted) price is a martingale for
the floor filtration. -/
theorem martingale_discreteAssets (hQ : IsEMM 𝓕 P S T Q) :
    Martingale (fun t ω ↦ (fun _ : ℝ≥0 ↦ (1 : ℝ)) t * discreteAssets S T () t ω)
      (floorFiltration 𝓕) Q := by
  simpa only [one_mul, discreteAssets] using hQ.martingale.comp (Nat.floor_mono (R := ℝ≥0))

/-- **The forward's value under an equivalent martingale measure**: the forward struck at `K`, at
any maturity, is worth `S₀ - K` (the price is in numeraire units, `D ≡ 1`), for a price starting
at `S₀`. This is `value_forward_of_martingale`. -/
theorem value_forward (hQ : IsEMM 𝓕 P S T Q) (hS₀ : ∀ ω, S 0 ω = S₀) (K : ℝ) (τ : ℝ≥0) :
    (forward K τ).value Q (fun _ _ ↦ 1) (discreteAssets S T) = S₀ - K := by
  have := hQ.isProb
  have := value_forward_of_martingale (K := K) (T := τ) (𝓕 := floorFiltration 𝓕)
    (martingale_discreteAssets hQ) rfl
    (fun ω ↦ by
      change S (min ⌊(0 : ℝ≥0)⌋₊ T) ω = S₀
      rw [Nat.floor_zero, Nat.zero_min]
      exact hS₀ ω)
  simpa using this

/-- **Put–call parity under an equivalent martingale measure**: at any maturity, call minus put
is `S₀ - K`. This is `value_europeanCall_sub_put_of_martingale`. -/
theorem value_europeanCall_sub_put (hQ : IsEMM 𝓕 P S T Q) (hS₀ : ∀ ω, S 0 ω = S₀) (K : ℝ)
    (τ : ℝ≥0) :
    (europeanCall K τ).value Q (fun _ _ ↦ 1) (discreteAssets S T)
      - (europeanPut K τ).value Q (fun _ _ ↦ 1) (discreteAssets S T) = S₀ - K := by
  have := hQ.isProb
  have := value_europeanCall_sub_put_of_martingale (K := K) (T := τ) (𝓕 := floorFiltration 𝓕)
    (martingale_discreteAssets hQ) rfl
    (fun ω ↦ by
      change S (min ⌊(0 : ℝ≥0)⌋₊ T) ω = S₀
      rw [Nat.floor_zero, Nat.zero_min]
      exact hS₀ ω)
  simpa using this

/-! ### The discrete market as a `Market` -/

/-- **The discrete market as a `Market`**: the price frozen at the horizon (`discreteAssets`), the
floor filtration, and the unit numéraire, since the price is already quoted in numéraire units. The
price need only be adapted up to the horizon. -/
noncomputable def toMarket (P : Measure Ω) (𝓕 : Filtration ℕ mΩ) (S : ℕ → Ω → ℝ) (T : ℕ)
    (hS : ∀ n ≤ T, StronglyMeasurable[𝓕 n] (S n)) : Market Unit Ω where
  P := P
  𝓕 := floorFiltration 𝓕
  asset := discreteAssets S T
  numeraire _ _ := 1
  numeraire_pos _ _ := one_pos
  asset_adapted _ t := by
    change StronglyMeasurable[(floorFiltration 𝓕) t] (S (min ⌊t⌋₊ T))
    rw [floorFiltration, Filtration.comp_apply]
    exact (hS (min ⌊t⌋₊ T) (min_le_right _ _)).mono (𝓕.mono (min_le_left _ _))
  numeraire_adapted _ := stronglyMeasurable_const

variable {hS : ∀ n ≤ T, StronglyMeasurable[𝓕 n] (S n)}

theorem deflator_toMarket : (toMarket P 𝓕 S T hS).deflator = fun _ _ ↦ 1 := by
  funext t ω
  simp [Market.deflator, toMarket]

/-- The price in the discrete market is the contract value with the unit discount `D ≡ 1`. -/
theorem price_toMarket (c : Contract Unit) :
    (toMarket P 𝓕 S T hS).price Q c = c.value Q (fun _ _ ↦ 1) (discreteAssets S T) := by
  change c.value Q (toMarket P 𝓕 S T hS).deflator (discreteAssets S T) = _
  rw [deflator_toMarket]

/-- The deflated asset of the discrete market, frozen at the horizon, is the floor extension of
`n ↦ S (min n T)`. -/
theorem deflated_toMarket_min (u : Unit) :
    (fun t ↦ (toMarket P 𝓕 S T hS).deflated u (min t T)) = fun t ω ↦ S (min ⌊t⌋₊ T) ω := by
  funext t ω
  have hfl : ⌊min t (T : ℝ≥0)⌋₊ = min ⌊t⌋₊ T := by
    rw [Nat.floor_mono.map_min, Nat.floor_natCast]
  simp [Market.deflated, toMarket, discreteAssets, hfl]

/-- **An equivalent martingale measure is a pricing measure of the discrete market**: the floor
extension of the frozen price is a martingale for the floor filtration (`Martingale.comp`). -/
theorem isPricingMeasure_toMarket_of_isEMM (hQ : IsEMM 𝓕 P S T Q) :
    (toMarket P 𝓕 S T hS).IsPricingMeasure T Q :=
  .of_isEquivProbMeasure hQ.toIsEquivProbMeasure fun u ↦ by
    rw [deflated_toMarket_min]
    exact hQ.martingale.comp (Nat.floor_mono (R := ℝ≥0))

/-- **A pricing measure of the discrete market that is equivalent to `P` everywhere is an
equivalent martingale measure**: the frozen price is read back from its floor extension at the
integer dates (`Martingale.of_comp`, with the right inverse `Nat.cast`). -/
theorem isEMM_of_isPricingMeasure_toMarket (hQ : (toMarket P 𝓕 S T hS).IsPricingMeasure T Q)
    (hQP : IsEquivProbMeasure P Q) : IsEMM 𝓕 P S T Q := by
  have hM := hQ.martingale ()
  rw [deflated_toMarket_min] at hM
  exact ⟨hQP, Martingale.of_comp (f := fun n ↦ S (min n T)) (Nat.floor_mono (R := ℝ≥0))
    Nat.mono_cast Nat.floor_natCast hM⟩

/-- **The pricing measures of the discrete market are the measures that agree with an equivalent
martingale measure on the information at the horizon.** A pricing measure is equivalent to `P` on
`𝓕 T` only; it agrees there with one equivalent to `P` everywhere
(`Market.IsPricingMeasure.exists_isEquivProbMeasure`), which is an `IsEMM`. Conversely an `IsEMM`
is a pricing measure, and so is every measure agreeing with a pricing measure on `𝓕 T`
(`Market.IsPricingMeasure.of_trim_eq`). -/
theorem isPricingMeasure_toMarket_iff [IsFiniteMeasure P] :
    (toMarket P 𝓕 S T hS).IsPricingMeasure T Q ↔
      ∃ Q', IsEMM 𝓕 P S T Q' ∧
        Q'.trim ((toMarket P 𝓕 S T hS).𝓕.le T) = Q.trim ((toMarket P 𝓕 S T hS).𝓕.le T) := by
  refine ⟨fun hQ ↦ ?_, fun ⟨Q', hQ', htrim⟩ ↦ (isPricingMeasure_toMarket_of_isEMM hQ').of_trim_eq
    htrim⟩
  have : IsFiniteMeasure (toMarket P 𝓕 S T hS).P := inferInstanceAs (IsFiniteMeasure P)
  obtain ⟨Q', hQP, hQ', htrim⟩ := hQ.exists_isEquivProbMeasure
  exact ⟨Q', isEMM_of_isPricingMeasure_toMarket hQ' hQP, htrim⟩

/-- **A pricing measure rules out arbitrage** in the discrete market: it agrees on the information
at the horizon with an equivalent martingale measure (`isPricingMeasure_toMarket_iff`), which does
(`IsEMM.noArbitrage`). -/
theorem _root_.MathFin.Market.IsPricingMeasure.noArbitrage_toMarket [IsFiniteMeasure P]
    (hQ : (toMarket P 𝓕 S T hS).IsPricingMeasure T Q) : NoArbitrage 𝓕 P S T :=
  (isPricingMeasure_toMarket_iff.1 hQ).elim fun _ h ↦ h.1.noArbitrage

/-- **The fundamental theorem of asset pricing on the trunk, finite sample space**
(Harrison–Pliska): a one-asset discrete market on a finite space whose reference measure charges
every state has no arbitrage iff it has a pricing measure. This is `ftap_discrete` read through
`isPricingMeasure_toMarket_iff`. -/
theorem noArbitrage_iff_exists_isPricingMeasure_of_finite [Finite Ω] [Nonempty Ω]
    [MeasurableSingletonClass Ω] [IsFiniteMeasure P] (hSa : StronglyAdapted 𝓕 S)
    (hP : ∀ ω, 0 < P {ω}) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, (toMarket P 𝓕 S T fun n _ ↦ hSa n).IsPricingMeasure T Q :=
  ⟨fun hNA ↦ ((ftap_discrete 𝓕 P S T hSa hP).1 hNA).imp fun _ ↦ isPricingMeasure_toMarket_of_isEMM,
    fun ⟨_, hQ⟩ ↦ hQ.noArbitrage_toMarket⟩

variable (hS) in
/-- **The fundamental theorem of asset pricing on the trunk, assuming the conditional one-period
FTAP** (Dalang–Morton–Willinger): for an adapted integrable one-asset price, if
`ConditionalOnePeriodFTAP` holds (an hypothesis, **not proved** in this library: see
`DalangMortonWillinger.lean`), no arbitrage is equivalent to the existence of a pricing measure of
the discrete market. Only the forward direction uses the hypothesis. -/
theorem noArbitrage_iff_exists_isPricingMeasure [IsProbabilityMeasure P]
    (hint : ∀ t ≤ T, Integrable (S t) P) (hcond : ConditionalOnePeriodFTAP 𝓕 P S T) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, (toMarket P 𝓕 S T hS).IsPricingMeasure T Q :=
  ⟨fun hNA ↦ (exists_isEMM_of_noArbitrage_of_conditionalFTAP hS hint hcond hNA).imp
    fun _ ↦ isPricingMeasure_toMarket_of_isEMM, fun ⟨_, hQ⟩ ↦ hQ.noArbitrage_toMarket⟩

variable (hS) in
/-- **No arbitrage gives a pricing measure under which the contracts satisfy parity**, assuming the
conditional one-period FTAP. For an adapted integrable one-asset price with
`ConditionalOnePeriodFTAP` (an hypothesis, **not proved** in this library: see
`DalangMortonWillinger.lean`), no arbitrage yields one pricing measure `Q` of `toMarket` under
which, for every strike and maturity, the forward's price is `S₀ - K` and the call's price less the
put's is `S₀ - K`. -/
theorem exists_isPricingMeasure_parity [IsProbabilityMeasure P] (hint : ∀ t ≤ T, Integrable (S t) P)
    (hcond : ConditionalOnePeriodFTAP 𝓕 P S T) (hNA : NoArbitrage 𝓕 P S T)
    (hS₀ : ∀ ω, S 0 ω = S₀) :
    ∃ Q, (toMarket P 𝓕 S T hS).IsPricingMeasure T Q ∧ ∀ (K : ℝ) (τ : ℝ≥0),
      (toMarket P 𝓕 S T hS).price Q (forward K τ) = S₀ - K ∧
      (toMarket P 𝓕 S T hS).price Q (europeanCall K τ)
        - (toMarket P 𝓕 S T hS).price Q (europeanPut K τ) = S₀ - K := by
  obtain ⟨Q, hQ⟩ := exists_isEMM_of_noArbitrage_of_conditionalFTAP hS hint hcond hNA
  refine ⟨Q, isPricingMeasure_toMarket_of_isEMM hQ, fun K τ ↦ ?_⟩
  simp only [price_toMarket]
  exact ⟨value_forward hQ hS₀ K τ, value_europeanCall_sub_put hQ hS₀ K τ⟩

end MathFin.Contracts.DiscreteMarket
