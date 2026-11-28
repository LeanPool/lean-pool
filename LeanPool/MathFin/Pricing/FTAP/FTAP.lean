/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.EquivMartingaleMeasure
public import LeanPool.MathFin.Probability.Discrete.MartingaleTransform
public import LeanPool.MathFin.Pricing.NoArbitrageCore
public import LeanPool.MathFin.Pricing.ReplicationPricing

/-!
# FTAP (Theorem 2.6.7), forward (⇒) direction: EMM ⇒ no arbitrage

The discrete-time market and the one forward direction of the library's FTAP: existence of an
equivalent martingale measure precludes arbitrage, via the martingale-transform argument, on a
general probability space and up to a finite horizon `T`.

* `IsEMM 𝓕 P S T Q` (`EquivMartingaleMeasure.lean`, for any linearly ordered time) at time `ℕ`:
  `Q` is an equivalent martingale measure for the `F`-valued discounted price `S` up to the
  horizon `T`. On `ℕ` one is built from the one-step martingale identity
  (`IsEMM.of_condExp_succ`).
* `NoArbitrage 𝓕 P S T` — no predictable strategy, bounded up to `T`, turns zero initial wealth
  into a `P`-a.s. nonnegative gain that is not `P`-a.s. zero. The price and the holdings are valued
  in a real inner-product space `F` (several assets), the gains are `⟪φ_{t+1}, S_{t+1} − S_t⟫`
  (`martingaleTransform φ S T`); the scalar market is `F = ℝ`.
* `IsEMM.noArbitrage` — the forward theorem: `IsEMM` ⇒ `NoArbitrage`.
* `IsCompleteMarket 𝓕 P S T` — every bounded `𝓕 T`-claim is replicated, `P`-a.s., by a bounded
  predictable strategy from some initial wealth: `H = x + martingaleTransform φ S T`.
* `tradedGains 𝓕 S T` — the terminal gains `martingaleTransform φ S T` of those strategies; under
  an equivalent martingale measure they are a fair game (`IsEMM.integrable_and_integral_gains`).
* `IsEMM.measure_eq_of_isCompleteMarket` — the second FTAP's easy direction: in a complete market
  two equivalent martingale measures agree on `𝓕 T`. It is `measure_eq_of_replicates`
  (`ReplicationPricing.lean`), shared with the Brownian market, for the class `tradedGains`. The
  converse, on a finite space, is `ftap_two` (`FTAPComplete.lean`).

The finite-Ω market of `FTAPDiscrete.lean` and the one-period market of
`FTAPOnePeriodVector.lean` (a two-step filtration with `𝓕 0 = ⊥`) are instances: their forward
directions call this theorem. So does the continuous-time one,
`ContinuousMarket.isEMM_noArbitrageSimple`, through `IsEMM.sampled`. The backward
directions are proved in the narrower settings: on a finite full-support space over a finite
horizon (`FTAPDiscrete.lean`), for one period on a general space (`FTAPOnePeriodVector.lean`,
with the scalar `FTAPOnePeriod.lean` its `F = ℝ` case), and for one-period finite-state
markets (`FTAPMultiState.lean`, whose two-state case is `FTAPTwoState.lean`).

## Main definitions

* `NoArbitrage`: up to horizon `T`, no bounded predictable strategy turns zero initial wealth into
  a `P`-a.s. nonnegative gain `martingaleTransform φ S T` that is not `P`-a.s. zero.
* `IsCompleteMarket`: up to horizon `T`, every bounded `𝓕 T`-measurable claim is `P`-a.s. equal to
  `x + martingaleTransform φ S T` for some initial wealth `x` and bounded predictable `φ`.
* `tradedGains`: the set of terminal gains `martingaleTransform φ S T` of bounded predictable
  strategies.

## Main results

* `of_condExp_succ`: an equivalent probability measure `Q` under which `S` is adapted and
  integrable up to `T` and satisfies `S t = E_Q[S (t+1) | 𝓕 t]` for `t < T` is an `IsEMM`.
* `exists_martingale_gains`: under an `IsEMM`, the gains of a bounded predictable strategy are the
  terminal value of a `Q`-martingale started at `0`.
* `integral_martingaleTransform`, `integrable_and_integral_gains`: under an `IsEMM` such gains are
  `Q`-integrable with `Q`-mean zero.
* `noArbitrage`: the existence of an `IsEMM` implies `NoArbitrage` (the forward direction of the
  FTAP only).
* `measure_eq_of_isCompleteMarket`: in a complete market any two equivalent martingale measures
  agree on `𝓕 T`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.6.7

## Tags

fundamental theorem of asset pricing, equivalent martingale measure, no arbitrage,
martingale transform, complete market, second FTAP, JEL G13, MSC 91G20, MSC 60G42
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **No arbitrage** up to the horizon `T`: no predictable strategy `φ` (`φ (t+1)` is
`𝓕 t`-measurable for `t < T`), bounded up to `T`, turns zero initial wealth into a `P`-a.s.
nonnegative gain `martingaleTransform φ S T` without making it `P`-a.s. zero. -/
def NoArbitrage (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ φ : ℕ → Ω → F, (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) →
    (∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) →
    0 ≤ᵐ[P] martingaleTransform φ S T → martingaleTransform φ S T =ᵐ[P] 0

/-- **Complete market** up to the horizon `T`: every bounded `𝓕 T`-measurable claim `H` is
replicated, `P`-a.s., by a bounded predictable strategy `φ` from some initial wealth `x`:
`H = x + martingaleTransform φ S T`, the terminal value of the self-financing portfolio holding
`φ_{t+1}` over `(t, t+1]`. The same strategy class as `NoArbitrage`. -/
def IsCompleteMarket (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ H : Ω → ℝ, StronglyMeasurable[𝓕 T] H → (∃ C : ℝ, ∀ ω, |H ω| ≤ C) →
    ∃ (x : ℝ) (φ : ℕ → Ω → F), (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) ∧
      (∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) ∧ H =ᵐ[P] fun ω ↦ x + martingaleTransform φ S T ω

/-- The **terminal gains** up to the horizon `T`: `martingaleTransform φ S T` for the bounded
predictable strategies `φ` of `NoArbitrage` and `IsCompleteMarket`. -/
def tradedGains (𝓕 : Filtration ℕ m0) (S : ℕ → Ω → F) (T : ℕ) : Set (Ω → ℝ) :=
  {G | ∃ φ : ℕ → Ω → F, (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) ∧
    (∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) ∧ G = martingaleTransform φ S T}

omit [CompleteSpace F] in
/-- The transform of the price by a bounded predictable strategy is one of its terminal gains. -/
theorem martingaleTransform_mem_tradedGains {𝓕 : Filtration ℕ m0} {S : ℕ → Ω → F} {T : ℕ}
    {φ : ℕ → Ω → F} (hpred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hbdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) :
    martingaleTransform φ S T ∈ tradedGains 𝓕 S T :=
  ⟨φ, hpred, hbdd, rfl⟩

namespace IsEMM

variable {𝓕 : Filtration ℕ m0} {P Q : Measure Ω} {S : ℕ → Ω → F} {T : ℕ}

/-- **The way an EMM is built**: an equivalent probability measure under which the price is
adapted and integrable up to `T` and satisfies the one-step martingale identity
`S t = E_Q[S (t+1) | 𝓕 t]` for `t < T` (`martingale_min_of_condExp_succ`). -/
theorem of_condExp_succ (hQ : IsEquivProbMeasure P Q)
    (hadapt : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hint : ∀ t ≤ T, Integrable (S t) Q)
    (hmart : ∀ t < T, S t =ᵐ[Q] Q[S (t + 1) | 𝓕 t]) : IsEMM 𝓕 P S T Q :=
  have := hQ.isProb
  ⟨hQ, martingale_min_of_condExp_succ hadapt hint hmart⟩

/-- **The gains of a bounded predictable strategy are a `Q`-martingale started at `0`.** The
transform of the frozen price by the strategy cut off at the horizon (where the frozen price stops
moving) is a bounded predictable transform of a martingale, hence a martingale
(`martingaleTransform_isMartingale`), and at time `T` it is `martingaleTransform φ S T`. -/
theorem exists_martingale_gains (h : IsEMM 𝓕 P S T Q) {φ : ℕ → Ω → F}
    (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) :
    ∃ V : ℕ → Ω → ℝ, Martingale V 𝓕 Q ∧ V 0 = 0 ∧ V T = martingaleTransform φ S T := by
  have := h.isProb
  obtain ⟨K, hK⟩ := hφ_bdd
  let φ' : ℕ → Ω → F := fun n ω ↦ if n ≤ T then φ n ω else 0
  have hsum : martingaleTransform φ' (fun n ↦ S (min n T)) T = martingaleTransform φ S T := by
    funext ω
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have htT : t + 1 ≤ T := Finset.mem_range.mp ht
    simp only [φ', ite_eq_left htT, min_eq_left htT, min_eq_left (t.le_succ.trans htT)]
  exact ⟨_, martingaleTransform_isMartingale h.martingale
      (fun n ↦ by
        rcases lt_or_ge n T with hn | hn
        · simpa only [φ', ite_eq_left (Nat.succ_le_of_lt hn)] using hφ_pred n hn
        · simp only [φ', ite_eq_right (by omega : ¬ n + 1 ≤ T)]
          exact stronglyMeasurable_zero)
      ⟨max K 0, Filter.Eventually.of_forall fun ω n ↦ by
        simp only [φ']
        split_ifs with hn
        · exact (hK n hn ω).trans (le_max_left _ _)
        · simp⟩,
    martingaleTransform_zero _ _, hsum⟩

/-- **Fair game**: the gains of a bounded predictable strategy have `Q`-mean zero. -/
theorem integral_martingaleTransform (h : IsEMM 𝓕 P S T Q) {φ : ℕ → Ω → F}
    (hφ_pred : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K) :
    ∫ ω, martingaleTransform φ S T ω ∂Q = 0 := by
  have := h.isProb
  obtain ⟨V, hV, hV0, hVT⟩ := h.exists_martingale_gains hφ_pred hφ_bdd
  simpa [← hVT, hV0] using (hV.setIntegral_eq (Nat.zero_le T) MeasurableSet.univ).symm

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale measure
precludes arbitrage.

Given an equivalent martingale measure `Q ≈ P` for the discounted price `S` up to the horizon `T`
and a predictable strategy `φ` bounded up to `T`, the discounted P&L
`V_T = ∑_{t<T} ⟪φ_{t+1}(ω), S_{t+1}(ω) − S_t(ω)⟫` (`martingaleTransform φ S T`; for a scalar price,
`F = ℝ`, the product `φ_{t+1} · (S_{t+1} − S_t)`) cannot be `P`-a.s. nonnegative without being
`P`-a.s. zero. The price and the holdings are valued in a real inner-product space `F` (several
assets); the scalar theorem is the case `F = ℝ`.

Proof: the gains are a `Q`-martingale started at `0` (`exists_martingale_gains`); a `Q`-a.s.
nonnegative terminal value of such a martingale vanishes (`martingale_nonneg_terminal_ae_zero`),
and `P ≪ Q` carries the null set over. -/
theorem noArbitrage (h : IsEMM 𝓕 P S T Q) : NoArbitrage 𝓕 P S T := by
  have := h.isProb
  intro φ hφ_pred hφ_bdd hV_nonneg
  obtain ⟨V, hV, hV0, hVT⟩ := h.exists_martingale_gains hφ_pred hφ_bdd
  refine ae_eq_zero_of_nonneg_of_null_pos hV_nonneg ?_
  rw [← hVT]
  exact h.ac' (martingale_nonneg_terminal_ae_zero hV hV0 (by rw [hVT]; exact h.ac.ae_le hV_nonneg))

/-- **Fair game, as a class**: under an equivalent martingale measure every terminal gain of a
bounded predictable strategy is `Q`-integrable with `Q`-mean zero. This is the neutrality
`measure_eq_of_replicates` asks of the class of gains. -/
theorem integrable_and_integral_gains (h : IsEMM 𝓕 P S T Q) {G : Ω → ℝ}
    (hG : G ∈ tradedGains 𝓕 S T) : Integrable G Q ∧ ∫ ω, G ω ∂Q = 0 := by
  have := h.isProb
  obtain ⟨φ, hpred, hbdd, rfl⟩ := hG
  obtain ⟨V, hV, -, hVT⟩ := h.exists_martingale_gains hpred hbdd
  exact ⟨hVT ▸ hV.integrable T, h.integral_martingaleTransform hpred hbdd⟩

/-- **Second FTAP, `complete ⇒ unique`**: in a complete market any two equivalent martingale
measures agree on `𝓕 T`. This is `measure_eq_of_replicates` for the class of gains of bounded
predictable strategies, neutral under every equivalent martingale measure
(`integrable_and_integral_gains`), and completeness is the replication of every indicator. -/
theorem measure_eq_of_isCompleteMarket {Q₁ Q₂ : Measure Ω} (hc : IsCompleteMarket 𝓕 P S T)
    (h₁ : IsEMM 𝓕 P S T Q₁) (h₂ : IsEMM 𝓕 P S T Q₂) {A : Set Ω} (hA : MeasurableSet[𝓕 T] A) :
    Q₁ A = Q₂ A := by
  have := h₁.isProb
  have := h₂.isProb
  refine measure_eq_of_replicates h₁.ac h₂.ac (fun _ ↦ h₁.integrable_and_integral_gains)
    (fun _ ↦ h₂.integrable_and_integral_gains) (𝓕.le T) (fun A hA ↦ ?_) hA
  obtain ⟨x, φ, hpred, hbdd, hrep⟩ := hc (A.indicator 1) (stronglyMeasurable_const.indicator hA)
    ⟨1, fun ω ↦ by by_cases hω : ω ∈ A <;> simp [hω]⟩
  exact ⟨x, _, martingaleTransform_mem_tradedGains hpred hbdd, hrep⟩

end IsEMM

end MathFin
