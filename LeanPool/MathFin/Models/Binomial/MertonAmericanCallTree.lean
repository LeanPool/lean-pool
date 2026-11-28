/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.American
public import LeanPool.MathFin.Models.Binomial.Bermudan
public import LeanPool.MathFin.Models.Binomial.CRRClosedForm
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Merton 1973 in the binomial tree

Classical Merton (1973) result extended from continuous-time Black-Scholes to
the discrete-time binomial tree.

**Theorem.** In a binomial tree with no dividends (`g(S) = max(S − K, 0)`) under
`BinomialNoArb u d r`, a nonnegative risk-free rate `r ≥ 0` and a nonnegative strike `K ≥ 0`,
the American call
price equals the European call price at every step `n` and every spot `S`:

  `americanPrice u d r g n S = binomialPrice u d r g n S`.

**Mathematical content.** At every interior node, the *continuation value*
(discounted risk-neutral expectation of the next-step value) dominates the
*immediate-exercise value* (the call's intrinsic payoff `max(S − K, 0)`).
Hence the Bellman `max(intrinsic, continuation)` always selects the
continuation, and `americanPrice` equals `binomialPrice`.

The substantive lemma is **`call_one_period_continuation_dominates_intrinsic`**:
the one-period continuation `e^{−r} · E^Q[max(S' − K, 0)]` is bounded below
by `max(S − K, 0)` for `r ≥ 0`. The proof combines:

1. *Convexity of `max(·, 0)`*: `q · max(a, 0) + (1 − q) · max(b, 0) ≥
   max(q · a + (1 − q) · b, 0)` (Jensen for the positive part).
2. *Martingale identity*: `q · u + (1 − q) · d = e^r` under no-arbitrage.
3. *Forward discount*: `K · e^{−r} ≤ K` for `r ≥ 0`.

Steps 1 and 2 together give `continuation ≥ max(S · e^{−r} · e^r − K · e^{−r}, 0)`
= `max(S − K · e^{−r}, 0)`. Step 3 gives `max(S − K · e^{−r}, 0) ≥
max(S − K, 0)`.

The one-period dominance is the binomial-tree counterpart of `bsV_ge_forward_lower_bound` in
`PriceBounds.lean` (the European call dominates the discounted forward payoff). In continuous
time the library proves that dominance but not the American = European equality; here the tree
version of the equality is proved, and its CRR limit is the Black–Scholes call
(`crr_americanCall_tendsto_bs`).

## Main results

* `crrUpProb_mul_up_add` (`Models/Binomial/Model.lean`): `q · u + (1 − q) · d = e^r` under no-arb.
* `weighted_max_zero_ge`: convexity inequality for `max(·, 0)` (Jensen).
* `call_one_period_continuation_dominates_intrinsic`: under `BinomialNoArb`, `r ≥ 0`, `K ≥ 0`,
  the one-period continuation of the call payoff dominates the intrinsic value.
* `call_intrinsic_le_binomialPrice`: under the same hypotheses, the intrinsic value
  `max(S − K, 0)` is bounded above by the European call's binomial price at every step
  `n` (multi-step extension of the one-period dominance, by induction).
* `bermudanCallPrice_eq_binomialPrice`: under `BinomialNoArb`, `r ≥ 0`, `K ≥ 0`, for every
  exercise set `E`, the `E`-exercise call price
  equals the European call price at every step, the European price process being a martingale
  above the payoff and hence above the Snell envelope `bermudanPrice E`; the reverse inequality is
  `bermudanPrice_mono` (`Models.Binomial.Bermudan`) for `∅ ⊆ E`.
* `americanCallPrice_eq_binomialPrice`: **American call = European call**
  for the non-dividend call in the binomial tree (Merton 1973), under `BinomialNoArb`, `r ≥ 0`,
  `K ≥ 0`, at every step `n` and every spot `S` (the case `E = univ`).
* `crr_americanCall_tendsto_bs`: on the Cox–Ross–Rubinstein tree with `r ≥ 0`, `σ, T, S₀, K > 0` and
  no-arbitrage at every step `n ≥ 1`, the `n`-step American call price converges to the
  Black–Scholes European call price `S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)` (the equality above, transported
  along `binomialPrice_call_tendsto_bs_closed`).

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  §4.5

## Tags

Merton no early exercise, American call, non-dividend call, early exercise premium, binomial tree,
American equals European, MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-- **Convexity inequality for the positive part `max(·, 0)`**: for any
real `a, b` and convex-combination weights `q, 1 − q` with `q ∈ [0, 1]`,

  `max(q · a + (1 − q) · b, 0) ≤ q · max(a, 0) + (1 − q) · max(b, 0)`.

This is Jensen's inequality for the convex function `x ↦ max(x, 0)`,
which is convex as the maximum of the affine `x` and the constant `0`. -/
lemma weighted_max_zero_ge {q a b : ℝ} (hq : 0 ≤ q) (h1q : q ≤ 1) :
    max (q * a + (1 - q) * b) 0 ≤ q * max a 0 + (1 - q) * max b 0 := by
  have h1q_nn : 0 ≤ 1 - q := by linarith
  -- Jensen for the convex `x ↦ max x 0` (`= id ⊔ const 0`), evaluated at `a, b`.
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ ↦ max x 0) :=
    (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
  simpa using hconv.2 (Set.mem_univ a) (Set.mem_univ b) hq h1q_nn (by ring)

/-- **Algebraic identity**: `e^{−r} · max(S · e^r − K, 0) = max(S − K · e^{−r}, 0)`.

`max(·, 0)` is positively homogeneous: `c · max(x, 0) = max(c · x, 0)` for
`c ≥ 0`. Combined with `e^{−r} · e^r = 1`, this gives the discount-shift
identity. -/
lemma exp_neg_mul_max_call_payoff (S K r : ℝ) :
    Real.exp (-r) * max (S * Real.exp r - K) 0 = max (S - K * Real.exp (-r)) 0 := by
  have h_exp_pos : 0 < Real.exp (-r) := Real.exp_pos _
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add]; simp
  by_cases h : 0 ≤ S * Real.exp r - K
  · rw [max_eq_left h]
    have h_lhs_nn : 0 ≤ S - K * Real.exp (-r) := by
      have h1 : Real.exp (-r) * K ≤ Real.exp (-r) * (S * Real.exp r) :=
        mul_le_mul_of_nonneg_left (by linarith) h_exp_pos.le
      have h2 : Real.exp (-r) * (S * Real.exp r) = S := by
        rw [show Real.exp (-r) * (S * Real.exp r) =
              S * (Real.exp (-r) * Real.exp r) from by ring,
            h_exp_inv, mul_one]
      have h3 : Real.exp (-r) * K = K * Real.exp (-r) := mul_comm _ _
      linarith
    rw [max_eq_left h_lhs_nn]
    calc Real.exp (-r) * (S * Real.exp r - K)
        = S * (Real.exp (-r) * Real.exp r) - K * Real.exp (-r) := by ring
      _ = S * 1 - K * Real.exp (-r) := by rw [h_exp_inv]
      _ = S - K * Real.exp (-r) := by ring
  · have h' : S * Real.exp r - K < 0 := not_le.mp h
    rw [max_eq_right h'.le, mul_zero]
    have h_lhs_le : S - K * Real.exp (-r) ≤ 0 := by
      have h1 : Real.exp (-r) * (S * Real.exp r) ≤ Real.exp (-r) * K :=
        mul_le_mul_of_nonneg_left (by linarith : S * Real.exp r ≤ K) h_exp_pos.le
      have h2 : Real.exp (-r) * (S * Real.exp r) = S := by
        rw [show Real.exp (-r) * (S * Real.exp r) =
              S * (Real.exp (-r) * Real.exp r) from by ring,
            h_exp_inv, mul_one]
      have h3 : Real.exp (-r) * K = K * Real.exp (-r) := mul_comm _ _
      linarith
    rw [max_eq_right h_lhs_le]

/-- **Continuation dominates the forward-discounted intrinsic** in the
single-period binomial. For the call payoff `g(S) = max(S − K, 0)`,

  `max(S − K · e^{−r}, 0)
    ≤ e^{−r} · (q · max(uS − K, 0) + (1 − q) · max(dS − K, 0))
    = continuation`.

Combines `weighted_max_zero_ge` (Jensen for max-zero), the martingale identity
(`qu + (1 − q)d = e^r`), and the discount-shift identity. -/
theorem call_one_period_continuation_ge_forward
    {u d r K S : ℝ} (h : BinomialNoArb u d r) :
    max (S - K * Real.exp (-r)) 0 ≤
      binomialOptionPriceOnePeriod u d r
        (max (S * u - K) 0) (max (S * d - K) 0) := by
  set q := crrUpProb u d r with q_def
  have h_q : q ∈ Set.Ioo 0 1 := crrUpProb_mem_Ioo h
  have h_q_pos : 0 < q := h_q.1
  have h_q_lt_one : q < 1 := h_q.2
  have h_exp_pos : 0 < Real.exp (-r) := Real.exp_pos _
  -- Step 1: martingale identity gives q · u + (1 − q) · d = e^r.
  have h_mart : q * u + (1 - q) * d = Real.exp r := crrUpProb_mul_up_add u d r h
  -- Step 2: Jensen for max-zero, with a = uS − K, b = dS − K.
  have h_conv :
      max (q * (S * u - K) + (1 - q) * (S * d - K)) 0 ≤
        q * max (S * u - K) 0 + (1 - q) * max (S * d - K) 0 :=
    weighted_max_zero_ge h_q_pos.le h_q_lt_one.le
  -- The linear combination collapses via the martingale identity:
  -- q · (uS − K) + (1 − q) · (dS − K) = S · (qu + (1 − q)d) − K = S · e^r − K.
  have h_lin :
      q * (S * u - K) + (1 - q) * (S * d - K) = S * Real.exp r - K := by
    have : q * (S * u - K) + (1 - q) * (S * d - K) =
           S * (q * u + (1 - q) * d) - K := by ring
    rw [this, h_mart]
  rw [h_lin] at h_conv
  -- h_conv: max(S e^r − K, 0) ≤ q · max(uS − K, 0) + (1 − q) · max(dS − K, 0).
  -- Multiply by e^{−r} ≥ 0:
  have h_mul := mul_le_mul_of_nonneg_left h_conv h_exp_pos.le
  -- LHS simplifies via exp_neg_mul_max_call_payoff:
  rw [exp_neg_mul_max_call_payoff S K r] at h_mul
  -- Goal RHS is the binomialOptionPriceOnePeriod unfolded:
  unfold binomialOptionPriceOnePeriod
  rw [← q_def]
  exact h_mul

/-- **Continuation dominates intrinsic for `r ≥ 0`**: combines
`call_one_period_continuation_ge_forward` with the forward-discount
inequality `max(S − K · e^{−r}, 0) ≥ max(S − K, 0)` (for `r ≥ 0`, `K ≥ 0`).

The inequality need not be strict, even for `r > 0` and `K > 0`: when the call is out of the
money in both daughter states (`S·u ≤ K`), both sides are `0`. -/
theorem call_one_period_continuation_dominates_intrinsic
    {u d r K S : ℝ} (h : BinomialNoArb u d r) (hr : 0 ≤ r) (hK : 0 ≤ K) :
    max (S - K) 0 ≤
      binomialOptionPriceOnePeriod u d r
        (max (S * u - K) 0) (max (S * d - K) 0) := by
  have h_step1 := call_one_period_continuation_ge_forward (K := K) (S := S) h
  -- max(S − K, 0) ≤ max(S − K · e^{−r}, 0) when K · e^{−r} ≤ K (i.e. r ≥ 0, K ≥ 0).
  have h_exp_le_one : Real.exp (-r) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_K_disc_le : K * Real.exp (-r) ≤ K := by
    have := mul_le_mul_of_nonneg_left h_exp_le_one hK
    simpa using this
  have h_step2 : max (S - K) 0 ≤ max (S - K * Real.exp (-r)) 0 := by
    apply max_le_max
    · linarith
    · exact le_refl _
  linarith

/-! ## Multi-step Merton 1973

The one-period dominance `call_one_period_continuation_dominates_intrinsic`
extends to arbitrary horizons by induction, which puts the intrinsic payoff below the European
price at every step (`call_intrinsic_le_binomialPrice`). The European price process is then a
martingale dominating the payoff, and `americanPrice` is the smallest supermartingale doing so
(the Snell envelope, `bermudanPrice_le_of_supermartingale_dominating`), which gives
American ≤ European.

The reverse inequality `binomialPrice ≤ americanPrice` is `Models.Binomial.Bermudan`'s
`bermudanPrice_mono` for the exercise sets `∅ ⊆ univ` (the European price is a
supermartingale dominating the payoff at maturity, so it is above the smaller envelope).
Together they give equality. -/

/-- **Intrinsic ≤ European binomial price** (multi-step) for the call payoff
with `r ≥ 0, K ≥ 0`.

This is the substantive content of Merton 1973 at multi-step horizons: the
one-period continuation dominance lifts to every step by induction. -/
theorem call_intrinsic_le_binomialPrice {u d r K : ℝ} (h : BinomialNoArb u d r)
    (hr : 0 ≤ r) (hK : 0 ≤ K) :
    ∀ (n : ℕ) (S : ℝ),
      max (S - K) 0 ≤ binomialPrice u d r (fun S' ↦ max (S' - K) 0) n S := by
  intro n
  induction n with
  | zero => intro S; simp
  | succ n ih =>
    intro S
    -- Step 1: one-period dominance bounds the intrinsic by the one-period
    -- continuation of the *payoff* values at the daughter nodes.
    have h_one_step :=
      call_one_period_continuation_dominates_intrinsic
        (u := u) (d := d) (r := r) (K := K) (S := S) h hr hK
    -- Step 2: by induction at the daughter nodes, the payoff values
    -- max(uS - K, 0), max(dS - K, 0) are bounded by the European binomial
    -- prices binomialPrice n (uS), binomialPrice n (dS).
    have h_mono := binomialOptionPriceOnePeriod_mono (h := h)
      (ih (S * u)) (ih (S * d))
    -- Step 3: the one-step European recursion at S equals exactly that
    -- one-period continuation of binomialPrice n at the daughter nodes.
    have h_succ := binomialPrice_succ_eq_onePeriod u d r
      (fun S' ↦ max (S' - K) 0) n S
    linarith

/-- **Merton 1973 (multi-step): no exercise date adds value to the call.** For every exercise set
`E` (any Bermudan schedule), the `E`-exercise tree price of the call equals the European binomial
price, for `r ≥ 0, K ≥ 0`.

The European price process is a martingale (the one-period recursion
`binomialPrice_succ_eq_onePeriod`) that dominates the intrinsic payoff
(`call_intrinsic_le_binomialPrice`), so it dominates the smallest such process, the Snell envelope
`bermudanPrice E` (`bermudanPrice_le_of_supermartingale_dominating`); the reverse inequality is
`bermudanPrice_mono` for `∅ ⊆ E`. -/
theorem bermudanCallPrice_eq_binomialPrice {u d r K : ℝ} (h : BinomialNoArb u d r)
    (hr : 0 ≤ r) (hK : 0 ≤ K) (E : Set ℕ) (n : ℕ) (S : ℝ) :
    bermudanPrice E u d r (fun S' ↦ max (S' - K) 0) n S =
      binomialPrice u d r (fun S' ↦ max (S' - K) 0) n S :=
  le_antisymm
    (bermudanPrice_le_of_supermartingale_dominating h E _ (binomialPrice u d r _)
      (fun n _ S ↦ call_intrinsic_le_binomialPrice h hr hK n S)
      (fun n S ↦ (binomialPrice_succ_eq_onePeriod u d r _ n S).ge) n S)
    (bermudanPrice_mono h _ (Set.empty_subset E) n S)

/-- **Merton 1973 (multi-step, equality form)**: the American call price equals
the European call price at every step in the no-dividend binomial tree, for
`r ≥ 0, K ≥ 0` (the case `E = univ` of `bermudanCallPrice_eq_binomialPrice`). -/
theorem americanCallPrice_eq_binomialPrice {u d r K : ℝ} (h : BinomialNoArb u d r)
    (hr : 0 ≤ r) (hK : 0 ≤ K) (n : ℕ) (S : ℝ) :
    americanPrice u d r (fun S' ↦ max (S' - K) 0) n S =
      binomialPrice u d r (fun S' ↦ max (S' - K) 0) n S :=
  bermudanCallPrice_eq_binomialPrice h hr hK Set.univ n S

/-! ## The CRR American call converges to the Black–Scholes call -/

section CRRLimit

open Filter
open scoped Topology

/-- **The CRR American call converges to the Black–Scholes European call.** On the
Cox–Ross–Rubinstein tree (`u = e^{σ√(T/n)}`, `d = e^{−σ√(T/n)}`, per-step rate `rT/n`) with
`r ≥ 0`, `σ, T, S₀, K > 0` and no-arbitrage at every step `n ≥ 1`, the `n`-step American call
price converges to `S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)` as `n → ∞`. At each `n ≥ 1` the American and
European tree prices coincide (`americanCallPrice_eq_binomialPrice`, the per-step rate
`rT/n` being nonnegative), and the European prices converge
(`binomialPrice_call_tendsto_bs_closed`). -/
theorem crr_americanCall_tendsto_bs {r σ T S₀ K : ℝ} (hr : 0 ≤ r) (hσ : 0 < σ) (hT : 0 < T)
    (hS₀ : 0 < S₀) (hK : 0 < K)
    (hna : ∀ n, 0 < n → BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)) :
    Tendsto (fun n : ℕ ↦ americanPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T) - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T))) :=
  (binomialPrice_call_tendsto_bs_closed hσ hT hS₀ hK hna).congr'
    (eventually_atTop.mpr ⟨1, fun n hn ↦ (americanCallPrice_eq_binomialPrice (hna n hn)
      (mul_nonneg hr (div_nonneg hT.le n.cast_nonneg)) hK.le n S₀).symm⟩)

end CRRLimit

end MathFin
