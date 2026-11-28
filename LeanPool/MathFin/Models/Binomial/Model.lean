/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.LinearCombination

/-!
# Binomial-tree option pricing (Cox-Ross-Rubinstein style)

We formalize **discrete-time European option pricing on a binomial tree**.

At each time step, the asset price moves up by factor `u` or down by factor
`d`. Risk-free continuously-compounded rate per step is `r`. Under no-arbitrage
(`d < e^r < u`), there is a unique risk-neutral probability

    q = (e^r - d) / (u - d) ∈ (0, 1),

and the no-arbitrage price of a single-period contingent claim with payoffs
`V_u` (up state) and `V_d` (down state) is

    V_0 = e^{-r} (q · V_u + (1 - q) · V_d).

This file contains:
1. Risk-neutral probability `crrUpProb` and its `(0, 1)`-range bound.
2. Single-period option pricing formula `binomialOptionPriceOnePeriod`.
3. **No-arbitrage replication theorem**: cost of the replicating portfolio
   equals `binomialOptionPriceOnePeriod`.
4. The multi-period (`N`-step) backward-induction price with early exercise on a step set
   `E` (`bermudanPrice`), and its European case `binomialPrice` (`E = ∅`).

The bridge to Black-Scholes (CRR convergence) is proved in
`Models/Binomial/CRRCharFun.lean` (`binomialPrice_call_tendsto_bs`).

## Main definitions

* `crrUpProb`: the risk-neutral up-probability `q = (e^r − d) / (u − d)`.
* `BinomialNoArb`: the no-arbitrage condition `0 < d < e^r < u`.
* `binomialOptionPriceOnePeriod`: the one-period price `e^{−r} (q · V_u + (1 − q) · V_d)`.
* `bermudanPrice`: the tree price by backward induction with early exercise at the steps in a
  set `E`.
* `binomialPrice`: the European tree price, `bermudanPrice` with no exercise dates.

## Main results

* `crrUpProb_mem_Ioo`: under `BinomialNoArb`, `crrUpProb u d r ∈ (0, 1)`.
* `crrUpProb_mul_up_add`: under `BinomialNoArb`, `q · u + (1 − q) · d = e^r`.
* `replicating_portfolio_cost`: for `S₀ > 0` and `BinomialNoArb`, the portfolio with `Δ` shares
  and bond holding `B` that matches `V_u`, `V_d` costs `binomialOptionPriceOnePeriod u d r V_u V_d`;
  `replicating_payoff_up` and `replicating_payoff_down` give its payoffs in the two states.
* `le_bermudanPrice`: at maturity and at every exercise date the price is at least the payoff.
* `bermudanPrice_supermartingale`: the one-period continuation of `bermudanPrice` is at most the
  price.
* `binomialPrice_succ_eq_onePeriod`: the `(n + 1)`-step price is the one-period price of the two
  `n`-step prices at `S · u` and `S · d`.
* `binomialPrice_add`, `binomialPrice_smul`: the price is linear in the payoff.
* `binomialPrice_const`: a constant payoff `c` has price `e^{−n r} · c`.
* `binomialPrice_id`: under `BinomialNoArb`, the payoff `S ↦ S` has price `S` at every `n`.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  1.2

## Tags

Cox–Ross–Rubinstein, binomial tree, risk-neutral probability, replicating portfolio,
backward induction, one-period pricing, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-! ### Risk-neutral up-probability -/

/-- The risk-neutral up-probability `q = (e^r - d) / (u - d)`. -/
noncomputable def crrUpProb (u d r : ℝ) : ℝ :=
  (Real.exp r - d) / (u - d)

/-- No-arbitrage condition for the binomial single-period model:
`d < e^r < u` (and `d > 0`). -/
structure BinomialNoArb (u d r : ℝ) : Prop where
  d_pos : 0 < d
  d_lt : d < Real.exp r
  lt_u : Real.exp r < u

/-- Under no-arbitrage, `u > d`. -/
lemma BinomialNoArb.d_lt_u {u d r : ℝ} (h : BinomialNoArb u d r) : d < u :=
  lt_trans h.d_lt h.lt_u

/-- Under no-arbitrage, `u > 0`. -/
lemma BinomialNoArb.u_pos {u d r : ℝ} (h : BinomialNoArb u d r) : 0 < u :=
  lt_trans h.d_pos h.d_lt_u

/-- Under no-arbitrage, the risk-neutral up-probability is in `(0, 1)`. -/
lemma crrUpProb_mem_Ioo {u d r : ℝ} (h : BinomialNoArb u d r) :
    crrUpProb u d r ∈ Set.Ioo 0 1 := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  refine ⟨?_, ?_⟩
  · unfold crrUpProb
    exact div_pos (by linarith [h.d_lt]) h_ud
  · unfold crrUpProb
    rw [div_lt_one h_ud]; linarith [h.lt_u]

/-- Under no-arbitrage the risk-neutral up-probability `crrUpProb u d r` is a probability in
`ℝ≥0`: the form the `ℝ≥0`-parametrised flip laws (`coinFlipMeasure`, `horizonMeasure`) take. -/
lemma BinomialNoArb.exists_nnreal_crrUpProb {u d r : ℝ} (h : BinomialNoArb u d r) :
    ∃ q : NNReal, q ≤ 1 ∧ crrUpProb u d r = q :=
  ⟨(crrUpProb u d r).toNNReal, Real.toNNReal_le_one.2 (crrUpProb_mem_Ioo h).2.le,
    (Real.coe_toNNReal _ (crrUpProb_mem_Ioo h).1.le).symm⟩

/-- The probability `1 - q = (u - e^r) / (u - d)`. -/
@[pricing =]
lemma one_sub_crrUpProb {u d r : ℝ} (h : BinomialNoArb u d r) :
    1 - crrUpProb u d r = (u - Real.exp r) / (u - d) := by
  unfold crrUpProb
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  field_simp
  ring

/-! ### Single-period option pricing -/

/-- Single-period European option price via the risk-neutral expectation:
`V_0 = e^{-r}(q · V_u + (1-q) · V_d)`. -/
noncomputable def binomialOptionPriceOnePeriod (u d r V_u V_d : ℝ) : ℝ :=
  Real.exp (-r) *
    (crrUpProb u d r * V_u + (1 - crrUpProb u d r) * V_d)

/-- Monotonicity of the one-period continuation: if `V_u ≤ V_u'` and
`V_d ≤ V_d'`, then the one-period prices satisfy the same ordering. -/
lemma binomialOptionPriceOnePeriod_mono {u d r V_u V_u' V_d V_d' : ℝ}
    (h : BinomialNoArb u d r) (hu : V_u ≤ V_u') (hd : V_d ≤ V_d') :
    binomialOptionPriceOnePeriod u d r V_u V_d
      ≤ binomialOptionPriceOnePeriod u d r V_u' V_d' := by
  have hp := crrUpProb_mem_Ioo h
  have : 0 ≤ 1 - crrUpProb u d r := by linarith [hp.2]
  unfold binomialOptionPriceOnePeriod
  gcongr
  exact hp.1.le

/-- **No-arbitrage single-period replication.** For an asset with spot `S_0`
and `BinomialNoArb u d r`, any contingent claim with payoffs `V_u` (in the up
state `S_0 · u`) and `V_d` (down state `S_0 · d`) is replicated by

    Δ = (V_u - V_d) / (S_0 (u - d))  shares of stock,
    B = e^{-r}(u · V_d - d · V_u) / (u - d)  in bonds (at time 0 value).

The cost of this replicating portfolio at time 0 equals
`binomialOptionPriceOnePeriod`. -/
theorem replicating_portfolio_cost {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * S_0 + B = binomialOptionPriceOnePeriod u d r V_u V_d := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_id : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold binomialOptionPriceOnePeriod crrUpProb
  simp only
  field_simp
  linear_combination -(V_u - V_d) * h_exp_id

/-- **Replication payoff: up state.** The replicating portfolio pays `V_u`
when the asset goes up. -/
theorem replicating_payoff_up {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * (S_0 * u) + B * Real.exp r = V_u := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only
  field_simp
  linear_combination (u * V_d - d * V_u) * h_exp_inv

/-- **Replication payoff: down state.** The replicating portfolio pays `V_d`
when the asset goes down. -/
theorem replicating_payoff_down {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * (S_0 * d) + B * Real.exp r = V_d := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only
  field_simp
  linear_combination (u * V_d - d * V_u) * h_exp_inv

/-! ### Multi-period (N-step) backward-induction pricing -/

open scoped Classical in
/-- **The binomial tree price with early exercise at the steps in `E`.**

`bermudanPrice E u d r g n S` is the time-0 value with `n` time steps remaining, current
asset price `S`, and payoff `g` (applied at maturity, and at any step with `k` steps remaining
for `k ∈ E`). The Bellman recursion takes `max(intrinsic, continuation)` exactly at the
steps in `E` and the bare discounted risk-neutral continuation otherwise. This is the one
recursion of the tree: `E = ∅` is the European price (`binomialPrice`) and `E = univ` the
American price (`americanPrice`). -/
noncomputable def bermudanPrice (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, S => g S
  | n + 1, S =>
      if (n + 1) ∈ E then
        max (g S) (binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)))
      else
        binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d))

/-- At maturity (`n = 0`) the price is the payoff `g S`. -/
@[simp]
lemma bermudanPrice_zero (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    bermudanPrice E u d r g 0 S = g S := rfl

/-- Bellman step at an exercise date (`n + 1 ∈ E`): the max of intrinsic value and
continuation. -/
lemma bermudanPrice_succ_of_mem {E : Set ℕ} {n : ℕ} (hn : n + 1 ∈ E) (u d r : ℝ) (g : ℝ → ℝ)
    (S : ℝ) :
    bermudanPrice E u d r g (n + 1) S = max (g S) (binomialOptionPriceOnePeriod u d r
      (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d))) := by
  rw [bermudanPrice, ite_eq_left hn]

/-- Bellman step off the exercise set (`n + 1 ∉ E`): the bare continuation. -/
lemma bermudanPrice_succ_of_notMem {E : Set ℕ} {n : ℕ} (hn : n + 1 ∉ E) (u d r : ℝ)
    (g : ℝ → ℝ) (S : ℝ) :
    bermudanPrice E u d r g (n + 1) S = binomialOptionPriceOnePeriod u d r
      (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)) := by
  rw [bermudanPrice, ite_eq_right hn]

/-- **Supermartingale clause**: the one-period continuation never exceeds the price. -/
lemma bermudanPrice_supermartingale (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialOptionPriceOnePeriod u d r (bermudanPrice E u d r g n (S * u))
      (bermudanPrice E u d r g n (S * d)) ≤ bermudanPrice E u d r g (n + 1) S := by
  by_cases hn : n + 1 ∈ E
  · rw [bermudanPrice_succ_of_mem hn]; exact le_max_right _ _
  · rw [bermudanPrice_succ_of_notMem hn]

/-- **Dominance clause**: at maturity and at every exercise date the price dominates the
intrinsic value. -/
lemma le_bermudanPrice {E : Set ℕ} {n : ℕ} (hn : n = 0 ∨ n ∈ E) (u d r : ℝ) (g : ℝ → ℝ)
    (S : ℝ) : g S ≤ bermudanPrice E u d r g n S := by
  cases n with
  | zero => exact le_rfl
  | succ m =>
    rw [bermudanPrice_succ_of_mem (hn.resolve_left (Nat.succ_ne_zero m))]
    exact le_max_left _ _

/-- Backward-induction binomial tree price: the European price, never exercising early
(`bermudanPrice ∅`).

`binomialPrice u d r g n S` returns the time-0 option value with `n` time steps
remaining, current asset price `S`, and payoff function `g : ℝ → ℝ` (applied at
maturity). At each step, the price is the risk-neutral expectation discounted
by `e^{-r}`. -/
noncomputable def binomialPrice (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  bermudanPrice ∅ u d r g

/-- At maturity (`n = 0`) the binomial price is the payoff `g S`. -/
@[simp]
lemma binomialPrice_zero (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    binomialPrice u d r g 0 S = g S := rfl

/-- **One-step consistency**: `binomialPrice u d r g (n+1) S` equals
`binomialOptionPriceOnePeriod u d r V_u V_d` where `V_u, V_d` are the
sub-tree prices for `n` more steps starting from `S·u` and `S·d`. -/
theorem binomialPrice_succ_eq_onePeriod (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g (n + 1) S =
      binomialOptionPriceOnePeriod u d r
        (binomialPrice u d r g n (S * u))
        (binomialPrice u d r g n (S * d)) :=
  bermudanPrice_succ_of_notMem (Set.notMem_empty _) u d r g S

/-- One-step backward recursion: the price at `n+1` is the discounted risk-neutral
average of the prices at the up/down successors. -/
lemma binomialPrice_succ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g (n + 1) S =
      Real.exp (-r) *
        (crrUpProb u d r * binomialPrice u d r g n (S * u) +
         (1 - crrUpProb u d r) * binomialPrice u d r g n (S * d)) :=
  binomialPrice_succ_eq_onePeriod u d r g n S

/-- **Linearity of the binomial price** in the payoff function. -/
lemma binomialPrice_add (u d r : ℝ) (g h : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ g x + h x) n S =
      binomialPrice u d r g n S + binomialPrice u d r h n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, binomialPrice_succ, binomialPrice_succ]
    rw [ih (S * u), ih (S * d)]
    ring

/-- **Scalar homogeneity of the binomial price** in the payoff function. -/
lemma binomialPrice_smul (u d r c : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ c * g x) n S = c * binomialPrice u d r g n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, binomialPrice_succ]
    rw [ih (S * u), ih (S * d)]
    ring

/-- **Constant-payoff price**: a deterministic payoff `c` at maturity has time-0
price `e^{-rn} · c` for `n` steps. -/
theorem binomialPrice_const (u d r c : ℝ) (_h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun _ ↦ c) n S = Real.exp (-(n : ℝ) * r) * c := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    rw [binomialPrice_succ, ih (S * u), ih (S * d)]
    have h_q_complement : crrUpProb u d r + (1 - crrUpProb u d r) = 1 := by ring
    have h_factor : Real.exp (-r) * Real.exp (-(n : ℝ) * r) =
        Real.exp (-((n + 1 : ℕ) : ℝ) * r) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc Real.exp (-r) *
          (crrUpProb u d r * (Real.exp (-(n : ℝ) * r) * c) +
            (1 - crrUpProb u d r) * (Real.exp (-(n : ℝ) * r) * c))
        = Real.exp (-r) * Real.exp (-(n : ℝ) * r) * c *
            (crrUpProb u d r + (1 - crrUpProb u d r)) := by ring
      _ = Real.exp (-r) * Real.exp (-(n : ℝ) * r) * c * 1 := by rw [h_q_complement]
      _ = Real.exp (-((n + 1 : ℕ) : ℝ) * r) * c := by rw [mul_one, h_factor]

/-- **One-step risk-neutral martingale identity** for the binomial up-probability:
`p · u + (1 − p) · d = eʳ`. -/
@[pricing =]
lemma crrUpProb_mul_up_add (u d r : ℝ) (h : BinomialNoArb u d r) :
    crrUpProb u d r * u + (1 - crrUpProb u d r) * d = Real.exp r := by
  have hud : u - d ≠ 0 := sub_ne_zero.mpr h.d_lt_u.ne'
  rw [crrUpProb]
  field_simp
  ring

/-- **Stock-price martingale value**: pricing the payoff `g(S) = S` (the underlying
itself) returns `S` — the discounted stock price is a martingale under the
risk-neutral probability. -/
theorem binomialPrice_id (u d r : ℝ) (h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ x) n S = S := by
  have hmart := crrUpProb_mul_up_add u d r h
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, ih (S * u), ih (S * d),
        show crrUpProb u d r * (S * u) + (1 - crrUpProb u d r) * (S * d)
          = S * (crrUpProb u d r * u + (1 - crrUpProb u d r) * d) from by ring, hmart,
        show Real.exp (-r) * (S * Real.exp r) = S * (Real.exp (-r) * Real.exp r) from by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end MathFin
