/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.Model
public import LeanPool.MathFin.Models.Binomial.FlipPaths
public meta import Lean.Meta.Tactic.NormCast

/-!
# Snell envelope characterization of `bermudanPrice` — scalar and path-space

In the discrete-time binomial tree, the price with early exercise on a step set `E`
(`bermudanPrice E`; `E = univ` is the American price) is the **Snell envelope** of the
payoff `g`: the *smallest* process satisfying intrinsic dominance at the exercise dates and
the one-step supermartingale property. This file proves the characterization at **two
levels**.

**Scalar (Markov) level.** The smallest function `V : ℕ → ℝ → ℝ` with

1. **Intrinsic dominance**: `V n S ≥ g S` at maturity and at every exercise date `n ∈ E`;
2. **One-step supermartingale**: `V (n+1) S ≥ e^{-r}·(q·V n (uS) + (1−q)·V n (dS))`

is `bermudanPrice E` (`bermudanPrice_is_snell_envelope`, with minimality from
`bermudanPrice_le_of_supermartingale_dominating`, which is derived below from the path-space
minimality).

**Path-space level.** On coin-flip paths `ω : ℕ → Bool` — the same pathwise
language as `Models/Binomial/FlipPaths.lean`, where the conditional
expectation w.r.t. the binomial filtration is the explicit node average
`E[X_{k+1} | ℱ_k](ω) = q·X_{k+1}(up child) + (1−q)·X_{k+1}(down child)` —
the envelope `snellAux E q Z j k` of a payoff *process* `Z` is defined by the
backward Bellman recursion (the max with the payoff taken exactly when the number of
steps to go lies in the exercise set `E`), and the four clauses of the Snell theorem are
each proved: payoff dominance (`snellAux_ge_payoff`), the supermartingale
property (`snellAux_supermartingale`), adaptedness — the filtration content
(`pathAdaptedAt_snellAux`) — and **minimality over arbitrary path-processes**
(`snellAux_le_of_supermartingale_of_ge`), a strictly larger competitor class
than the scalar form's Markov candidates.

The **identification theorem** (`snellAux_eq_discounted_bermudanPrice`)
closes the loop: for the discounted intrinsic payoff
`Z_k(ω) = e^{−rk}·g(S_k(ω))` along the spot path
`S_k(ω) = S₀·∏_{i<k}(u if ωᵢ else d)` and risk-neutral `q = crrUpProb`,

  `snellAux E q Z j k ω = e^{−rk} · bermudanPrice E u d r g j (S_k(ω))`.

The scalar Bellman recursion is thereby the Markov instance of the genuine
path-space Snell envelope, and the supermartingale / intrinsic-dominance
statements about the price become clauses of the characterization
(`discounted_bermudanPrice_supermartingale`,
`discounted_intrinsic_le_bermudanPrice`, `bermudanPrice_snell_minimal`).

Monotonicity in the exercise set (`bermudanPrice_mono`, `Models/Binomial/Bermudan.lean`) and
Merton's no-early-exercise theorem for the tree call (`bermudanCallPrice_eq_binomialPrice`,
`MertonAmericanCallTree.lean`) are instances of the minimality, with another exercise-set price
and the European price process as the competitor.

The remaining classical form — `americanPrice = sup over stopping times τ of
E^Q[e^{−rτ} g(S_τ)]` — is downstream work on top of this file's path layer.

## Main definitions

* `spotPath`: the spot path `S_k(ω) = S₀ · ∏_{i<k} (u if ωᵢ else d)` along a coin-flip path.
* `snellAux`: the Snell envelope of a payoff process `Z` indexed by remaining steps `j` and
  time `k`, with exercise allowed at the steps in `E`.
* `snell`: the Snell envelope over horizon `N`, indexed by absolute time `k`.

## Main results

* `bermudanPrice_le_of_supermartingale_dominating`, `bermudanPrice_is_snell_envelope`:
  the scalar characterization, under `BinomialNoArb`.
* `snellAux_ge_payoff` / `snellAux_supermartingale` / `pathAdaptedAt_snellAux` /
  `snellAux_le_of_supermartingale_of_ge`: the four Snell clauses on paths (minimality for
  `q ∈ [0, 1]`).
* `crrUpProb_average_discounted`: the discounted node average, the one-period price at a node.
* `snellAux_eq_discounted_bermudanPrice`: the identification theorem.
* `discounted_bermudanPrice_supermartingale`, `discounted_intrinsic_le_bermudanPrice`,
  `bermudanPrice_snell_minimal`: the price corollaries on paths (minimality under
  `BinomialNoArb`).

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 21.5
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4

## Tags

Snell envelope, optimal stopping, American option, Bellman recursion, supermartingale,
early exercise, MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-! ## The path-space Snell envelope

Coin-flip paths `ω : ℕ → Bool`, payoff *processes* `Z : ℕ → (ℕ → Bool) → ℝ`,
and the node-average conditional expectation, as in
`Models/Binomial/FlipPaths.lean`. -/

variable {E : Set ℕ} {q : ℝ} {Z U : ℕ → (ℕ → Bool) → ℝ}

/-- The **spot path**: `S_k(ω) = S₀ · ∏_{i<k} (u if ωᵢ else d)`. -/
noncomputable def spotPath (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) : ℝ :=
  S₀ * ∏ i ∈ Finset.range k, (if ω i then u else d)

/-- One-step spot recursion along the `k`-th flip. -/
lemma spotPath_update_succ (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) (b : Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k b)
      = spotPath S₀ u d k ω * (if b then u else d) := by
  unfold spotPath
  rw [Finset.prod_range_succ]
  have h_prefix : ∏ i ∈ Finset.range k, (if Function.update ω k b i then u else d)
      = ∏ i ∈ Finset.range k, (if ω i then u else d) :=
    Finset.prod_congr rfl fun i hi ↦ by
      rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
  rw [h_prefix]
  simp [mul_assoc]

/-- Up-child spot: `S_{k+1}(ω, k-th flip up) = S_k(ω) · u`. -/
lemma spotPath_update_succ_true (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k true) = spotPath S₀ u d k ω * u := by
  simpa using spotPath_update_succ S₀ u d k ω true

/-- Down-child spot: `S_{k+1}(ω, k-th flip down) = S_k(ω) · d`. -/
lemma spotPath_update_succ_false (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k false) = spotPath S₀ u d k ω * d := by
  simpa using spotPath_update_succ S₀ u d k ω false

/-- The spot path is adapted: `S_k` depends only on the first `k` flips. -/
lemma pathAdaptedAt_spotPath (S₀ u d : ℝ) (k : ℕ) :
    PathAdaptedAt k (spotPath S₀ u d k) := fun ω ω' h ↦ by
  unfold spotPath
  congr 1
  exact Finset.prod_congr rfl fun i hi ↦ by rw [h i (Finset.mem_range.1 hi)]

open scoped Classical in
/-- **Snell envelope, by remaining steps**: `snellAux E q Z j k` is the envelope
value at time `k` with `j` steps to the horizon. `j = 0`: the payoff;
`j + 1`: the node-average continuation `E[· | ℱ_k]`, maxed with the immediate payoff
exactly when `j + 1 ∈ E` (an exercise date). `E = univ` is the classical Snell envelope. -/
noncomputable def snellAux (E : Set ℕ) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) :
    ℕ → ℕ → (ℕ → Bool) → ℝ
  | 0, k, ω => Z k ω
  | j + 1, k, ω =>
    if (j + 1) ∈ E then
      max (Z k ω)
        (q * snellAux E q Z j (k + 1) (Function.update ω k true)
          + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false))
    else
      q * snellAux E q Z j (k + 1) (Function.update ω k true)
        + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false)

/-- The **Snell envelope** of the payoff process `Z` over horizon `N`,
indexed by absolute time `k`. -/
noncomputable def snell (E : Set ℕ) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (N k : ℕ)
    (ω : ℕ → Bool) : ℝ :=
  snellAux E q Z (N - k) k ω

/-- Envelope step at an exercise date: the max of the payoff and the node-average
continuation. -/
lemma snellAux_succ_of_mem {j : ℕ} (hj : j + 1 ∈ E) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (k : ℕ)
    (ω : ℕ → Bool) :
    snellAux E q Z (j + 1) k ω = max (Z k ω)
      (q * snellAux E q Z j (k + 1) (Function.update ω k true)
        + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false)) := by
  rw [snellAux, ite_eq_left hj]

/-- Envelope step off the exercise set: the bare node-average continuation. -/
lemma snellAux_succ_of_notMem {j : ℕ} (hj : j + 1 ∉ E) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (k : ℕ)
    (ω : ℕ → Bool) :
    snellAux E q Z (j + 1) k ω =
      q * snellAux E q Z j (k + 1) (Function.update ω k true)
        + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false) := by
  rw [snellAux, ite_eq_right hj]

/-- **Dominance clause**: at the horizon and at every exercise date the envelope dominates
the payoff. -/
theorem snellAux_ge_payoff {j : ℕ} (hj : j = 0 ∨ j ∈ E) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ)
    (k : ℕ) (ω : ℕ → Bool) : Z k ω ≤ snellAux E q Z j k ω := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [snellAux_succ_of_mem (hj.resolve_left (Nat.succ_ne_zero j))]
    exact le_max_left _ _

/-- **Supermartingale clause**: the node-average of the next-step envelope is
at most the current envelope — `E[V_{k+1} | ℱ_k] ≤ V_k` in node-average form. -/
theorem snellAux_supermartingale (E : Set ℕ) (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (j k : ℕ)
    (ω : ℕ → Bool) :
    q * snellAux E q Z j (k + 1) (Function.update ω k true)
      + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false)
      ≤ snellAux E q Z (j + 1) k ω := by
  by_cases hj : j + 1 ∈ E
  · rw [snellAux_succ_of_mem hj]; exact le_max_right _ _
  · rw [snellAux_succ_of_notMem hj]

/-- **Adaptedness clause**: the envelope at time `k` depends only on the first
`k` flips — it is `ℱ_k`-measurable, the filtration content of the Snell
theorem. -/
theorem pathAdaptedAt_snellAux (hZ : ∀ n, PathAdaptedAt n (Z n)) :
    ∀ j k, PathAdaptedAt k (snellAux E q Z j k) := by
  intro j
  induction j with
  | zero => exact fun k ↦ hZ k
  | succ j ih =>
    intro k ω ω' hω
    have h_child : ∀ b : Bool,
        snellAux E q Z j (k + 1) (Function.update ω k b)
          = snellAux E q Z j (k + 1) (Function.update ω' k b) := by
      intro b
      refine ih (k + 1) _ _ fun i hi ↦ ?_
      rcases eq_or_ne i k with rfl | hi'
      · simp
      · rw [Function.update_of_ne hi', Function.update_of_ne hi']
        exact hω i (by omega)
    by_cases hj : j + 1 ∈ E
    · rw [snellAux_succ_of_mem hj, snellAux_succ_of_mem hj, hZ k ω ω' hω, h_child true,
        h_child false]
    · rw [snellAux_succ_of_notMem hj, snellAux_succ_of_notMem hj, h_child true, h_child false]

/-- **Minimality clause (Snell)**: any pathwise supermartingale `U` dominating
the payoff at the exercise dates dominates the envelope — over *arbitrary*
path-processes, a strictly larger competitor class than the scalar (Markov) form.
Backward induction from the horizon `H`: at the horizon the envelope is the payoff; at a
step, the continuation is squeezed by the inductive hypothesis averaged through the node
(convexity: `q ∈ [0,1]`) plus `U`'s own supermartingale property, and at an exercise
date the Bellman max is squeezed because `U` also beats the payoff directly. Only the
supermartingale steps `k < H` before the horizon are used, and the exercise dates are the
times `k` with `H - k` steps to go in `E`.
(Adaptedness of `U` is not needed for the bound — only for reading the node
average as a conditional expectation.) -/
theorem snellAux_le_of_supermartingale_of_ge {H : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hU_super : ∀ k < H, ∀ ω, q * U (k + 1) (Function.update ω k true)
        + (1 - q) * U (k + 1) (Function.update ω k false) ≤ U k ω)
    (hU_ge : ∀ k ≤ H, (H - k = 0 ∨ H - k ∈ E) → ∀ ω, Z k ω ≤ U k ω) :
    ∀ j k ω, k + j = H → snellAux E q Z j k ω ≤ U k ω := by
  intro j
  induction j with
  | zero => exact fun k ω hk ↦ hU_ge k (by omega) (Or.inl (by omega)) ω
  | succ j ih =>
    intro k ω hkj
    have hcont : q * snellAux E q Z j (k + 1) (Function.update ω k true)
          + (1 - q) * snellAux E q Z j (k + 1) (Function.update ω k false) ≤ U k ω :=
      calc _ ≤ q * U (k + 1) (Function.update ω k true)
            + (1 - q) * U (k + 1) (Function.update ω k false) :=
            add_le_add (mul_le_mul_of_nonneg_left (ih _ _ (by omega)) hq0)
              (mul_le_mul_of_nonneg_left (ih _ _ (by omega)) (by linarith))
        _ ≤ U k ω := hU_super k (by omega) ω
    by_cases hj : j + 1 ∈ E
    · rw [snellAux_succ_of_mem hj]
      exact max_le (hU_ge k (by omega) (Or.inr (by rwa [show H - k = j + 1 by omega])) ω) hcont
    · rwa [snellAux_succ_of_notMem hj]

/-- **One node of the discounted tree**: discounting the two children at `e^{-r(k+1)}` and
averaging with the risk-neutral weights is `e^{-rk}` times the one-period price. -/
lemma crrUpProb_average_discounted (u d r : ℝ) (k : ℕ) (a b : ℝ) :
    crrUpProb u d r * (Real.exp (-r * (k + 1 : ℕ)) * a)
      + (1 - crrUpProb u d r) * (Real.exp (-r * (k + 1 : ℕ)) * b)
      = Real.exp (-r * k) * binomialOptionPriceOnePeriod u d r a b := by
  unfold binomialOptionPriceOnePeriod
  have hexp : Real.exp (-r * ((k : ℕ) + 1 : ℕ)) = Real.exp (-r * k) * Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- **Identification with the scalar Bellman recursion**: for the discounted
intrinsic payoff `Z_n(ω) = e^{−rn}·g(S_n(ω))` and risk-neutral
`q = crrUpProb u d r`, the path-space Snell envelope *is* the discounted
scalar price with early exercise on `E`:

  `snellAux E q Z j k ω = e^{−rk} · bermudanPrice E u d r g j (S_k(ω))`.

Induction on remaining steps; the discount factors recombine
(`e^{−rk}·e^{−r} = e^{−r(k+1)}`) and the positive factor `e^{−rk}` passes
through the Bellman `max`. -/
theorem snellAux_eq_discounted_bermudanPrice (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ) :
    ∀ j k ω,
      snellAux E (crrUpProb u d r)
        (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j k ω
      = Real.exp (-r * k) * bermudanPrice E u d r g j (spotPath S₀ u d k ω) := by
  intro j
  induction j with
  | zero => intro k ω; rfl
  | succ j ih =>
    intro k ω
    have h_cont : crrUpProb u d r * snellAux E (crrUpProb u d r)
          (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j (k + 1)
          (Function.update ω k true)
        + (1 - crrUpProb u d r) * snellAux E (crrUpProb u d r)
          (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j (k + 1)
          (Function.update ω k false)
        = Real.exp (-r * k) * binomialOptionPriceOnePeriod u d r
            (bermudanPrice E u d r g j (spotPath S₀ u d k ω * u))
            (bermudanPrice E u d r g j (spotPath S₀ u d k ω * d)) := by
      rw [ih (k + 1) (Function.update ω k true), ih (k + 1) (Function.update ω k false),
        spotPath_update_succ_true, spotPath_update_succ_false, crrUpProb_average_discounted]
    by_cases hj : j + 1 ∈ E
    · rw [snellAux_succ_of_mem hj, bermudanPrice_succ_of_mem hj,
        mul_max_of_nonneg _ _ (Real.exp_pos (-r * (k : ℝ))).le]
      exact congrArg₂ max rfl h_cont
    · rw [snellAux_succ_of_notMem hj, bermudanPrice_succ_of_notMem hj]
      exact h_cont

/-- **Snell envelope upper bound (Markov form)**: any function `V : ℕ → ℝ → ℝ` that dominates
the payoff at maturity and at the exercise dates (`hV_g`) and satisfies the one-step
supermartingale condition (`hV_super`) is bounded below by `bermudanPrice E` at every step
and spot.

Combined with `le_bermudanPrice` and `bermudanPrice_supermartingale` (which show
`bermudanPrice E` itself satisfies both conditions), this gives the **Snell envelope
characterization**: `bermudanPrice E` is the smallest such `V`. It is the pathwise minimality
(`snellAux_le_of_supermartingale_of_ge`) for the discounted process
`U_k(ω) = e^{−rk}·V_{n−k}(S_k(ω))` along the spot path from `S`, whose supermartingale step is
`hV_super` at the node (`crrUpProb_average_discounted`), against the discounted intrinsic payoff;
by the identification theorem its envelope at time `0` is `bermudanPrice E n S`. -/
theorem bermudanPrice_le_of_supermartingale_dominating
    {u d r : ℝ} (h : BinomialNoArb u d r) (E : Set ℕ) (g : ℝ → ℝ) (V : ℕ → ℝ → ℝ)
    (hV_g : ∀ n, (n = 0 ∨ n ∈ E) → ∀ S, g S ≤ V n S)
    (hV_super : ∀ n S,
      binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
        V (n + 1) S) :
    ∀ n S, bermudanPrice E u d r g n S ≤ V n S := by
  intro n S
  have key := snellAux_le_of_supermartingale_of_ge (E := E) (q := crrUpProb u d r) (H := n)
    (Z := fun m ω ↦ Real.exp (-r * m) * g (spotPath S u d m ω))
    (U := fun k ω ↦ Real.exp (-r * k) * V (n - k) (spotPath S u d k ω))
    (crrUpProb_mem_Ioo h).1.le (crrUpProb_mem_Ioo h).2.le
    (fun k hk ω ↦ by
      rw [spotPath_update_succ_true, spotPath_update_succ_false, crrUpProb_average_discounted,
        show n - k = (n - (k + 1)) + 1 by omega]
      exact mul_le_mul_of_nonneg_left (hV_super _ _) (Real.exp_pos _).le)
    (fun k _ hk ω ↦ mul_le_mul_of_nonneg_left (hV_g _ hk _) (Real.exp_pos _).le)
    n 0 (fun _ ↦ true) (by omega)
  rwa [snellAux_eq_discounted_bermudanPrice, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul,
    Nat.sub_zero, one_mul, spotPath, Finset.prod_range_zero, mul_one] at key

/-- **Snell envelope theorem (packaged form)**: `bermudanPrice E u d r g` is
the smallest function `V : ℕ → ℝ → ℝ` that simultaneously dominates the
payoff at maturity and at the exercise dates and satisfies the one-step supermartingale
property.

The statement makes the universal characterization visible: for *any* V
satisfying the two properties, `bermudanPrice E ≤ V`. -/
theorem bermudanPrice_is_snell_envelope
    {u d r : ℝ} (h : BinomialNoArb u d r) (E : Set ℕ) (g : ℝ → ℝ) :
    (∀ n, (n = 0 ∨ n ∈ E) → ∀ S, g S ≤ bermudanPrice E u d r g n S) ∧
    (∀ n S,
      binomialOptionPriceOnePeriod u d r
        (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)) ≤
      bermudanPrice E u d r g (n + 1) S) ∧
    (∀ (V : ℕ → ℝ → ℝ),
      (∀ n, (n = 0 ∨ n ∈ E) → ∀ S, g S ≤ V n S) →
      (∀ n S,
        binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
          V (n + 1) S) →
      ∀ n S, bermudanPrice E u d r g n S ≤ V n S) :=
  ⟨fun _ hn S ↦ le_bermudanPrice hn u d r g S,
   bermudanPrice_supermartingale E u d r g,
   bermudanPrice_le_of_supermartingale_dominating h E g⟩

/-- **The discounted price process is a supermartingale** along every
path: for `k < N`, the risk-neutral node-average of the next-step discounted
value is at most the current discounted value —

  `q·X_{k+1}(up) + (1−q)·X_{k+1}(down) ≤ X_k`,  `X_k(ω) = e^{−rk}·V_{N−k}(S_k(ω))`,

for the price `V = bermudanPrice E` with early exercise on any step set `E`. This is the
genuine path-process, conditional-expectation form behind the scalar Bellman-max
dominance. -/
theorem discounted_bermudanPrice_supermartingale (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    {N k : ℕ} (hk : k < N) (ω : ℕ → Bool) :
    crrUpProb u d r * (Real.exp (-r * (k + 1 : ℕ)) *
        bermudanPrice E u d r g (N - (k + 1))
          (spotPath S₀ u d (k + 1) (Function.update ω k true)))
      + (1 - crrUpProb u d r) * (Real.exp (-r * (k + 1 : ℕ)) *
        bermudanPrice E u d r g (N - (k + 1))
          (spotPath S₀ u d (k + 1) (Function.update ω k false)))
      ≤ Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω) := by
  have hjk : N - k = (N - (k + 1)) + 1 := by omega
  calc crrUpProb u d r * (Real.exp (-r * (k + 1 : ℕ)) *
          bermudanPrice E u d r g (N - (k + 1))
            (spotPath S₀ u d (k + 1) (Function.update ω k true)))
        + (1 - crrUpProb u d r) * (Real.exp (-r * (k + 1 : ℕ)) *
          bermudanPrice E u d r g (N - (k + 1))
            (spotPath S₀ u d (k + 1) (Function.update ω k false)))
      = crrUpProb u d r * snellAux E (crrUpProb u d r)
            (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) (N - (k + 1)) (k + 1)
            (Function.update ω k true)
          + (1 - crrUpProb u d r) * snellAux E (crrUpProb u d r)
            (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) (N - (k + 1)) (k + 1)
            (Function.update ω k false) := by
        rw [snellAux_eq_discounted_bermudanPrice, snellAux_eq_discounted_bermudanPrice]
    _ ≤ snellAux E (crrUpProb u d r)
          (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) ((N - (k + 1)) + 1) k ω :=
        snellAux_supermartingale _ _ _ _ _ _
    _ = Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω) := by
        rw [← hjk, snellAux_eq_discounted_bermudanPrice]

/-- **The discounted intrinsic payoff is dominated by the discounted price
process** along every path, at the maturity and at every exercise date — the dominance
clause of the Snell characterization, evaluated at the scalar Bellman recursion. -/
theorem discounted_intrinsic_le_bermudanPrice (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    {N k : ℕ} (hNk : N - k = 0 ∨ N - k ∈ E) (ω : ℕ → Bool) :
    Real.exp (-r * k) * g (spotPath S₀ u d k ω)
      ≤ Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω) := by
  rw [← snellAux_eq_discounted_bermudanPrice]
  exact snellAux_ge_payoff hNk (crrUpProb u d r)
    (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) k ω

/-- **Snell minimality at the price**: any pathwise supermartingale
`U` (w.r.t. the risk-neutral node average, up to the horizon `N`) dominating the discounted
intrinsic payoff at the exercise dates dominates the discounted price along every path.
Together with `discounted_bermudanPrice_supermartingale` and
`discounted_intrinsic_le_bermudanPrice`, this characterizes the value
process as the **smallest supermartingale above the discounted payoff** — the
Snell envelope — over arbitrary path-processes. -/
theorem bermudanPrice_snell_minimal (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (hna : BinomialNoArb u d r) {N : ℕ} {U : ℕ → (ℕ → Bool) → ℝ}
    (hU_super : ∀ k < N, ∀ ω : ℕ → Bool,
      crrUpProb u d r * U (k + 1) (Function.update ω k true)
        + (1 - crrUpProb u d r) * U (k + 1) (Function.update ω k false) ≤ U k ω)
    (hU_ge : ∀ k ≤ N, (N - k = 0 ∨ N - k ∈ E) → ∀ ω : ℕ → Bool,
      Real.exp (-r * k) * g (spotPath S₀ u d k ω) ≤ U k ω)
    {k : ℕ} (hk : k ≤ N) (ω : ℕ → Bool) :
    Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω) ≤ U k ω := by
  rw [← snellAux_eq_discounted_bermudanPrice]
  exact snellAux_le_of_supermartingale_of_ge (crrUpProb_mem_Ioo hna).1.le
    (crrUpProb_mem_Ioo hna).2.le hU_super hU_ge _ k ω (by omega)

/-- **Adaptedness of the discounted value process**: the discounted
value at time `k` depends only on the first `k` flips — its
`ℱ_k`-measurability, the filtration clause of the Snell characterization at
the price. -/
lemma pathAdaptedAt_discounted_bermudanPrice (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (N k : ℕ) :
    PathAdaptedAt k (fun ω ↦ Real.exp (-r * k) *
      bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω)) := fun ω ω' h ↦ by
  change Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω)
      = Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω')
  rw [pathAdaptedAt_spotPath S₀ u d k ω ω' h]

end MathFin
