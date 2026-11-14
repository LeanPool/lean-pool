/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# DiscreteGronwall

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The discrete Grönwall inequality (`l.discrete.gronwall`)

ABK26, §4.3.  The source statement:

> Suppose `H ≥ 0`, `{ε_k}_{k=1}^i ⊂ ℝ₊` and `{a_k}_{k=1}^i` satisfy
> `a_l ≤ H + ∑_{k=1}^{l-1} ε_k a_k` for every `l ∈ {1,…,i}`.  Then
> `a_i ≤ H exp(∑_{k=1}^{i-1} ε_k)`.

and the printed proof is complete: with `S_l := ∑_{k≤l} ε_k a_k` one has `S_l
+ H ≤ (1 + ε_l)(S_{l-1} + H)`, hence `S_{i-1} + H ≤ H ∏_{k<i}(1 + ε_k)`, and
`1 + t ≤ e^t` finishes.  Both steps are reproduced here verbatim as
`gronwallProdBound` and `discrete_gronwall`.

## Reading conventions

* Indices run from `0` with `Finset.range`, so `∑_{k=1}^{l-1}` is
  `∑ k ∈ range l, ε k a k`.  This is a relabelling, not a change of content.
* The conclusion is proved for **every** `l ≤ N` simultaneously, which is what the
  telescoping argument gives for free and what the iteration lemma consumes (it
  feeds every `a_l` back into a sum).  `discrete_gronwall_top` is the source's
  literal single-index conclusion.
* **No sign hypothesis on `a`** is imposed, and none is needed: the proof only
  multiplies the hypothesis by `ε_l ≥ 0` and sums.  This matches the graph's own
  reading of the source hypotheses.
* The source writes `{ε_k} ⊂ ℝ₊` without saying whether `ℝ₊` is `[0,∞)` or
  `(0,∞)`; the recorded ambiguity is immaterial and the weaker `0 ≤ ε k` is used.

`Real.exp` is kept opaque throughout: the only transcendental input is
`Real.add_one_le_exp`, used once, and every other step is `ring`, an explicit
monotonicity lemma, or `linarith only`.

## Scope

`l.discrete.gronwall` is an unfrozen source node; this module is a provider
realization of its content and claims no node closure.

## References

* ABK26, `l.discrete.gronwall`, statement, proof.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Finset

/-- The telescoping core of discrete Grönwall: the running partial sum plus `H` is
dominated by `H ∏ (1 + ε_k)`. -/
theorem gronwallProdBound {N : ℕ} {H : ℝ} {a ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k)
    (hrec : ∀ l ≤ N, a l ≤ H + ∑ k ∈ range l, ε k * a k) :
    ∀ l ≤ N, (∑ k ∈ range l, ε k * a k) + H ≤ H * ∏ k ∈ range l, (1 + ε k) := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
      intro hlN
      have hlN' : l ≤ N := Nat.le_of_succ_le hlN
      have ihl := ih hlN'
      set S : ℝ := ∑ k ∈ range l, ε k * a k with hS
      set P : ℝ := ∏ k ∈ range l, (1 + ε k) with hP
      have hstep : a l ≤ H + S := by
        have h := hrec l hlN'
        rwa [← hS] at h
      have hmul : ε l * a l ≤ ε l * (H + S) :=
        mul_le_mul_of_nonneg_left hstep (hε l)
      have hfac : (0 : ℝ) ≤ 1 + ε l := by linarith only [hε l]
      have hstepprod : (S + H) * (1 + ε l) ≤ (H * P) * (1 + ε l) :=
        mul_le_mul_of_nonneg_right ihl hfac
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ← hS, ← hP]
      calc (S + ε l * a l) + H
          ≤ (S + ε l * (H + S)) + H := by linarith only [hmul]
        _ = (S + H) * (1 + ε l) := by ring
        _ ≤ (H * P) * (1 + ε l) := hstepprod
        _ = H * (P * (1 + ε l)) := by ring

/-- **Discrete Grönwall** (`l.discrete.gronwall`), all-indices form.

If `H ≥ 0`, the `ε_k` are nonnegative and `a_l ≤ H + ∑_{k<l} ε_k a_k` for every
`l ≤ N`, then `a_l ≤ H exp(∑_{k<l} ε_k)` for every `l ≤ N`. -/
theorem discrete_gronwall {N : ℕ} {H : ℝ} {a ε : ℕ → ℝ} (hH : 0 ≤ H)
    (hε : ∀ k, 0 ≤ ε k)
    (hrec : ∀ l ≤ N, a l ≤ H + ∑ k ∈ range l, ε k * a k) :
    ∀ l ≤ N, a l ≤ H * Real.exp (∑ k ∈ range l, ε k) := by
  intro l hlN
  have hprod := gronwallProdBound hε hrec l hlN
  have hstep : a l ≤ H + ∑ k ∈ range l, ε k * a k := hrec l hlN
  have hpe : ∏ k ∈ range l, (1 + ε k) ≤ Real.exp (∑ k ∈ range l, ε k) := by
    calc ∏ k ∈ range l, (1 + ε k)
        ≤ ∏ k ∈ range l, Real.exp (ε k) := by
          refine Finset.prod_le_prod₀ (fun k _ => ?_) fun k _ => ?_
          · linarith only [hε k]
          · linarith only [Real.add_one_le_exp (ε k)]
      _ = Real.exp (∑ k ∈ range l, ε k) := (Real.exp_sum _ _).symm
  have hHprod : H * ∏ k ∈ range l, (1 + ε k) ≤ H * Real.exp (∑ k ∈ range l, ε k) :=
    mul_le_mul_of_nonneg_left hpe hH
  linarith only [hprod, hstep, hHprod]

end Algsuperdiff.Section4.Provider.ExcessDecay
