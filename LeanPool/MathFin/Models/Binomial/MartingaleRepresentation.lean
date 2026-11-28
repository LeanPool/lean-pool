/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.PathMeasure
public import LeanPool.MathFin.Probability.Discrete.MartingaleTransform

/-!
# Binomial martingale representation (completeness of the binomial market)

On the binomial tree, with the coin flips i.i.d. `Bernoulli(q)` for `0 < q < 1`
(`coinFlipMeasure q`) and Mathlib's filtration of the flips `flipFiltration` (`ℱₙ = σ(ω₀, …,
ω_{n−1})`, the pullback on `[0, T]` of `horizonFiltration T`), every `Martingale M` is the discrete
stochastic integral of a **predictable** strategy `A` against any non-degenerate martingale `S`:

  `M_N = M_0 + (A · S)_N` (`binomial_martingale_representation`),

where `(A · S)_N(ω) = ∑_{k<N} A_{k+1}(ω)·(S_{k+1}(ω) − S_k(ω))` is the library's
`martingaleTransform`, and predictable is Mathlib's `StronglyAdapted flipFiltration (A ∘ succ)`:
the holding `A_{k+1}` over `(k, k+1]` is `ℱₖ`-strongly measurable, fixed by the first `k` flips.

This is the **martingale representation theorem** in discrete time, the second pillar of the
fundamental theorem of asset pricing (completeness: every contingent claim is replicable). It is
the converse of `martingaleTransform_isMartingale`
(`Probability/Discrete/MartingaleTransform.lean`): there
a predictable bounded `A` turns a martingale into a martingale; here every martingale of the tree
is such a transform of `S`. The hedge ratio is the node-wise *delta* `hedgeRatio M S n`
(`Models/Binomial/FlipPaths.lean`), the change in `M` over the change in `S` across the two children
of
a node. The conditional expectation is the node average (`oneStep_of_martingale`), so the argument
is the pathwise one-period delta hedge `repr_one_step`, telescoped.

The path space `ℕ → Bool` is the setting for the whole tree: the infinite-horizon spot and
claims of `Binomial/`, the contracts' scenarios and the Snell envelope live there, and
`flipFiltration` is the horizon filtration of the finite market pulled back along `flips T`
(`comap_flips_horizonFiltration`), where `FTAPDiscrete` needs finiteness. The representation
needs none, so it is stated once, here.

## Main results

* `binomial_martingale_representation` — for `0 < q < 1` and a martingale `S` whose up and down
  values differ at every node, every martingale of the flip filtration is its initial value plus
  the `martingaleTransform` of a predictable hedge against `S`.
* `binomialPrice_replication` — under `BinomialNoArb` and `S₀ ≠ 0`, the tree price of a European
  claim is the initial capital of a hedge: the representation applied to the discounted tree value
  and the discounted spot.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Theorem 1.2.2

## Tags

martingale representation, market completeness, replication, predictable strategy,
martingale transform, second fundamental theorem, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

variable {q : ℝ≥0} {M S : ℕ → (ℕ → Bool) → ℝ}

/-- **Binomial martingale representation theorem.** Under i.i.d. `Bernoulli(q)` flips with
`0 < q < 1`, every martingale `M` of the flip filtration is its initial value plus the
`martingaleTransform` of a predictable hedge `A` against a martingale `S` whose two children at
every node differ: `M_N = M_0 + ∑_{k<N} A_{k+1}·(S_{k+1} − S_k)`. The holding `A_{k+1}` over
`(k, k+1]` is `ℱₖ`-strongly measurable, i.e. depends only on the first `k` flips; it is the
node-wise delta `hedgeRatio M S k`. The binomial market is complete: every claim is replicable by
a self-financing strategy. -/
theorem binomial_martingale_representation (hq0 : 0 < q) (hq1 : q < 1)
    (hM : Martingale M flipFiltration (coinFlipMeasure q hq1.le))
    (hS : Martingale S flipFiltration (coinFlipMeasure q hq1.le))
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false)) :
    ∃ A : ℕ → (ℕ → Bool) → ℝ, StronglyAdapted flipFiltration (fun n ↦ A (n + 1)) ∧
      ∀ N ω, M N ω = M 0 ω + martingaleTransform A S N ω := by
  refine ⟨fun n ↦ hedgeRatio M S (n - 1), fun n ↦ stronglyMeasurable_flipFiltration_iff.2 ?_, ?_⟩
  · -- predictability: the hedge ratio depends only on the first `n` flips
    intro ω ω' hω
    have hM' := stronglyMeasurable_flipFiltration_iff.1 (hM.stronglyAdapted (n + 1))
    have hS' := stronglyMeasurable_flipFiltration_iff.1 (hS.stronglyAdapted (n + 1))
    simp only [hedgeRatio, Nat.add_sub_cancel, hM'.fixFlip true ω ω' hω,
      hM'.fixFlip false ω ω' hω, hS'.fixFlip true ω ω' hω, hS'.fixFlip false ω ω' hω]
  · -- the representation telescopes from the one-step identity
    intro N ω
    induction N with
    | zero => simp
    | succ N ih =>
      rw [martingaleTransform_real] at ih ⊢
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, Nat.add_sub_cancel,
        ← repr_one_step (oneStep_of_martingale hq0 hq1 hM) (oneStep_of_martingale hq0 hq1 hS)
          hS_nondeg N ω]
      ring

/-- **The tree price is the cost of a hedge.** Under no-arbitrage and `S₀ ≠ 0`, for every payoff
`g` and horizon `N` there is a predictable strategy `H` (`H_{k+1}` is `ℱₖ`-strongly measurable,
it depends only on the first `k` flips) whose `martingaleTransform` against the discounted spot,
added to the tree price, is the discounted payoff on every path:

  `e^{−rN} g(S_N) = binomialPrice u d r g N S₀ + ∑_{k<N} H_{k+1} (S_tilde_{k+1} − S_tilde_k)`.

The two martingales are the discounted tree value (`martingale_discountedTreeValue`) and the
discounted spot (`martingale_discountedSpot`) under `Bernoulli(crrUpProb u d r)` flips. -/
theorem binomialPrice_replication {u d r : ℝ} (h : BinomialNoArb u d r) {S₀ : ℝ} (hS₀ : S₀ ≠ 0)
    (g : ℝ → ℝ) (N : ℕ) :
    ∃ H : ℕ → (ℕ → Bool) → ℝ, StronglyAdapted flipFiltration (fun n ↦ H (n + 1)) ∧ ∀ ω,
      Real.exp (-(r * N)) * g (spotPath S₀ u d N ω) = binomialPrice u d r g N S₀
        + martingaleTransform H (discountedSpot S₀ u d r) N ω := by
  have hp := crrUpProb_mem_Ioo h
  obtain ⟨q, hqcrr⟩ : ∃ q : ℝ≥0, crrUpProb u d r = q := ⟨⟨_, hp.1.le⟩, rfl⟩
  have hq0 : 0 < q := by exact_mod_cast hqcrr ▸ hp.1
  have hq1 : q < 1 := by exact_mod_cast hqcrr ▸ hp.2
  obtain ⟨H, hH, hrep⟩ := binomial_martingale_representation hq0 hq1
    (martingale_discountedTreeValue u d r g N S₀ hq1.le hqcrr)
    (martingale_discountedSpot h S₀ hq1.le hqcrr) (discountedSpot_update_ne h hS₀)
  exact ⟨H, hH, fun ω ↦ by simpa [discountedTreeValue] using hrep N ω⟩

end MathFin
