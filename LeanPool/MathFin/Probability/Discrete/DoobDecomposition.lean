/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Martingale.Centering

/-!
# Doob decomposition: existence and uniqueness

Mathlib provides the decomposition operators `MeasureTheory.martingalePart` /
`MeasureTheory.predictablePart` together with four separate facts — the sum
identity, the martingale property of the martingale part, predictability of
the predictable part, `predictablePart f ℱ μ 0 = 0` — and two "essential
uniqueness" lemmas (`martingalePart_add_ae_eq`, `predictablePart_add_ae_eq`).
It never packages them as the textbook theorem.

This file assembles the **Doob decomposition for adapted integrable processes**.
For `f : ℕ → Ω → E` on a filtered measure space, the decomposition is

  `f = M + A`,  `M` a martingale,  `A` predictable with `A 0 = 0`,

and the decomposition is unique in the a.e. sense: any other such pair
`(M', A')` satisfies `M' n =ᵐ[μ] M n` and `A' n =ᵐ[μ] A n` at every time `n`.

Saporito's Theorem 2.2.12 states the submartingale case, where the predictable
compensator is also nondecreasing.

Predictability is encoded as in Mathlib's uniqueness lemmas: the shifted
process `n ↦ A (n + 1)` is `ℱ`-strongly-adapted, i.e. `A (n + 1)` is
`ℱ n`-measurable (`A` is known one step ahead).

## Main results

* `doob_decomposition_unique` — the uniqueness half: any decomposition of `f`
  agrees a.e. with `(martingalePart f ℱ μ, predictablePart f ℱ μ)`.
* `doob_decomposition` — the full existence-and-uniqueness statement.

`Probability/Discrete/SnellDoobDecomposition.lean` applies the uniqueness half to the finite-horizon
Snell
envelope `snellEnvelope` (`Probability/Discrete/SnellEnvelope.lean`) at `X = univ`, whose
compensator is a.e. nonincreasing and constant on the continuation region.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.2.12 (submartingale case)

## Tags

Doob decomposition, predictable part, martingale part, compensator, uniqueness, MSC 60G42, MSC 60G48
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- **Uniqueness of the Doob decomposition.** If `f = M + A` with `M` a
martingale and `A` predictable (`A (n+1)` is `ℱ n`-measurable), integrable,
and null at `0`, then `M` and `A` agree a.e. at every time with Mathlib's
canonical parts `martingalePart f ℱ μ` and `predictablePart f ℱ μ`. -/
theorem doob_decomposition_unique [SigmaFiniteFiltration μ ℱ]
    {f M A : ℕ → Ω → E}
    (hM : Martingale M ℱ μ)
    (hA : StronglyAdapted ℱ fun n ↦ A (n + 1)) (hA0 : A 0 = 0)
    (hA_int : ∀ n, Integrable (A n) μ)
    (hMA : M + A = f) (n : ℕ) :
    M n =ᵐ[μ] martingalePart f ℱ μ n ∧ A n =ᵐ[μ] predictablePart f ℱ μ n := by
  subst hMA
  exact ⟨(martingalePart_add_ae_eq hM hA hA0 hA_int n).symm,
         (predictablePart_add_ae_eq hM hA hA0 hA_int n).symm⟩

/-- **Doob decomposition for adapted processes.** Every adapted
integrable process `f : ℕ → Ω → E` decomposes as `f = M + A` where `M` is a
martingale and `A` is predictable with `A 0 = 0`; the decomposition is unique
up to a.e. equality at every time. The witnesses are Mathlib's
`martingalePart f ℱ μ` and `predictablePart f ℱ μ`. -/
theorem doob_decomposition [SigmaFiniteFiltration μ ℱ]
    {f : ℕ → Ω → E} (hf : StronglyAdapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ) :
    ∃ M A : ℕ → Ω → E,
      (Martingale M ℱ μ ∧ (StronglyAdapted ℱ fun n ↦ A (n + 1)) ∧ A 0 = 0 ∧
        M + A = f) ∧
      ∀ M' A' : ℕ → Ω → E, Martingale M' ℱ μ →
        (StronglyAdapted ℱ fun n ↦ A' (n + 1)) → A' 0 = 0 →
        (∀ n, Integrable (A' n) μ) → M' + A' = f →
        ∀ n, M' n =ᵐ[μ] M n ∧ A' n =ᵐ[μ] A n :=
  ⟨martingalePart f ℱ μ, predictablePart f ℱ μ,
    ⟨martingale_martingalePart hf hf_int, stronglyAdapted_predictablePart,
     predictablePart_zero, martingalePart_add_predictablePart ℱ μ f⟩,
   fun _ _ hM' hA' hA'0 hA'_int hM'A' n ↦
     doob_decomposition_unique hM' hA' hA'0 hA'_int hM'A' n⟩

end MathFin
