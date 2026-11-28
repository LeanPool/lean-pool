/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.American

/-!
# Bermudan sandwich: European ≤ Bermudan ≤ American

A Bermudan option's exercise set sits between the European (only at maturity)
and American (any time) exercise sets. As a stopping problem its value is the
maximum over admissible exercise times of the discounted exercise value, and
the maximum is monotone in the exercise set.

The clean abstract statement: for a value function `v : ι → ℝ` and exercise
sets `Eur ⊆ Berm ⊆ Amer`, `sup_Eur v ≤ sup_Berm v ≤ sup_Amer v`. We give the
discrete-time finite version using `Finset.sup'`, which is what the binomial
tree directly produces.

## Main results

* `bermudan_sandwich`: `Eur ⊆ Berm ⊆ Amer ⇒ sup_Eur ≤ sup_Berm ≤ sup_Amer` (`Eur` nonempty)
  (both inequalities, via `Finset.sup'_mono`) — the abstract optimal-stopping form.
* `bermudanPrice_mono`: under `BinomialNoArb`, the genuine CRR-tree price `bermudanPrice E`
  (`Models/Binomial/Model.lean`, the one recursion with `E = ∅` European and `E = univ` American) is
  monotone in the early-exercise step set `E`, as an instance of Snell minimality.
* `binomialPrice_le_bermudanPrice_le_americanPrice`: under `BinomialNoArb`, the sandwich as an
  actual discounted-expectation price ordering (not an abstract `sup'` over a free value).

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.5; 26.6
* [Rogers and Williams][RogersWilliams], Vol 2
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4

## Tags

Bermudan option, exercise dates, European American ordering, optimal stopping, Snell envelope,
option price bounds, MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*} {v : ι → ℝ}

open scoped Classical in
/-- **Bermudan sandwich**: `Eur ⊆ Berm ⊆ Amer` ⇒ the optimal-stopping values
are ordered `European ≤ Bermudan ≤ American` — enlarging the exercise set never
lowers the value. The financial content is the monotonicity of `Finset.sup'`
over the exercise set (`Finset.sup'_mono`); we state the full two-step ordering
directly rather than via single-`sup'_mono` wrapper lemmas. -/
lemma bermudan_sandwich
    {Eur Berm Amer : Finset ι}
    (hEB : Eur ⊆ Berm) (hBA : Berm ⊆ Amer) (hEurNE : Eur.Nonempty)
    (v : ι → ℝ) :
    Eur.sup' hEurNE v ≤ Berm.sup' (hEurNE.mono hEB) v ∧
      Berm.sup' (hEurNE.mono hEB) v ≤ Amer.sup' (hEurNE.mono (hEB.trans hBA)) v :=
  ⟨sup'_mono v hEB hEurNE,
   sup'_mono v hBA (hEurNE.mono hEB)⟩

/-! ## The genuine price-tree Bermudan sandwich

`bermudan_sandwich` above is the abstract optimal-stopping monotonicity on a free
value function. Here is the honest CRR-tree instance: the one recursion `bermudanPrice E`,
with `E = ∅` the European price `binomialPrice` and `E = univ` the American price
`americanPrice`, is monotone in the early-exercise step set `E ⊆ ℕ` — an instance of Snell
minimality — and the sandwich is a genuine price ordering. -/

/-- **Monotone in the exercise set**: enlarging the admissible early-exercise set
never lowers the price. The larger-set price is a supermartingale dominating the payoff at
every exercise date of the smaller set, so it dominates the smaller-set price by Snell
minimality (`bermudanPrice_le_of_supermartingale_dominating`). -/
lemma bermudanPrice_mono {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ)
    {E₁ E₂ : Set ℕ} (hE : E₁ ⊆ E₂) (n : ℕ) (S : ℝ) :
    bermudanPrice E₁ u d r g n S ≤ bermudanPrice E₂ u d r g n S :=
  bermudanPrice_le_of_supermartingale_dominating h E₁ g (bermudanPrice E₂ u d r g)
    (fun _ hn S ↦ le_bermudanPrice (hn.imp_right (@hE _)) u d r g S)
    (bermudanPrice_supermartingale E₂ u d r g) n S

/-- **Bermudan sandwich (genuine price-tree form)**: `European ≤ Bermudan ≤
American` for any admissible early-exercise set `E`, at every step and spot —
the three legs are the actual discounted-expectation CRR recursions, not an
abstract `Finset.sup'` over a free value function. -/
theorem binomialPrice_le_bermudanPrice_le_americanPrice {u d r : ℝ}
    (h : BinomialNoArb u d r) (g : ℝ → ℝ) (E : Set ℕ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g n S ≤ bermudanPrice E u d r g n S ∧
      bermudanPrice E u d r g n S ≤ americanPrice u d r g n S :=
  ⟨bermudanPrice_mono h g (Set.empty_subset E) n S,
   bermudanPrice_mono h g (Set.subset_univ E) n S⟩

end MathFin
