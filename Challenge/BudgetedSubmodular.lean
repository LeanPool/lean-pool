/-
Copyright (c) 2026 Mikhail Nemerov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Nemerov
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Modified greedy for budgeted monotone submodular maximisation

Source: doi:10.1145/3447386, url:https://arxiv.org/abs/2008.05391
Proposed by: Mikhail Nemerov
Open declarations: `Challenge.BudgetedSubmodular.modifiedGreedy_approx`
Tags: combinatorics, optimization, approximation-algorithms, submodular-functions
MSC: 90C27, 68W25
Estimated size: ~600 lines of Lean

Informal statement:
* `Challenge.BudgetedSubmodular.modifiedGreedy_approx` — For a monotone submodular set function F on
  finite sets with F of the empty set equal to 0, positive costs and a budget B, the better of the
  cost-benefit greedy set and the best single item that fits the budget has value at least (1 -
  1/e)/2 times the value of every set whose total cost is at most B.
-/

public section

namespace Challenge.BudgetedSubmodular

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A monotone set function with diminishing returns (submodular). -/
structure MonoSubmodular (F : Finset ι → ℝ) : Prop where
  mono : ∀ {S U : Finset ι}, S ⊆ U → F S ≤ F U
  dr : ∀ {S U : Finset ι}, S ⊆ U → ∀ x, F (insert x U) - F U ≤ F (insert x S) - F S

/-- The items of `U` outside `G` that still fit the budget `B` next to `G`. -/
noncomputable def fits (c : ι → ℝ) (B : ℝ) (U G : Finset ι) : Finset ι :=
  (U \ G).filter fun x => ∑ y ∈ G, c y + c x ≤ B

/-- One greedy step: add an item of `fits` with the largest gain per unit cost (ties broken
arbitrarily); keep `G` when nothing fits. -/
noncomputable def greedyStep (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U G : Finset ι) :
    Finset ι :=
  if h : (fits c B U G).Nonempty then
    insert (Classical.choose
      ((fits c B U G).exists_max_image (fun x => (F (insert x G) - F G) / c x) h)) G
  else G

/-- The greedy run on the ground set `U`: `U.card` steps from the empty set. -/
noncomputable def greedy (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U : Finset ι) : Finset ι :=
  (greedyStep F c B U)^[U.card] ∅

/-- The best value of a single item of `U` that fits the budget (`0` when none fits). -/
noncomputable def bestSingle (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U : Finset ι) : ℝ :=
  if h : (U.filter fun x => c x ≤ B).Nonempty then
    (U.filter fun x => c x ≤ B).sup' h fun x => F {x}
  else 0

/-- The modified greedy guarantee `(1 - 1/e)/2` (Khuller–Moss–Naor 1999; see Tang et al. 2021,
who prove `0.405` for the same algorithm). -/
theorem modifiedGreedy_approx (F : Finset ι → ℝ) (hF : MonoSubmodular F) (hF0 : F ∅ = 0)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (B : ℝ) (U O : Finset ι) (hOU : O ⊆ U)
    (hOB : ∑ y ∈ O, c y ≤ B) :
    (1 - Real.exp (-1)) / 2 * F O ≤ max (F (greedy F c B U)) (bestSingle F c B U) := sorry

end Challenge.BudgetedSubmodular
