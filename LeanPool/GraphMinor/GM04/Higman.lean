/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Data.Finset.Defs

/-!
# The theorem of Higman quoted as Graph Minors IV, (8.3)

Graph Minors IV, (8.3) (page 249), quoting G. Higman, *Ordering by divisibility in abstract
algebras*, Proc. London Math. Soc. (3) 2 (1952) 326–336: "(8.3) *Let $\Omega$ be a well-quasi
-order, and let $X_i$ ($i = 1, 2, \dots$) be a countable sequence of finite subsets of $E(\Omega)$.
Then there exists an infinite subset $I \subseteq \{1, 2, \dots\}$ with the property that for all
$i$, $i' \in I$ with $i < i'$ there is an injection $\alpha \colon X_i \to X_{i'}$ such that $x \le
\alpha(x)$ for all $x \in X_i$.*"

In the proof of (8.4) the paper applies (8.3) to sets of edges, each labelled by an element of a
well-quasi-order, where different edges may have the same label. `Higman83Statement` is therefore
stated for finite sets `Xᵢ` of a type `κ` with labels `ℓ i : κ → Ω`. The statement as printed is
the case `κ = Ω`, `ℓ i = id`.
-/

@[expose] public section

namespace GraphMinor.GM04

/-- Graph Minors IV, (8.3), for labelled finite sets: for every sequence of finite sets `X i` with
labels `ℓ i` in a well-quasi-order `Ω`, there is an infinite set `I` of indices such that for all
`i < i'` in `I` some injection `g : X i → X i'` satisfies `ℓ i x ≤ ℓ i' (g x)` for all `x ∈ X i`. -/
def Higman83Statement : Prop :=
  ∀ {κ Ω : Type*} [Preorder Ω], WellQuasiOrderedLE Ω → ∀ (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω),
    ∃ I : Set ℕ, I.Infinite ∧ ∀ i ∈ I, ∀ i' ∈ I, i < i' →
      ∃ g : κ → κ, Set.InjOn g (X i) ∧ Set.MapsTo g (X i) (X i') ∧
        ∀ x ∈ X i, ℓ i x ≤ ℓ i' (g x)

end GraphMinor.GM04
