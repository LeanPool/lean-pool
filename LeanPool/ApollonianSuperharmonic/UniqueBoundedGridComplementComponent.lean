/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: UniqueBoundedGridComplementComponent]

/-!
# UniqueBoundedGridComplementComponent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For sets of lattice-square centers $B,C\subseteq\mathbb Z[i]$, say that
$C$ is the *unique bounded grid-complement component* of the barrier
$B$ when $C$ is finite, nonempty, four-neighbor connected, and contained
in $B^c$; it is maximal among four-neighbor connected subsets of $B^c$;
and every finite maximal four-neighbor connected subset of $B^c$ equals
$C$.  Here four-neighbor paths take steps $\pm1,\pm i$.  This is the
square-center formulation of the unique bounded complementary component
used in the surrounding-ring argument.
-/
def UniqueBoundedGridComplementComponent
    (barrier component : Set GaussianInt) : Prop :=
-- BODY
  let GridConnected := fun S : Set GaussianInt =>
    S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List GaussianInt,
      p.head? = some x ∧ p.getLast? = some y ∧
      (∀ z ∈ p, z ∈ S) ∧
      ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ →
          b = a + 1 ∨ b = a - 1 ∨
            b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩
  component.Finite ∧ component ⊆ barrierᶜ ∧ GridConnected component ∧
    (∀ D : Set GaussianInt, GridConnected D → component ⊆ D →
      D ⊆ barrierᶜ → D = component) ∧
    ∀ D : Set GaussianInt, D.Finite → D ⊆ barrierᶜ → GridConnected D →
      (∀ E : Set GaussianInt, GridConnected E → D ⊆ E →
        E ⊆ barrierᶜ → E = D) →
      D = component

end ApollonianSuperharmonic

end
