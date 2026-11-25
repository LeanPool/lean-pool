/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs

/-! Proper arrangements of segregations in a surface. -/

@[expose] public section

namespace GraphMinor.GM16

open Set GraphMinor.GM09 GraphMinor.GM14

universe u v w

variable {α : Type u} {β : Type v}

/-- Proper arrangement of a segregation in a surface (Graph Minors XVI, Section 3, page 49):
"An arrangement is *proper* if $\Delta_i \cap \Delta_j = \emptyset$ for all $1 \le i < j \le k$ such
that $|\bar{\Omega}_i|, |\bar{\Omega}_j| > 3$." -/
def IsProperArrangement {S : Type w} [TopologicalSpace S]
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S) : Prop :=
  IsSurfaceArrangement S_seg α_disc α_pt ∧
    ∀ ⦃S₁ : Society α β⦄, S₁ ∈ S_seg → ∀ ⦃S₂ : Society α β⦄, S₂ ∈ S_seg →
      S₁ ≠ S₂ → 3 < S₁.Ω.bar.ncard → 3 < S₂.Ω.bar.ncard →
      Disjoint (α_disc S₁) (α_disc S₂)

end GraphMinor.GM16
