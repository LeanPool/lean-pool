/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Reindexing the paths through the eyes

XII (4.5), page 253, renumbers the external paths by the
crossing edges of the source graph. The endpoint partition
matches their unordered opposite pairs. Reverse a path when
its order differs from the assigned endpoint order.
-/

public section

namespace GraphMinor.GM12

open Set GM14

/-- Reverse an external path while retaining its avoidance and
endpoint conditions. -/
theorem isHPathWithEnds_reverse {α β : Type*} {G H P : Graph α β} {a b : α}
    (h : IsHPathWithEnds G H P a b) : IsHPathWithEnds G H P b a := by
  refine ⟨h.1, h.2.1.symm, h.2.2.1.symm, h.2.2.2.2.1,
    h.2.2.2.1, ?_, h.2.2.2.2.2.2⟩
  exact h.2.2.2.2.2.1.trans (pair_comm a b)

/-- Unordered equality of endpoint pairs suffices for choosing
the orientation of an external path. -/
theorem isHPathWithEnds_of_endpoint_pair_eq
    {S α β : Type*} {G H P : Graph α β} (f : S → α) {a b x y : S}
    (hP : IsHPathWithEnds G H P (f a) (f b))
    (hpair : ({x, y} : Set S) = {a, b}) :
    IsHPathWithEnds G H P (f x) (f y) := by
  rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hP
  · exact isHPathWithEnds_reverse hP

/-- Renumber disjoint external paths by their source-edge
bijection, orienting each to its assigned endpoints. This is
the renumbering step of XII (4.5), page 253. -/
theorem exists_external_paths_reindexed
    {S α β E I : Type*} {G H : Graph α β} (f : S → α)
    (σ : I ≃ E) (ends : E × Bool → S) (a b : I → S)
    (P : I → Graph α β)
    (hP : ∀ i, IsHPathWithEnds G H (P i) (f (a i)) (f (b i)))
    (hPP : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hpairs : ∀ i, ({ends (σ i, false), ends (σ i, true)} : Set S) = {a i, b i}) :
    ∃ R : E → Graph α β,
      (∀ e, IsHPathWithEnds G H (R e) (f (ends (e, false))) (f (ends (e, true)))) ∧
      Pairwise (fun e g => Disjoint (R e).vertexSet (R g).vertexSet) := by
  refine ⟨fun e => P (σ.symm e), ?_, ?_⟩
  · intro e
    have hpair := hpairs (σ.symm e)
    rw [σ.apply_symm_apply] at hpair
    exact isHPathWithEnds_of_endpoint_pair_eq f (hP (σ.symm e)) hpair
  · intro e g heg
    exact hPP (fun h => heg (σ.symm.injective h))

end GraphMinor.GM12
