/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The other disc bounded by a circle in a sphere

The sphere disc theorem supplies two complementary discs with a
given boundary. Its uniqueness clause identifies a given disc as
one of them. The other is the closure of its complement. This
constructs the closed outer face from the disc enclosed by the
wall in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- In a sphere, the closure of a disc's complement is the other disc
with the same boundary. -/
theorem isClosedDisc_closure_compl_of_isSphere {S : Type*}
    [TopologicalSpace S] [T2Space S] (hS : IsSphere S)
    {D : Set S} (hD : IsClosedDisc D) :
    IsClosedDisc (closure Dᶜ) ∧ discBd (closure Dᶜ) = discBd D ∧
      D ∪ closure Dᶜ = univ ∧ D ∩ closure Dᶜ = discBd D := by
  obtain ⟨D₁,D₂,_,h₁,h₂,hb₁,hb₂,hCup,hCap,_,hall⟩ :=
    sphere_disc S hS (discBd D) hD.isOArc_discBd
  have other {A B : Set S} (hB : IsClosedDisc B) (hb : discBd B = discBd D)
      (hu : A ∪ B = univ) (hi : A ∩ B = discBd D) : closure Aᶜ = B := by
    apply subset_antisymm
    · apply closure_minimal _ hB.isCompact.isClosed
      intro x hx
      exact (hu.ge (mem_univ x)).resolve_left hx
    · apply hB.subset_closure_discInt.trans
      apply closure_mono
      intro x hx hxA
      apply hx.2
      rw [hb,← hi]
      exact ⟨hxA,hx.1⟩
  rcases hall D hD rfl with he | he
  · subst D₁
    have hOther := other h₂ hb₂ hCup hCap
    rw [hOther]
    exact ⟨h₂,hb₂,hCup,hCap⟩
  · subst D₂
    have hCup' : D ∪ D₁ = univ := by rw [union_comm,hCup]
    have hCap' : D ∩ D₁ = discBd D := by rw [inter_comm,hCap]
    have hOther := other h₁ hb₁ hCup' hCap'
    rw [hOther]
    exact ⟨h₁,hb₁,hCup',hCap'⟩

end GraphMinor.GM16
