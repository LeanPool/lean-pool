/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Cotree

/-!
# The inside of a fundamental cycle as a subtree of the dual tree

For a search of the faces through the darts off a spanning tree (`IsSearch`, with root face `F₀`
and the darts `pd G` towards the faces found earlier), the inside of the dart `pd F` of a face
`F ≠ F₀` is the set of faces below `F` in the dual tree: a face `G` lies inside `pd F` exactly
when the dual path from `G` to the root passes through `F`.

`IsSearch.mem_inside_iff` states this as a characterization: any predicate `Q` on faces that is
false at the root, true at `F`, and at every other face equal to its value at the parent
`face (α (pd G))` describes the inside of `pd F`. A program computes such a `Q` by one pass over
the faces in the order of the search, since parents come first.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

namespace Map

namespace SpTree

variable {D P : Type*} {M : Map D P} {T : SpTree M} [DecidableEq D] [DecidableEq P] [Fintype D]
  [Fintype P]

namespace IsSearch

variable {F₀ : M.Face} {ord : M.Face → ℕ} {pd : M.Face → D} (hS : T.IsSearch F₀ ord pd)
include hS

/-- **The inside of `pd F` is the subtree below `F`.** -/
theorem mem_inside_iff (hM : M.IsPlane) {F : M.Face} (hF : F ≠ F₀) (Q : M.Face → Prop)
    (h0 : ¬ Q F₀) (h1 : Q F) (hrec : ∀ G, G ≠ F₀ → G ≠ F → (Q G ↔ Q (M.face (M.α (pd G))))) :
    ∀ G, Q G ↔ G ∈ T.inside (pd F) := by
  set r : M.Face → Prop := fun G => G ∈ T.inside (pd F)
  -- crossing the dart of a face other than `F` keeps the side
  have hstep : ∀ G, G ≠ F₀ → G ≠ F → (r G ↔ r (M.face (M.α (pd G)))) := by
    intro G hG hGF
    have hne1 : pd G ≠ pd F := fun e => hGF (by rw [← hS.face_pd G hG, e, hS.face_pd F hF])
    have hne2 : pd G ≠ M.α (pd F) := by
      intro e
      have hpG : M.face (M.α (pd G)) = F := by rw [e, M.α_α, hS.face_pd F hF]
      have hGp : G = M.face (M.α (pd F)) := by rw [← hS.face_pd G hG, e]
      have o1 := hS.ord_lt G hG
      have o2 := hS.ord_lt F hF
      rw [hpG] at o1
      rw [← hGp] at o2
      omega
    have := iff_of_ne hM (hS.not_isTree G hG) hne1 hne2
    rw [hS.face_pd G hG] at this
    exact this
  have hrF : r F := by
    have := face_mem_inside (T := T) hM (hS.not_isTree F hF)
    rwa [hS.face_pd F hF] at this
  have key : ∀ G, (Q G ∧ r G) ∨ (¬ Q G ∧ (r G ↔ r F₀)) := by
    intro G
    induction hn : ord G using Nat.strong_induction_on generalizing G with
    | _ k ih =>
      by_cases hG0 : G = F₀
      · subst hG0; exact Or.inr ⟨h0, Iff.rfl⟩
      by_cases hGF : G = F
      · subst hGF; exact Or.inl ⟨h1, hrF⟩
      have hq := hrec G hG0 hGF
      have hr := hstep G hG0 hGF
      rcases ih _ (hn ▸ hS.ord_lt G hG0) _ rfl with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨hq.2 a, hr.2 b⟩
      · exact Or.inr ⟨fun h => a (hq.1 h), hr.trans b⟩
  have hpar : ¬ r (M.face (M.α (pd F))) := T.face_α_notMem_inside (pd F)
  have hroot : ¬ r F₀ := by
    rcases key (M.face (M.α (pd F))) with ⟨-, b⟩ | ⟨-, b⟩
    · exact absurd b hpar
    · exact fun h => hpar (b.2 h)
  intro G
  rcases key G with ⟨a, b⟩ | ⟨a, b⟩
  · exact ⟨fun _ => b, fun _ => a⟩
  · exact ⟨fun h => absurd h a, fun h => absurd (b.1 h) hroot⟩

end IsSearch

end SpTree

end Map

end PlanarSeparator
