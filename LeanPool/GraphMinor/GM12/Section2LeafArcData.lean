/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM11.Corners
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# The unique edge at a leaf

For the omitted entry-edge lemma on XII page 243, a vertex with one
half-edge has one incident non-loop edge. Every other edge closure
misses the vertex. A loop would supply two distinct half-edges there.
The incident edge closure is therefore a line with the leaf as one end.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A one-half-edge vertex has a unique incident edge closure, and
that closure is a line starting at the vertex. -/
theorem exists_incident_line_at_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1) :
    ∃ (e : Set S) (u : S), e ∈ Γ.E ∧ u ≠ v ∧
      closure e ∩ Γ.V = {v, u} ∧ IsLineWithEnds (closure e) v u ∧
      ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
  obtain ⟨hss, hne⟩ := Nat.card_eq_one_iff_unique.mp hcard
  obtain ⟨⟨⟨e, b⟩, he, hb⟩⟩ := hne
  have hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
    intro f hf hfe hvf
    obtain ⟨b', hb'⟩ := exists_end_eq hγ hf hv hvf
    have heq := congrArg (fun k : halfEdges Γ γ v => k.val.1)
      (hss.elim ⟨(f, b'), hf, hb'⟩ ⟨(e, b), he, hb⟩)
    exact hfe heq
  have hvcl : v ∈ closure e := hb ▸ end_mem_closure hγ he b
  rcases Γ.edge_cond e he with ⟨u, w, huw, hcap, hL⟩ | ⟨u, hcap, _⟩
  · have hvends : v ∈ ({u, w} : Set S) := hcap ▸ (show v ∈ closure e ∩ Γ.V from ⟨hvcl, hv⟩)
    rcases hvends with rfl | rfl
    · exact ⟨e, w, he, huw.symm, hcap, hL, hleaf⟩
    · exact ⟨e, u, he, huw, by simpa only [pair_comm] using hcap, hL.symm, hleaf⟩
  · have hend : ∀ c, γ e (endOf c) = v := by
      intro c
      have h₁ : γ e (endOf c) ∈ closure e ∩ Γ.V := by
        refine ⟨end_mem_closure hγ he c, ?_⟩
        cases c
        · exact hγ.zero e he
        · exact hγ.one e he
      have h₂ : v ∈ closure e ∩ Γ.V := ⟨hvcl, hv⟩
      rw [hcap] at h₁ h₂
      exact h₁.trans h₂.symm
    have heq := congrArg (fun k : halfEdges Γ γ v => k.val.2)
      (hss.elim ⟨(e, true), he, hend true⟩ ⟨(e, false), he, hend false⟩)
    simp at heq

end GraphMinor.GM12
