/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Graph

/-!
# Paths of a connected drawing as lines

If two vertices are joined in the graph of a drawing without loops, then a path between them is a
line in the surface (`exists_line_of_connected`). We keep its vertices and edges, for the proof of
(6.6) of Graph Minors XIX.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

theorem exists_line_of_walk (D : Drawing S) (hl : LoopFree D) {X : Set S} (hX : X ⊆ D.V) {a b : X}
  (p : (D.adj.induce X).Walk a b) : p.IsPath → a ≠ b →
    ∃ (Vq : Set S) (Eq : Set (Set S)), (∀ x ∈ Vq, ∃ h : x ∈ X, (⟨x, h⟩ : X) ∈ p.support) ∧ Eq ⊆ D.E
      ∧ a.1 ∈ Vq ∧ b.1 ∈ Vq ∧ (∀ e ∈ Eq, tilde e ⊆ Vq) ∧ IsLineWithEnds (Vq ∪ ⋃₀ Eq) a b := by
  induction p with
  | nil => exact fun _ hab => absurd rfl hab
  | @cons a w b hadj q ih =>
    intro hp hab
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hadj' : D.adj.Adj a.1 w.1 := hadj
    obtain ⟨hne, -, -, e, he, h1, h2⟩ := hadj'
    obtain ⟨u, v, huv, hti, hL⟩ := hl e he
    have hti' : tilde e = {a.1, w.1} := by
      rw [hti] at h1 h2 ⊢
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, mem_singleton_iff.mp h2]
      · rw [mem_singleton_iff.mp h1, h2, pair_comm]
      · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
    have hLe : IsLineWithEnds (closure e) a w := by
      rw [hti] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, mem_singleton_iff.mp h2]; exact hL
      · rw [mem_singleton_iff.mp h1, h2]; exact GraphMinor.GM11.IsLineWithEnds.symm hL
      · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
    have hcl : closure e = e ∪ {a.1, w.1} := by
      rw [← hti', tilde]
      exact (union_sdiff_cancel subset_closure).symm
    by_cases hwb : w = b
    · subst hwb
      refine ⟨{a.1, w.1}, {e}, ?_, singleton_subset_iff.mpr he, .inl rfl, .inr rfl, ?_, ?_⟩
      · rintro x (rfl | rfl)
        · exact ⟨a.2, by simp⟩
        · exact ⟨w.2, by simp⟩
      · rintro f hf
        rw [mem_singleton_iff.mp hf, hti']
      · rw [sUnion_singleton, union_comm, ← hcl]
        exact hLe
    · obtain ⟨Vq, Eq, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih hp.1 hwb
      have hVV : Vq ⊆ D.V := fun x hx => hX (h₁ x hx).1
      have haV : a.1 ∉ Vq := fun h => by
        obtain ⟨h', hs⟩ := h₁ _ h
        exact hp.2 hs
      have hLq : ∀ {x}, x ∈ Vq ∪ ⋃₀ Eq → x ∈ D.V → x ∈ Vq := fun {x} hx hxV => by
        rcases hx with hx | ⟨f, hf, hxf⟩
        · exact hx
        · exact absurd hxV ((h₂ hf).2.1 hxf).2
      have hcap : closure e ∩ (Vq ∪ ⋃₀ Eq) = {w.1} := by
        apply Subset.antisymm
        · rintro x ⟨hxe, hxq⟩
          by_cases hxV : x ∈ D.V
          · have hx1 : x ∈ tilde e := GM19.tilde_eq_inter_V D he ▸ ⟨hxe, hxV⟩
            rw [hti'] at hx1
            rcases hx1 with rfl | hx1
            · exact absurd (hLq hxq hxV) haV
            · exact hx1
          · rcases hxq with hx | ⟨f, hf, hxf⟩
            · exact absurd (hVV hx) hxV
            · have hef := edge_eq_of_mem D he (h₂ hf) hxe (subset_closure hxf) hxV
              subst hef
              have : a.1 ∈ tilde e := by rw [hti']; exact .inl rfl
              exact absurd (h₅ e hf this) haV
        · rintro _ rfl
          exact ⟨hLe.right_mem, .inl h₃⟩
      have hU := IsLineWithEnds.union hLe h₆ hcap
      refine ⟨insert a.1 Vq, insert e Eq, ?_, ?_, .inl rfl, .inr h₄, ?_, ?_⟩
      · rintro x (rfl | hx)
        · exact ⟨a.2, by simp⟩
        · obtain ⟨h, hs⟩ := h₁ x hx
          exact ⟨h, by simp [hs]⟩
      · exact insert_subset he h₂
      · rintro f (rfl | hf) x hx
        · rw [hti'] at hx
          rcases hx with rfl | hx
          · exact .inl rfl
          · exact .inr (mem_singleton_iff.mp hx ▸ h₃)
        · exact .inr (h₅ f hf hx)
      · have e' : insert a.1 Vq ∪ ⋃₀ insert e Eq = closure e ∪ (Vq ∪ ⋃₀ Eq) := by
          rw [sUnion_insert, hcl]
          ext x
          simp only [mem_union, mem_insert_iff, mem_singleton_iff]
          constructor
          · tauto
          · rintro ((h | h | h) | h | h)
            · tauto
            · tauto
            · exact .inl (.inr (h ▸ h₃))
            · tauto
            · tauto
        rw [e']
        exact hU

/-- **A path as a line.** See the module docstring. -/
theorem exists_line_of_connected (D : Drawing S) (hl : LoopFree D) {X : Set S} (hX : X ⊆ D.V) (hc :
  (D.adj.induce X).Preconnected) {a b : S} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) :
    ∃ (Vq : Set S) (Eq : Set (Set S)), Vq ⊆ X ∧ Eq ⊆ D.E ∧ a ∈ Vq ∧ b ∈ Vq ∧
      (∀ e ∈ Eq, tilde e ⊆ Vq) ∧ IsLineWithEnds (Vq ∪ ⋃₀ Eq) a b := by
  obtain ⟨p, hp⟩ := (hc ⟨a, ha⟩ ⟨b, hb⟩).exists_isPath
  obtain ⟨Vq, Eq, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_line_of_walk D hl hX p hp (fun h => hab
    (congrArg Subtype.val h))
  exact ⟨Vq, Eq, fun x hx => (h₁ x hx).1, h₂, h₃, h₄, h₅, h₆⟩

end GraphMinor.GM19
