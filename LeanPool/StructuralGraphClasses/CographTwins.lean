/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.CotreeCompleteness

/-!
# Twins and nontrivial decompositions of cographs

Twins have the same adjacency to every other vertex; they may be adjacent
(true twins) or nonadjacent (false twins). Decomposition statements require
two nonempty parts and do not constrain the root of an arbitrary unreduced cotree.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Distinct vertices with identical adjacency outside the pair. -/
def AreTwins (G : SimpleGraph V) (a b : V) : Prop :=
  a ≠ b ∧ ∀ x, x ≠ a → x ≠ b → (G.Adj a x ↔ G.Adj b x)

/-- The twin relation is symmetric. -/
theorem AreTwins.symm {a b : V} (h : G.AreTwins a b) : G.AreTwins b a :=
  ⟨h.1.symm, fun x hxb hxa => (h.2 x hxa hxb).symm⟩

/-- Complementation exchanges true and false twins while preserving the twin relation. -/
theorem AreTwins.compl {a b : V} (h : G.AreTwins a b) : Gᶜ.AreTwins a b := by
  refine ⟨h.1, ?_⟩
  intro x hxa hxb
  simp only [compl_adj]
  exact and_congr ⟨fun _ => hxb.symm, fun _ => hxa.symm⟩ (not_congr (h.2 x hxa hxb))

/-- Relabel a pair of twins along a graph isomorphism. -/
theorem AreTwins.mapIso {a b : V} (h : G.AreTwins a b) (f : G ≃g H) :
    H.AreTwins (f a) (f b) := by
  refine ⟨fun he => h.1 (f.injective he), ?_⟩
  intro x hxa hxb
  have ha : f.symm x ≠ a := fun he => hxa (by simpa using congrArg f he)
  have hb : f.symm x ≠ b := fun he => hxb (by simpa using congrArg f he)
  calc
    H.Adj (f a) x ↔ H.Adj (f a) (f (f.symm x)) := by rw [f.apply_symm_apply]
    _ ↔ G.Adj a (f.symm x) := f.map_rel_iff
    _ ↔ G.Adj b (f.symm x) := h.2 (f.symm x) ha hb
    _ ↔ H.Adj (f b) x := by
      simpa only [f.apply_symm_apply] using
        (f.map_rel_iff : H.Adj (f b) (f (f.symm x)) ↔ G.Adj b (f.symm x)).symm

/-- A left-child twin pair remains twins in a disjoint union. -/
theorem AreTwins.sum_left {a b : V} (h : G.AreTwins a b) (H : SimpleGraph W) :
    (G ⊕g H).AreTwins (Sum.inl a) (Sum.inl b) := by
  refine ⟨fun he => h.1 (Sum.inl.inj he), ?_⟩
  rintro (x | x) hxa hxb
  · simpa only [sum_adj] using h.2 x
      (fun he => hxa (congrArg Sum.inl he)) (fun he => hxb (congrArg Sum.inl he))
  · simp

/-- A right-child twin pair remains twins in a disjoint union. -/
theorem AreTwins.sum_right {a b : W} (h : H.AreTwins a b) (G : SimpleGraph V) :
    (G ⊕g H).AreTwins (Sum.inr a) (Sum.inr b) := by
  refine ⟨fun he => h.1 (Sum.inr.inj he), ?_⟩
  rintro (x | x) hxa hxb
  · simp
  · simpa only [sum_adj] using h.2 x
      (fun he => hxa (congrArg Sum.inr he)) (fun he => hxb (congrArg Sum.inr he))

/-- Every cotree with at least two leaves has a twin pair. -/
theorem Cotree.exists_twins (t : Cotree) :
    Nontrivial t.Vertex → ∃ a b, t.graph.AreTwins a b := by
  induction t with
  | empty =>
    intro h
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact PEmpty.elim a
  | leaf =>
    intro h
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact (hab (by cases a; cases b; rfl)).elim
  | union l r ihl ihr =>
    intro h
    by_cases hl : Nontrivial l.Vertex
    · obtain ⟨a, b, hab⟩ := ihl hl
      exact ⟨Sum.inl a, Sum.inl b, hab.sum_left r.graph⟩
    by_cases hr : Nontrivial r.Vertex
    · obtain ⟨a, b, hab⟩ := ihr hr
      exact ⟨Sum.inr a, Sum.inr b, hab.sum_right l.graph⟩
    let : Subsingleton l.Vertex := not_nontrivial_iff_subsingleton.mp hl
    let : Subsingleton r.Vertex := not_nontrivial_iff_subsingleton.mp hr
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    have hleft : l.graph = ⊥ := Subsingleton.elim _ _
    have hright : r.graph = ⊥ := Subsingleton.elim _ _
    refine ⟨a, b, hab, ?_⟩
    intro x hxa hxb
    cases a <;> cases b <;> cases x <;> simp [Cotree.graph, hleft, hright]
  | join l r ihl ihr =>
    intro h
    by_cases hl : Nontrivial l.Vertex
    · obtain ⟨a, b, hab⟩ := ihl hl
      exact ⟨Sum.inl a, Sum.inl b, (hab.compl.sum_left r.graphᶜ).compl⟩
    by_cases hr : Nontrivial r.Vertex
    · obtain ⟨a, b, hab⟩ := ihr hr
      exact ⟨Sum.inr a, Sum.inr b, (hab.compl.sum_right l.graphᶜ).compl⟩
    let : Subsingleton l.Vertex := not_nontrivial_iff_subsingleton.mp hl
    let : Subsingleton r.Vertex := not_nontrivial_iff_subsingleton.mp hr
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    have hleft : l.graphᶜ = ⊥ := Subsingleton.elim _ _
    have hright : r.graphᶜ = ⊥ := Subsingleton.elim _ _
    have ht : (l.graphᶜ ⊕g r.graphᶜ).AreTwins a b := by
      refine ⟨hab, ?_⟩
      intro x hxa hxb
      cases a <;> cases b <;> cases x <;> simp [hleft, hright]
    exact ⟨a, b, ht.compl⟩

/-- Every nontrivial finite cograph has true or false twins. -/
theorem IsCograph.exists_twins [Finite V] [Nontrivial V] (h : G.IsCograph) :
    ∃ a b, G.AreTwins a b := by
  obtain ⟨R⟩ := h.nonempty_cotreeRepresentation
  have hn : Nontrivial R.cotree.Vertex := R.iso.toEquiv.nontrivial
  obtain ⟨a, b, hab⟩ := R.cotree.exists_twins hn
  exact ⟨R.iso a, R.iso b, hab.mapIso R.iso⟩

/-- A connected nontrivial finite cograph admits a join cut with two nonempty parts. -/
theorem IsCograph.exists_join_cut [Finite V] [Nontrivial V]
    (h : G.IsCograph) (hc : G.Preconnected) :
    ∃ s : Set V, s.Nonempty ∧ sᶜ.Nonempty ∧ ∀ u ∈ s, ∀ v ∉ s, G.Adj u v := by
  have hn : ¬Gᶜ.Preconnected := (h.not_preconnected_or_compl).resolve_left (not_not.mpr hc)
  obtain ⟨s, hs, hsc, hcross⟩ := exists_separated_cut_of_not_preconnected hn
  refine ⟨s, hs, hsc, ?_⟩
  intro u hu v hv
  by_contra hadj
  exact hcross u hu v hv ⟨fun he => hv (he ▸ hu), hadj⟩

/-- A cut with every cross edge gives an exact join decomposition. -/
noncomputable def isoJoinInduce (s : Set V)
    (hcross : ∀ u ∈ s, ∀ v ∉ s, G.Adj u v) :
    graphJoin (G.induce s) (G.induce sᶜ) ≃g G := by
  have hh : ∀ u ∈ s, ∀ v ∉ s, ¬Gᶜ.Adj u v := by
    intro u hu v hv h
    exact h.2 (hcross u hu v hv)
  have he (t : Set V) : Gᶜ.induce t = (G.induce t)ᶜ := by
    ext a b
    simp only [induce_adj, compl_adj, Subtype.val_injective.ne_iff]
  have f := (isoSumInduce (G := Gᶜ) s hh).complement
  rw [he s, he sᶜ, compl_compl] at f
  exact f

/-- Assemble the supplied cotrees across a complete join cut. -/
noncomputable def CotreeRepresentation.joinInduce (s : Set V)
    (hcross : ∀ u ∈ s, ∀ v ∉ s, G.Adj u v)
    (L : CotreeRepresentation (G.induce s)) (R : CotreeRepresentation (G.induce sᶜ)) :
    CotreeRepresentation G := (L.graphJoin R).mapIso (isoJoinInduce s hcross)

/-- A disconnected cograph splits as a union of two nonempty cographs. -/
theorem IsCograph.exists_sum_decomposition (h : G.IsCograph)
    (hn : ¬G.Preconnected) :
    ∃ s : Set V, s.Nonempty ∧ sᶜ.Nonempty ∧
      (G.induce s).IsCograph ∧ (G.induce sᶜ).IsCograph ∧
      Nonempty ((G.induce s ⊕g G.induce sᶜ) ≃g G) := by
  obtain ⟨s, hs, hsc, hcross⟩ := exists_separated_cut_of_not_preconnected hn
  exact ⟨s, hs, hsc, h.induce s, h.induce sᶜ, ⟨isoSumInduce s hcross⟩⟩

/-- A connected nontrivial finite cograph splits as a join of two nonempty cographs. -/
theorem IsCograph.exists_join_decomposition [Finite V] [Nontrivial V]
    (h : G.IsCograph) (hc : G.Preconnected) :
    ∃ s : Set V, s.Nonempty ∧ sᶜ.Nonempty ∧
      (G.induce s).IsCograph ∧ (G.induce sᶜ).IsCograph ∧
      Nonempty (graphJoin (G.induce s) (G.induce sᶜ) ≃g G) := by
  obtain ⟨s, hs, hsc, hcross⟩ := h.exists_join_cut hc
  exact ⟨s, hs, hsc, h.induce s, h.induce sᶜ, ⟨isoJoinInduce s hcross⟩⟩

/-- A disconnected finite cograph admits a union-root cotree with nonempty children. -/
theorem IsCograph.exists_union_root [Finite V] (h : G.IsCograph)
    (hn : ¬G.Preconnected) :
    ∃ R : CotreeRepresentation G, ∃ l r : Cotree,
      R.cotree = .union l r ∧ Nonempty l.Vertex ∧ Nonempty r.Vertex := by
  obtain ⟨s, hs, hsc, hcross⟩ := exists_separated_cut_of_not_preconnected hn
  obtain ⟨L⟩ := (h.induce s).nonempty_cotreeRepresentation
  obtain ⟨R⟩ := (h.induce sᶜ).nonempty_cotreeRepresentation
  exact ⟨CotreeRepresentation.unionInduce s hcross L R, L.cotree, R.cotree, rfl,
    ⟨L.iso.symm ⟨hs.choose, hs.choose_spec⟩⟩,
    ⟨R.iso.symm ⟨hsc.choose, hsc.choose_spec⟩⟩⟩

/-- A connected nontrivial finite cograph admits a join-root cotree with nonempty children. -/
theorem IsCograph.exists_join_root [Finite V] [Nontrivial V]
    (h : G.IsCograph) (hc : G.Preconnected) :
    ∃ R : CotreeRepresentation G, ∃ l r : Cotree,
      R.cotree = .join l r ∧ Nonempty l.Vertex ∧ Nonempty r.Vertex := by
  obtain ⟨s, hs, hsc, hcross⟩ := h.exists_join_cut hc
  obtain ⟨L⟩ := (h.induce s).nonempty_cotreeRepresentation
  obtain ⟨R⟩ := (h.induce sᶜ).nonempty_cotreeRepresentation
  exact ⟨CotreeRepresentation.joinInduce s hcross L R, L.cotree, R.cotree, rfl,
    ⟨L.iso.symm ⟨hs.choose, hs.choose_spec⟩⟩,
    ⟨R.iso.symm ⟨hsc.choose, hsc.choose_spec⟩⟩⟩

end SimpleGraph
