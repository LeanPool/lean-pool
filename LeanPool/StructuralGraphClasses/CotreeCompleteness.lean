/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.CographDecomposition
public import LeanPool.StructuralGraphClasses.CotreeOperations

/-!
# Every finite cograph has a cotree

Seinsche's theorem supplies a separated cut in the graph or its complement.
Both parts have fewer vertices, so induction gives their cotrees. In the
complement case, exchanging union and join completes the representation.
The empty graph is included rather than hidden by a nonempty hypothesis.
-/

@[expose] public section

namespace SimpleGraph

universe u

private theorem exists_cotree_of_card_le (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ n →
      G.IsP4Free → Nonempty (CotreeRepresentation G) := by
  classical
  induction n with
  | zero =>
    intro V _ G hcard hp
    let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact ⟨CotreeRepresentation.ofIsEmpty G⟩
  | succ n ih =>
    intro V _ G hcard hp
    by_cases hn : Nonempty V
    · let _ := hn
      by_cases hs : Subsingleton V
      · let _ := hs
        exact ⟨CotreeRepresentation.ofSubsingleton G⟩
      · let _ : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
        have hbuild : ∀ (H : SimpleGraph V), H.IsP4Free → ¬H.Preconnected →
            Nonempty (CotreeRepresentation H) := by
          intro H hh hd
          obtain ⟨s, hsne, hcne, hcross⟩ := exists_separated_cut_of_not_preconnected hd
          obtain ⟨a, ha⟩ := hsne
          obtain ⟨b, hb⟩ := hcne
          have hleft : Fintype.card s ≤ n := by
            have : Fintype.card s < Fintype.card V :=
              Fintype.card_lt_of_injective_of_notMem (f := fun x : s => x.val) (b := b)
                Subtype.val_injective (by rintro ⟨x, hx⟩; exact hb (hx ▸ x.property))
            omega
          have hright : Fintype.card (sᶜ : Set V) ≤ n := by
            have : Fintype.card (sᶜ : Set V) < Fintype.card V :=
              Fintype.card_lt_of_injective_of_notMem
                (f := fun x : (sᶜ : Set V) => x.val) (b := a)
                Subtype.val_injective (by
                  rintro ⟨x, hx⟩
                  have hx' : x.val = a := hx
                  exact x.property (by simpa only [hx'] using ha))
            omega
          obtain ⟨L⟩ := ih s (H.induce s) hleft (hh.induce s)
          obtain ⟨R⟩ := ih (sᶜ : Set V) (H.induce sᶜ) hright (hh.induce sᶜ)
          exact ⟨CotreeRepresentation.unionInduce s hcross L R⟩
        rcases hp.not_preconnected_or_compl with hd | hd
        · exact hbuild G hp hd
        · obtain ⟨R⟩ := hbuild Gᶜ hp.compl hd
          have hR : Nonempty (CotreeRepresentation Gᶜᶜ) := ⟨R.compl⟩
          simpa only [compl_compl] using hR
    · let _ : IsEmpty V := not_nonempty_iff.mp hn
      exact ⟨CotreeRepresentation.ofIsEmpty G⟩

/-- Every finite cograph has a cotree representation. -/
theorem IsCograph.nonempty_cotreeRepresentation {V : Type*} [Finite V]
    {G : SimpleGraph V} (h : G.IsCograph) : Nonempty (CotreeRepresentation G) := by
  classical
  let _ := Fintype.ofFinite V
  exact exists_cotree_of_card_le (Fintype.card V) V G le_rfl h

/-- For finite graphs, cograph membership is exactly representability by a cotree. -/
theorem isCograph_iff_nonempty_cotreeRepresentation {V : Type*} [Finite V]
    (G : SimpleGraph V) : G.IsCograph ↔ Nonempty (CotreeRepresentation G) :=
  ⟨IsCograph.nonempty_cotreeRepresentation, fun ⟨R⟩ => R.isCograph⟩

/-- Choose a cotree for a finite cograph; no claim of a canonical cotree or an
executable recognition algorithm is made. -/
noncomputable def IsCograph.cotreeRepresentation {V : Type*} [Finite V]
    {G : SimpleGraph V} (h : G.IsCograph) : CotreeRepresentation G :=
  Classical.choice h.nonempty_cotreeRepresentation

/-- An induced restriction of a represented cograph has a cotree too.
This interface uses completeness, rather than asserting that its cotree is a
particular pruning of the original certificate. -/
noncomputable def CotreeRepresentation.induce {V : Type*}
    {G : SimpleGraph V} (R : CotreeRepresentation G) (s : Set V) :
    CotreeRepresentation (G.induce s) := by
  letI : Finite V := Finite.of_surjective R.iso R.iso.surjective
  exact (R.isCograph.induce s).cotreeRepresentation

end SimpleGraph
