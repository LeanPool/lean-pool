/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Lines and subspaces

Constructions on Mathlib's `Combinatorics.Line` and `Combinatorics.Subspace` used in Shelah's proof
of the Hales--Jewett theorem.

## Main definitions

* `Combinatorics.Line.reindex`: change the index type of a line.
* `Combinatorics.Subspace.prodLine`: the subspace spanned by a subspace and a line on disjoint sets
  of coordinates.
* `Combinatorics.Subspace.compLine`: a line of the parameter cube of a subspace, as a line of the
  ambient cube.

## Main results

* `Combinatorics.Line.exists_map_eq_of_card_le`: in a cube of dimension `N` colored with at most
  `N` colors, some line has the same color at two given letters.
-/

@[expose] public section

namespace Combinatorics

variable {η α ι ι' κ : Type*}

namespace Line

/-- Change the index type of a line. -/
def reindex (l : Line α ι) (e : ι ≃ ι') : Line α ι' where
  idxFun := l.idxFun ∘ e.symm
  proper := let ⟨i, hi⟩ := l.proper; ⟨e i, by simp [hi]⟩

@[simp]
lemma reindex_apply (l : Line α ι) (e : ι ≃ ι') (x : α) : l.reindex e x = l x ∘ e.symm := rfl

/-- If a cube of dimension `N` is colored with at most `N` colors, then for any two letters `a` and
`b` some line has the same color at `a` and at `b`.

The `N + 1` words that are `a` on an initial segment of the coordinates and `b` afterwards cannot
have distinct colors. Two of them with the same color are the points at `a` and at `b` of the line
whose wildcards are the coordinates on which they differ. -/
theorem exists_map_eq_of_card_le [Finite κ] {N : ℕ} (hN : Nat.card κ ≤ N) (a b : α)
    (C : (Fin N → α) → κ) : ∃ l : Line α (Fin N), C (l a) = C (l b) := by
  cases nonempty_fintype κ
  let u (j : Fin (N + 1)) (p : Fin N) : α := if (p : ℕ) < j then a else b
  obtain ⟨j, j', hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun j ↦ C (u j))
    (by simpa [Nat.card_eq_fintype_card] using Nat.lt_succ_of_le hN)
  wlog hlt : (j : ℕ) < j' generalizing j j'
  · exact this j' j hne.symm h.symm (by grind)
  let l : Line α (Fin N) :=
    ⟨fun p ↦ if (p : ℕ) < j then some a else if (p : ℕ) < j' then none else some b,
      ⟨⟨j, by grind⟩, by simp [hlt]⟩⟩
  refine ⟨l, ?_⟩
  convert h.symm using 2 <;> ext p <;> grind [coe_apply]

end Line

namespace Subspace

/-- A subspace of `ι → α` and a line of `ι' → α` span a subspace of `ι ⊕ ι' → α` with one more
dimension, `none`, along the line. -/
def prodLine (V : Subspace η α ι) (l : Line α ι') : Subspace (Option η) α (ι ⊕ ι') where
  idxFun := Sum.elim (fun i ↦ (V.idxFun i).map id some) fun i ↦ (l.idxFun i).elim (.inr none) .inl
  proper
    | none => let ⟨i, hi⟩ := l.proper; ⟨.inr i, by simp [hi]⟩
    | some e => let ⟨i, hi⟩ := V.proper e; ⟨.inl i, by simp [hi]⟩

@[simp]
lemma prodLine_apply (V : Subspace η α ι) (l : Line α ι') (x : Option η → α) :
    V.prodLine l x = Sum.elim (V (x ∘ some)) (l (x none)) := by
  funext i
  cases i with
  | inl i => cases h : V.idxFun i <;> simp [prodLine, coe_apply, h]
  | inr i => cases h : l.idxFun i <;> simp [prodLine, coe_apply, h]

/-- A line of the parameter cube of a subspace, as a line of the ambient cube. -/
def compLine (V : Subspace η α ι) (l : Line α η) : Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := let ⟨e, he⟩ := l.proper; let ⟨i, hi⟩ := V.proper e; ⟨i, by simp [hi, he]⟩

@[simp]
lemma compLine_apply (V : Subspace η α ι) (l : Line α η) (x : α) : V.compLine l x = V (l x) := by
  funext i
  cases h : V.idxFun i <;> simp [compLine, coe_apply, h]

end Subspace

end Combinatorics
