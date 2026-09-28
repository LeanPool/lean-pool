/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the edges of the **placement hypergraph**

The ground set of the box-allocation nibble (`Nibble.BoxAllocationSpec`) is

* one *slot* `(S, T, i, j)` for every ordered cluster pair `(S, T)` and every pair `(i, j)` of cells
  — only the slots with `idx S < idx T` are ever used, `idx` being a fixed injective indexing of the
  clusters, so that each *unordered* cluster pair is represented once and only once;
* one *token* per copy, which forces a matching to use at most one placement of each copy.

The edge of the placement `A` of the copy `c` is its token together with the three rectangles
`A a × A (a+1)` it occupies in the three cluster pairs of `c`, each written in the orientation
prescribed by `idx`.  This file establishes the four structural facts the nibble needs: which slots
and tokens an edge contains, how many vertices it has, and that a placement is recoverable from its
edge.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxPlacementCount

/-! # BoxPlacementEdge -/

open Finset

@[expose] public section

namespace Nibble.AX1

/-- A cell-pair slot of an ordered cluster pair. -/
abbrev Slot (ι : Type) (P : ℕ) := ι × ι × Fin P × Fin P

/-- The ground set of the placement hypergraph: the cell-pair slots and the copy tokens. -/
abbrev PlaceVtx (ι κ : Type) (P : ℕ) := Slot ι P ⊕ κ

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {P : ℕ}

/-- The slot of the cell pair `(i, j)` of the cluster pair `(S, T)`, written in the orientation
prescribed by `idx`. -/
def orient (idx : ι → ℕ) (S T : ι) (i j : Fin P) : Slot ι P :=
  if idx S < idx T then (S, T, i, j) else (T, S, j, i)

/-- The rectangle that the placement `A` of the copy `c` occupies in the cluster pair
`(cl c a, cl c (a+1))`. -/
def rect (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (c : κ) (A : ZMod 3 → Finset (Fin P)) (a : ZMod 3) :
    Finset (PlaceVtx ι κ P) :=
  ((A a) ×ˢ (A (a + 1))).image (fun p => Sum.inl (orient idx (cl c a) (cl c (a + 1)) p.1 p.2))

/-- The edge of the placement `A` of the copy `c`: its token and its three rectangles. -/
def placeEdge (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (c : κ) (A : ZMod 3 → Finset (Fin P)) :
    Finset (PlaceVtx ι κ P) :=
  insert (Sum.inr c) ((Finset.univ : Finset (ZMod 3)).biUnion (rect idx cl c A))

variable {idx : ι → ℕ} {cl : κ → ZMod 3 → ι} {c : κ} {A : ZMod 3 → Finset (Fin P)}
/-- In `ZMod 3` two distinct positions are consecutive one way or the other. -/
theorem zmod3_consec {p q : ZMod 3} (hpq : p ≠ q) : q = p + 1 ∨ p = q + 1 := by
  revert hpq; revert p q; decide

/-- Two distinct positions of a copy give two distinct cluster pairs. -/
theorem zmod3_pair_ne {a b : ZMod 3} (hab : a ≠ b) :
    ¬ ((a = b ∧ a + 1 = b + 1) ∨ (a = b + 1 ∧ a + 1 = b)) := by
  revert hab; revert a b; decide

omit [DecidableEq ι] in
/-- The orientation is symmetric on distinct clusters. -/
theorem orient_symm {S T : ι} (h : idx S ≠ idx T) (i j : Fin P) :
    orient idx T S j i = orient idx S T i j := by
  rw [orient, orient]
  rcases lt_trichotomy (idx S) (idx T) with hlt | heq | hgt
  · rw [ite_eq_left hlt, ite_eq_right (by omega)]
  · exact absurd heq h
  · rw [ite_eq_left hgt, ite_eq_right (by omega)]

omit [DecidableEq ι] in
theorem orient_inj (S T : ι) :
    Function.Injective (fun p : Fin P × Fin P => orient idx S T p.1 p.2) := by
  intro p p' h
  simp only [orient] at h
  by_cases hst : idx S < idx T
  · rw [ite_eq_left hst, ite_eq_left hst] at h
    simpa [Prod.ext_iff] using h
  · rw [ite_eq_right hst, ite_eq_right hst] at h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2.2 h.2.2.1

theorem mem_rect {a : ZMod 3} {x : Slot ι P} :
    (Sum.inl x : PlaceVtx ι κ P) ∈ rect idx cl c A a ↔
      ∃ i ∈ A a, ∃ j ∈ A (a + 1), orient idx (cl c a) (cl c (a + 1)) i j = x := by
  simp only [rect, Finset.mem_image, Finset.mem_product, Sum.inl.injEq]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hx⟩
    exact ⟨i, hi, j, hj, hx⟩
  · rintro ⟨i, hi, j, hj, hx⟩
    exact ⟨(i, j), ⟨hi, hj⟩, hx⟩

theorem inr_notMem_rect {a : ZMod 3} {c' : κ} :
    (Sum.inr c' : PlaceVtx ι κ P) ∉ rect idx cl c A a := by
  simp [rect]

/-- An edge contains exactly one token, that of its copy. -/
theorem mem_placeEdge_inr (c' : κ) :
    (Sum.inr c' : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔ c' = c := by
  rw [placeEdge, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Sum.inr_injective h
    · rw [Finset.mem_biUnion] at h
      obtain ⟨a, -, ha⟩ := h
      exact absurd ha inr_notMem_rect
  · rintro rfl; exact Or.inl rfl

/-- The tokens of an edge: exactly the token of its copy. -/
theorem placeEdge_toRight : (placeEdge idx cl c A).toRight = {c} := by
  ext c'
  rw [Finset.mem_toRight, mem_placeEdge_inr, Finset.mem_singleton]

/-- **Occupying a slot.**  The placement `A` of `c` occupies the slot of the cell pair `(i, j)` in
the cluster pair `(cl c p, cl c q)` whenever `i ∈ A p` and `j ∈ A q`. -/
theorem mem_placeEdge_orient (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {p q : ZMod 3} (hpq : p ≠ q) {i j : Fin P} (hi : i ∈ A p) (hj : j ∈ A q) :
    (Sum.inl (orient idx (cl c p) (cl c q) i j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A := by
  have hne : idx (cl c p) ≠ idx (cl c q) := fun h => hpq (hcl (hidx h))
  rw [placeEdge, Finset.mem_insert, Finset.mem_biUnion]
  refine Or.inr ?_
  rcases zmod3_consec hpq with rfl | rfl
  · exact ⟨p, Finset.mem_univ _, mem_rect.mpr ⟨i, hi, j, hj, rfl⟩⟩
  · exact ⟨q, Finset.mem_univ _, mem_rect.mpr ⟨j, hj, i, hi, orient_symm hne i j⟩⟩

/-- **The slots of an edge.**  The placement `A` of `c` occupies the slot `(S, T, i, j)` exactly
when `S` and `T` are two clusters of `c`, in the orientation prescribed by `idx`, and `i`, `j` are
cells of the corresponding two sets of `A`. -/
theorem mem_placeEdge_inl (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (S T : ι) (i j : Fin P) :
    (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔
      ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T ∧ i ∈ A p ∧ j ∈ A q := by
  constructor
  · intro hmem
    rw [placeEdge, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · exact absurd h (by simp)
    rw [Finset.mem_biUnion] at h
    obtain ⟨a, -, ha⟩ := h
    obtain ⟨i₀, hi₀, j₀, hj₀, hx⟩ := mem_rect.mp ha
    have hsucc : a ≠ a + 1 := BoxCount.succ_ne_self a
    have hane : cl c a ≠ cl c (a + 1) := fun h => hsucc (hcl h)
    have hidxne : idx (cl c a) ≠ idx (cl c (a + 1)) := fun h => hane (hidx h)
    rw [orient] at hx
    by_cases hlt : idx (cl c a) < idx (cl c (a + 1))
    · rw [ite_eq_left hlt] at hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1; subst h2; subst h3; subst h4
      exact ⟨a, a + 1, hsucc, rfl, rfl, hlt, hi₀, hj₀⟩
    · rw [ite_eq_right hlt] at hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1; subst h2; subst h3; subst h4
      exact ⟨a + 1, a, hsucc.symm, rfl, rfl, by omega, hj₀, hi₀⟩
  · rintro ⟨p, q, hpq, rfl, rfl, hlt, hi, hj⟩
    have := mem_placeEdge_orient (A := A) hidx hcl hpq hi hj
    rwa [orient, ite_eq_left hlt] at this

/-- **A cell pair of an edge.** -/
theorem mem_placeEdge_iff (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {p q : ZMod 3} (hpq : p ≠ q) (i j : Fin P) :
    (Sum.inl (orient idx (cl c p) (cl c q) i j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔
      i ∈ A p ∧ j ∈ A q := by
  constructor
  · intro hmem
    rw [orient] at hmem
    by_cases hlt : idx (cl c p) < idx (cl c q)
    · rw [ite_eq_left hlt] at hmem
      obtain ⟨p', q', -, h1, h2, -, hi, hj⟩ := (mem_placeEdge_inl hidx hcl _ _ _ _).mp hmem
      have hp' : p' = p := hcl h1
      have hq' : q' = q := hcl h2
      subst hp'; subst hq'
      exact ⟨hi, hj⟩
    · rw [ite_eq_right hlt] at hmem
      obtain ⟨p', q', -, h1, h2, -, hi, hj⟩ := (mem_placeEdge_inl hidx hcl _ _ _ _).mp hmem
      have hp' : p' = q := hcl h1
      have hq' : q' = p := hcl h2
      subst hp'; subst hq'
      exact ⟨hj, hi⟩
  · rintro ⟨hi, hj⟩
    exact mem_placeEdge_orient hidx hcl hpq hi hj

theorem card_rect (a : ZMod 3) : #(rect idx cl c A a) = #(A a) * #(A (a + 1)) := by
  have hinj : Function.Injective (fun p : Fin P × Fin P =>
      (Sum.inl (orient idx (cl c a) (cl c (a + 1)) p.1 p.2) : PlaceVtx ι κ P)) :=
    fun p p' h => orient_inj (idx := idx) _ _ (Sum.inl_injective h)
  rw [rect, Finset.card_image_of_injective _ hinj, Finset.card_product]

theorem rect_disjoint (hcl : Function.Injective (cl c)) {a b : ZMod 3} (hab : a ≠ b) :
    Disjoint (rect idx cl c A a) (rect idx cl c A b) := by
  rw [Finset.disjoint_left]
  rintro x ha hb
  rcases x with x | c'
  swap
  · exact inr_notMem_rect ha
  obtain ⟨i₁, -, j₁, -, hx₁⟩ := mem_rect.mp ha
  obtain ⟨i₂, -, j₂, -, hx₂⟩ := mem_rect.mp hb
  have hkey : (cl c a = cl c b ∧ cl c (a + 1) = cl c (b + 1)) ∨
      (cl c a = cl c (b + 1) ∧ cl c (a + 1) = cl c b) := by
    rw [orient] at hx₁ hx₂
    split_ifs at hx₁ hx₂ <;> subst hx₁ <;> simp only [Prod.mk.injEq] at hx₂ <;>
      first
        | exact Or.inl ⟨hx₂.1.symm, hx₂.2.1.symm⟩
        | exact Or.inr ⟨hx₂.1.symm, hx₂.2.1.symm⟩
        | exact Or.inl ⟨hx₂.2.1.symm, hx₂.1.symm⟩
        | exact Or.inr ⟨hx₂.2.1.symm, hx₂.1.symm⟩
  refine zmod3_pair_ne hab ?_
  rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hcl h1, hcl h2⟩
  · exact Or.inr ⟨hcl h1, hcl h2⟩

/-- **The size of an edge**: the token plus the three rectangles. -/
theorem placeEdge_card (hcl : Function.Injective (cl c)) :
    #(placeEdge idx cl c A) = 1 + ∑ a : ZMod 3, #(A a) * #(A (a + 1)) := by
  rw [placeEdge, Finset.card_insert_of_notMem (by
    rw [Finset.mem_biUnion]
    rintro ⟨a, -, ha⟩
    exact inr_notMem_rect ha)]
  rw [Finset.card_biUnion (fun a _ b _ hab => rect_disjoint hcl hab)]
  simp only [card_rect]
  omega

/-- **A placement is recoverable from its edge.** -/
theorem placeEdge_inj (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {c' : κ} {A' : ZMod 3 → Finset (Fin P)} (hcl' : Function.Injective (cl c'))
    (hA : ∀ a, (A a).Nonempty) (hA' : ∀ a, (A' a).Nonempty)
    (h : placeEdge idx cl c A = placeEdge idx cl c' A') : c = c' ∧ A = A' := by
  have hcc : c = c' := by
    have hmem : (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A' := by
      rw [← h, mem_placeEdge_inr]
    exact (mem_placeEdge_inr (A := A') (idx := idx) c).mp hmem
  subst hcc
  refine ⟨rfl, ?_⟩
  funext a
  ext i
  obtain ⟨j, hj⟩ := hA (a + 1)
  obtain ⟨j', hj'⟩ := hA' (a + 1)
  have hane : a ≠ a + 1 := BoxCount.succ_ne_self a
  constructor
  · intro hi
    have h1 : (Sum.inl (orient idx (cl c a) (cl c (a + 1)) i j) : PlaceVtx ι κ P)
        ∈ placeEdge idx cl c A := mem_placeEdge_orient hidx hcl hane hi hj
    rw [h] at h1
    exact ((mem_placeEdge_iff hidx hcl' hane i j).mp h1).1
  · intro hi
    have h1 : (Sum.inl (orient idx (cl c a) (cl c (a + 1)) i j') : PlaceVtx ι κ P)
        ∈ placeEdge idx cl c A' := mem_placeEdge_orient hidx hcl' hane hi hj'
    rw [← h] at h1
    exact ((mem_placeEdge_iff hidx hcl hane i j').mp h1).1

end Nibble.AX1
