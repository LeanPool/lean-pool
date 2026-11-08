/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import LeanPool.ShelahHalesJewett.Line

/-!
# Shelah's bound for the Hales--Jewett numbers

Shelah's proof of the Hales--Jewett theorem, by induction on the alphabet.

To pass from `α` to `Option α`, fix a letter `a₀` of `α`.
`Combinatorics.Subspace.exists_insensitive` gives a subspace on which the color of a word does not
change when a `none` is replaced by `some a₀`. On this subspace the coloring is determined by the
words over `α`, so a monochromatic line over `α` in its parameter cube is also monochromatic at
`none`.

The subspace is built dimension by dimension. Each dimension is a line in a block of new
coordinates, given by `Combinatorics.Line.exists_map_eq_of_card_le`, whose points at the two
letters have the same color for every choice of the other coordinates.

## Main definitions

* `Combinatorics.Subspace.insensitiveBound`: the dimension of the cube in
  `Combinatorics.Subspace.exists_insensitive`.
* `Combinatorics.Line.shelahBound`: Shelah's bound for the Hales--Jewett numbers.

## Main results

* `Combinatorics.Subspace.exists_insensitive`: in a cube of dimension `insensitiveBound`, every
  coloring is insensitive to two given letters on a subspace.
* `Combinatorics.Line.exists_mono_of_card_eq_shelahBound`: the Hales--Jewett theorem in dimension
  `shelahBound`.
* `Combinatorics.Line.exists_mono_of_shelahBound_le`: the Hales--Jewett theorem in every dimension
  at least `shelahBound`, over a nonempty alphabet.

## References

* S. Shelah, *Primitive recursive bounds for van der Waerden numbers*, J. Amer. Math. Soc. 1
  (1988), 683--697.
-/

@[expose] public section

namespace Combinatorics

namespace Subspace

/-- A dimension in which every coloring with `r` colors of the words over `k` letters is
insensitive to two given letters on an `n`-dimensional subspace. Each dimension of the subspace
takes a block of as many coordinates as there are colorings of the words on the earlier blocks. -/
def insensitiveBound (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, r => insensitiveBound k n (r ^ k) + r ^ k ^ insensitiveBound k n (r ^ k)

/-- In a cube of dimension `insensitiveBound`, every coloring is insensitive to the letters `a`
and `b` on some `η`-dimensional subspace: replacing `a` by `b` in any coordinates of a point of
the subspace does not change its color. -/
theorem exists_insensitive (α : Type) [Finite α] (a b : α) (η : Type) [Finite η]
    (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι = insensitiveBound (Nat.card α) (Nat.card η) (Nat.card κ) ∧
      ∀ C : (ι → α) → κ, ∃ V : Subspace η α ι,
        ∀ x y : η → α, (∀ e, x e = y e ∨ x e = a ∧ y e = b) → C (V x) = C (V y) := by
  induction η using Finite.induction_empty_option generalizing κ with
  | @of_equiv η η' e ih =>
    obtain ⟨ι, _, hι, h⟩ := ih κ
    refine ⟨ι, ‹_›, Nat.card_congr e ▸ hι, ?_⟩
    intro C
    obtain ⟨V, hV⟩ := h C
    refine ⟨V.reindex e (.refl α) (.refl ι), ?_⟩
    intro x y hxy
    have key (z : η' → α) : V.reindex e (.refl α) (.refl ι) z = V (z ∘ e) := by
      ext
      simp
    rw [key, key]
    apply hV
    intro e'
    exact hxy (e e')
  | h_empty =>
    refine ⟨Empty, inferInstance, by simp [insensitiveBound], ?_⟩
    intro C
    refine ⟨⟨fun i ↦ i.elim, fun e ↦ e.elim⟩, ?_⟩
    intro x y _
    rw [Subsingleton.elim x y]
  | h_option ih =>
    obtain ⟨ι, _, hι, h⟩ := ih (α → κ)
    refine ⟨ι ⊕ Fin (Nat.card ((ι → α) → κ)), inferInstance,
      by simp [insensitiveBound, Nat.card_fun, hι], ?_⟩
    intro C
    obtain ⟨l, hl⟩ := Line.exists_map_eq_of_card_le le_rfl a b
      fun (u : Fin (Nat.card ((ι → α) → κ)) → α) (w : ι → α) ↦ C (Sum.elim w u)
    obtain ⟨V, hV⟩ := h fun w x ↦ C (Sum.elim w (l x))
    refine ⟨V.prodLine l, ?_⟩
    intro x y hxy
    rw [prodLine_apply, prodLine_apply]
    apply (congrFun (hV (x ∘ some) (y ∘ some) fun e ↦ hxy (some e)) (x none)).trans
    grind [congrFun hl (V (y ∘ some))]

end Subspace

namespace Line

/-- Shelah's bound for the Hales--Jewett number of `k` letters and `r` colors: the dimension of a
cube in which every coloring is insensitive to two letters on a subspace whose dimension is the
bound for `k - 1` letters. -/
def shelahBound : ℕ → ℕ → ℕ
  | 0, r => min r 1
  | 1, _ => 1
  | k + 2, r => Subspace.insensitiveBound (k + 2) (shelahBound (k + 1) r) r

/-- The Hales--Jewett theorem with Shelah's bound, for some index type of cardinality
`shelahBound`. See `exists_mono_of_card_eq_shelahBound`. -/
private lemma exists_mono_shelahBound' (α : Type) [Finite α] (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = shelahBound (Nat.card α) (Nat.card κ) ∧
      ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C := by
  induction α using Finite.induction_empty_option generalizing κ with
  | @of_equiv α α' e ih =>
    obtain ⟨ι, _, hι, h⟩ := ih κ
    refine ⟨ι, ‹_›, Nat.card_congr e ▸ hι, ?_⟩
    intro C
    obtain ⟨l, c, hc⟩ := h fun v ↦ C (e ∘ v)
    refine ⟨l.map e, c, ?_⟩
    intro x
    rw [← e.apply_symm_apply x, map_apply]
    exact hc _
  | h_empty =>
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · refine ⟨Empty, inferInstance, by simp [shelahBound], ?_⟩
      intro C
      exact isEmptyElim (C isEmptyElim)
    · refine ⟨Unit, inferInstance, by simp [shelahBound, Nat.succ_le_iff], ?_⟩
      intro C
      exact ⟨default, Classical.arbitrary κ, isEmptyElim⟩
  | @h_option α _ ih =>
    rcases isEmpty_or_nonempty α with hα | hα
    · refine ⟨Unit, inferInstance, by simp [shelahBound], ?_⟩
      intro C
      refine ⟨diagonal _ Unit, C (diagonal _ Unit none), ?_⟩
      intro x
      rw [Subsingleton.elim x none]
    obtain ⟨ι', _, hι', h'⟩ := ih κ
    obtain ⟨ι, _, hι, h⟩ :=
      Subspace.exists_insensitive (Option α) none (some (Classical.arbitrary α)) ι' κ
    refine ⟨ι, ‹_›, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := α)).ne'
      rw [hι, Finite.card_option, hk, shelahBound, Nat.card_eq_fintype_card (α := ι'), hι', hk]
    intro C
    obtain ⟨V, hV⟩ := h C
    obtain ⟨l, c, hc⟩ := h' fun w ↦ C (V (some ∘ w))
    refine ⟨V.compLine (l.map some), c, ?_⟩
    intro x
    rw [Subspace.compLine_apply]
    have hsome (x' : α) : C (V (l.map some (some x'))) = c := by simpa using hc x'
    rcases x with _ | x
    · rw [← hsome (Classical.arbitrary α)]
      apply hV
      intro e
      cases he : l.idxFun e <;> simp [map, he]
    · exact hsome x

variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]

/-- The **Hales--Jewett theorem** with Shelah's bound: every coloring of the words over `α` indexed
by a type of cardinality `shelahBound (card α) (card κ)` has a monochromatic line. -/
theorem exists_mono_of_card_eq_shelahBound
    (h : Fintype.card ι = shelahBound (Fintype.card α) (Fintype.card κ)) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by
  obtain ⟨ι₀, _, hι₀, h₀⟩ :=
    exists_mono_shelahBound' (Fin (Fintype.card α)) (Fin (Fintype.card κ))
  rw [Nat.card_fin, Nat.card_fin, ← h] at hι₀
  let eα := Fintype.equivFin α
  let eκ := Fintype.equivFin κ
  let eι := Fintype.equivOfCardEq hι₀
  obtain ⟨l, c, hc⟩ := h₀ fun v ↦ eκ (C (eα.symm ∘ v ∘ eι.symm))
  refine ⟨(l.map eα.symm).reindex eι, eκ.symm c, ?_⟩
  intro x
  rw [reindex_apply, ← eα.symm_apply_apply x, map_apply]
  exact eκ.eq_symm_apply.2 (hc (eα x))

/-- The **Hales--Jewett theorem** with Shelah's bound: over a nonempty alphabet `α`, every coloring
of the words indexed by a type of cardinality at least `shelahBound (card α) (card κ)` has a
monochromatic line. -/
theorem exists_mono_of_shelahBound_le [Nonempty α]
    (h : shelahBound (Fintype.card α) (Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by
  let e : Fin (shelahBound (Fintype.card α) (Fintype.card κ)) ⊕
      Fin (Fintype.card ι - shelahBound (Fintype.card α) (Fintype.card κ)) ≃ ι :=
    Fintype.equivOfCardEq (by simp [Nat.add_sub_cancel' h])
  let a : α := Classical.arbitrary α
  obtain ⟨l, c, hc⟩ := exists_mono_of_card_eq_shelahBound (by simp)
    fun v : Fin (shelahBound (Fintype.card α) (Fintype.card κ)) → α ↦
      C (Sum.elim v (fun _ ↦ a) ∘ e.symm)
  refine ⟨(l.horizontal fun _ ↦ a).reindex e, c, ?_⟩
  intro x
  rw [reindex_apply, horizontal_apply]
  exact hc x

end Line

end Combinatorics
