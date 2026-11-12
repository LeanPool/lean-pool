/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Ordered

/-!
# Canonically padded tuples

Shared machinery for interpretations whose tags need tuples of *different*
lengths. The universe of a `DescriptiveComplexity.FOInterpretation` is `Tag × A^dim`
for a single dimension `dim`, so an element meant to carry an `m`-tuple with
`m < dim` must fix its remaining coordinates; otherwise the same intended
element would have several representatives, which for the SAT-family
reductions would mean several distinct propositional variables standing for
the same atom.

The convention here is to pad with a *minimum* of the input order: a tuple is
`DescriptiveComplexity.Canon m` when every coordinate from `m` on is a minimum. This is
the one place where the reductions of the library need their input structure
to be ordered. The file provides

* the semantic side: `DescriptiveComplexity.Canon`, `DescriptiveComplexity.Agree`,
  the padding `DescriptiveComplexity.pad` and prefix `DescriptiveComplexity.pref` operations,
  and the fact that a canonical tuple is the padding of its prefix
  (`DescriptiveComplexity.pad_pref_of_canon`, `DescriptiveComplexity.eq_pad_of_canon_agree`);
* the first-order side: formulas `DescriptiveComplexity.canonF`,
  `DescriptiveComplexity.eqTupF`, `DescriptiveComplexity.agreeF` over the ordered expansion
  `L.sum Language.order` expressing these conditions of the coordinates held
  by selected free variables, with their realization lemmas;
* the special case of a tuple read from a context through an index map
  (`DescriptiveComplexity.PadTup`, `DescriptiveComplexity.padTupF`), which is how an element
  encoding a second-order atom `R (x_{f 0}, …)` is pinned down.

Formula builders are parameterized by maps `Fin D → γ` selecting the free
variables holding each tuple, so that they can be instantiated at the variable
types of the defining formulas of an interpretation (`Fin 1 × Fin D`,
`Fin 2 × Fin D`).

Clients: the Tseitin encoding of `DescriptiveComplexity.Problems.Sat.Tseitin` and the
Horn discharge of `DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Finite conjunctions and disjunctions of formulas -/

section ListConnectives

variable {L' : Language.{0, 0}} {γ A : Type} [L'.Structure A] {v : γ → A}

/-- Finite conjunction of a list of formulas. -/
def listInf : List (L'.Formula γ) → L'.Formula γ
  | [] => ⊤
  | φ :: l => φ ⊓ listInf l

/-- Finite disjunction of a list of formulas. -/
def listSup : List (L'.Formula γ) → L'.Formula γ
  | [] => ⊥
  | φ :: l => φ ⊔ listSup l

private theorem realize_listInf (l : List (L'.Formula γ)) :
    (listInf l).Realize v ↔ ∀ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [listInf, Formula.realize_top]
  | cons φ l ih => simp [listInf, Formula.realize_inf, ih]

private theorem realize_listSup (l : List (L'.Formula γ)) :
    (listSup l).Realize v ↔ ∃ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [listSup, Formula.realize_bot]
  | cons φ l ih => simp [listSup, Formula.realize_sup, ih]

end ListConnectives

/-! ### Padded tuples -/

section Padding

variable {A : Type} {D : ℕ}

/-- A `D`-tuple is canonical at context length `m`: every coordinate from `m`
on is a minimum of the order. -/
def Canon [LE A] (m : ℕ) (u : Fin D → A) : Prop :=
  ∀ j : Fin D, m ≤ (j : ℕ) → IsBot (u j)

/-- Two `D`-tuples agree below `m`. -/
def Agree (m : ℕ) (u x : Fin D → A) : Prop :=
  ∀ j : Fin D, (j : ℕ) < m → x j = u j

/-- Pad a context tuple to a `D`-tuple with a (minimal) element. -/
def pad (a₀ : A) {m : ℕ} (w : Fin m → A) : Fin D → A :=
  fun j => if hj : (j : ℕ) < m then w ⟨j, hj⟩ else a₀

/-- The prefix of a `D`-tuple. -/
def pref {m : ℕ} (h : m ≤ D) (u : Fin D → A) : Fin m → A :=
  fun j => u (Fin.castLE h j)

private theorem pref_pad (a₀ : A) {m : ℕ} (h : m ≤ D) (w : Fin m → A) :
    pref h (pad a₀ w) = w := by
  funext j
  rw [pref, pad, dite_eq_left (show ((Fin.castLE h j : Fin D) : ℕ) < m from j.isLt)]
  exact congrArg w (Fin.ext rfl)

theorem canon_pad [LE A] {a₀ : A} (h₀ : IsBot a₀) (m : ℕ) (w : Fin m → A) :
    Canon m (pad (D := D) a₀ w) := by
  intro j hj
  rw [pad, dite_eq_right (not_lt.mpr hj)]
  exact h₀

private theorem agree_pad_pad (a₀ : A) {m : ℕ} (w : Fin m → A) (a : A) :
    Agree m (pad (D := D) a₀ (Fin.snoc w a)) (pad a₀ w) := by
  intro j hj
  rw [pad, pad, dite_eq_left hj, dite_eq_left (hj.trans (Nat.lt_succ_self m))]
  rw [show (⟨(j : ℕ), hj.trans (Nat.lt_succ_self m)⟩ : Fin (m + 1)) =
      Fin.castSucc ⟨(j : ℕ), hj⟩ from Fin.ext rfl, Fin.snoc_castSucc]

/-- A canonical tuple is the padding of its prefix. -/
theorem pad_pref_of_canon [PartialOrder A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ} (h : m ≤ D)
    {u : Fin D → A} (hc : Canon m u) : pad a₀ (pref h u) = u := by
  funext j
  rw [pad]
  split_ifs with hj
  · rw [pref]
    exact congrArg u (Fin.ext rfl)
  · exact (h₀ (u j)).antisymm (hc j (not_lt.mp hj) a₀)

/-- A tuple canonical at `m` agreeing with `u` below `m` is the padding of
`u`'s prefix. -/
theorem eq_pad_of_canon_agree [PartialOrder A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ}
    (h : m ≤ D) {u x : Fin D → A} (hcx : Canon m x) (ha : Agree m u x) :
    x = pad a₀ (pref h u) := by
  funext j
  rw [pad]
  split_ifs with hj
  · rw [pref]
    exact (ha j hj).trans (congrArg u (Fin.ext rfl)).symm
  · exact ((h₀ (x j)).antisymm (hcx j (not_lt.mp hj) a₀)).symm

private theorem pref_pad_snoc (a₀ : A) {m : ℕ} (h : m ≤ D) (w : Fin m → A) (a : A) :
    pref h (pad a₀ (Fin.snoc w a)) = w := by
  funext j
  rw [pref, pad, dite_eq_left (show ((Fin.castLE h j : Fin D) : ℕ) < m + 1 from
    j.isLt.trans (Nat.lt_succ_self m))]
  rw [show (⟨((Fin.castLE h j : Fin D) : ℕ), _⟩ : Fin (m + 1)) = Fin.castSucc j from
    Fin.ext rfl, Fin.snoc_castSucc]

private theorem agree_pad_snoc_pref (a₀ a : A) {m : ℕ} (h : m ≤ D) (u : Fin D → A) :
    Agree m u (pad a₀ (Fin.snoc (pref h u) a)) := by
  intro j hj
  rw [pad, dite_eq_left (hj.trans (Nat.lt_succ_self m))]
  rw [show (⟨(j : ℕ), hj.trans (Nat.lt_succ_self m)⟩ : Fin (m + 1)) =
      Fin.castSucc ⟨(j : ℕ), hj⟩ from Fin.ext rfl, Fin.snoc_castSucc]
  rw [pref]
  exact congrArg u (Fin.ext rfl)

/-! #### Tuples read through an index map

An interpretation encoding second-order atoms as elements needs one element per
atom `R (x_{f 0}, …, x_{f (m-1)})`, whose coordinates are read from a context
tuple `u` through an index map `f`. Canonical padding makes that element
unique. -/

/-- `x` is the canonically padded, length-`m` tuple read from `u` through the
index map `f`. -/
def PadTup [LE A] {m : ℕ} (f : Fin m → Fin D) (u x : Fin D → A) : Prop :=
  Canon m x ∧ ∀ (j : Fin D) (hj : (j : ℕ) < m), x j = u (f ⟨j, hj⟩)

/-- The canonical padding of the tuple read through `f` does satisfy
`DescriptiveComplexity.PadTup`. -/
private theorem padTup_pad [LE A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ} (f : Fin m → Fin D)
    (u : Fin D → A) : PadTup f u (pad (D := D) a₀ fun j => u (f j)) := by
  refine ⟨canon_pad h₀ m _, fun j hj => ?_⟩
  rw [pad, dite_eq_left hj]

/-- Conversely, a tuple satisfying `DescriptiveComplexity.PadTup` *is* that canonical
padding: the element encoding an atom is unique. -/
private theorem eq_pad_of_padTup [PartialOrder A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ}
    {f : Fin m → Fin D} {u x : Fin D → A} (h : PadTup f u x) :
    x = pad a₀ fun j => u (f j) := by
  funext j
  rw [pad]
  split_ifs with hj
  · exact h.2 j hj
  · exact ((h₀ (x j)).antisymm (h.1 j (not_lt.mp hj) a₀)).symm

/-- A tuple canonical at `m + 1` agreeing below `m` with `u` is the padding
of the prefix of `u` extended by its own coordinate `m`. -/
private theorem eq_pad_snoc_of_canon_agree [PartialOrder A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ}
    (h : m < D) {u x : Fin D → A} (hcx : Canon (m + 1) x) (ha : Agree m u x) :
    x = pad a₀ (Fin.snoc (pref h.le u) (x ⟨m, h⟩)) := by
  funext j
  rw [pad]
  split_ifs with hj
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · rw [show (⟨(j : ℕ), hj⟩ : Fin (m + 1)) = Fin.castSucc ⟨(j : ℕ), hj'⟩ from
        Fin.ext rfl, Fin.snoc_castSucc]
      rw [pref]
      exact (ha j hj').trans (congrArg u (Fin.ext rfl)).symm
    · rw [show (⟨(j : ℕ), hj⟩ : Fin (m + 1)) = Fin.last m from Fin.ext hj',
        Fin.snoc_last]
      exact congrArg x (Fin.ext hj')
  · exact ((h₀ (x j)).antisymm (hcx j (not_lt.mp hj) a₀)).symm

end Padding

section Builders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

/-- `x` is a minimum of the order, as a formula. -/
noncomputable def botF (x : γ) : (L.sum Language.order).Formula γ :=
  Formula.iAlls (Fin 1)
    (Relations.formula₂ leSymb (Term.var (Sum.inl x)) (Term.var (Sum.inr 0)))

/-- The coordinates of `c` from `m` on are minima, as a formula: `c` holds a
canonically padded context tuple of length `m`. -/
noncomputable def canonF (m : ℕ) (c : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    if m ≤ (j : ℕ) then botF (c j) else ⊤)

/-- The tuples held by `u` and `x` are equal, as a formula. -/
def eqTupF (u x : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    Term.equal (Term.var (x j)) (Term.var (u j)))

/-- The tuples held by `u` and `x` agree below `m`, as a formula. -/
def agreeF (m : ℕ) (u x : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    if (j : ℕ) < m then Term.equal (Term.var (x j)) (Term.var (u j)) else ⊤)

/-- The tuple held by `x` is the canonically padded, length-`m` tuple read
from `u` through the index map `f`, as a formula. -/
noncomputable def padTupF {m : ℕ} (f : Fin m → Fin D) (u x : Fin D → γ) :
    (L.sum Language.order).Formula γ :=
  canonF m x ⊓
    listInf ((List.finRange D).map fun (j : Fin D) =>
      if hj : (j : ℕ) < m then Term.equal (Term.var (x j)) (Term.var (u (f ⟨j, hj⟩)))
      else ⊤)

end Builders

/-! ### Realization of the builders -/

section RealizeBuilders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_botF {x : γ} : (botF (L := L) x).Realize v ↔ IsBot (v x) := by
  rw [botF]
  simp only [Formula.realize_iAlls, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, relMap_leSymb]
  exact ⟨fun h b => h fun _ => b, fun h i => h (i 0)⟩

@[simp]
theorem realize_canonF {m : ℕ} {c : Fin D → γ} :
    (canonF (L := L) m c).Realize v ↔ Canon m fun j => v (c j) := by
  rw [canonF, realize_listInf]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [ite_eq_left hj] at this
    exact realize_botF.mp this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · exact realize_botF.mpr (h j hj)
    · exact Formula.realize_top.mpr trivial

@[simp]
theorem realize_eqTupF {u x : Fin D → γ} :
    (eqTupF (L := L) u x).Realize v ↔ (fun j => v (x j)) = fun j => v (u j) := by
  rw [eqTupF, realize_listInf, funext_iff]
  constructor
  · intro h j
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact h j

@[simp]
theorem realize_agreeF {m : ℕ} {u x : Fin D → γ} :
    (agreeF (L := L) m u x).Realize v ↔
      Agree m (fun j => v (u j)) fun j => v (x j) := by
  rw [agreeF, realize_listInf]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [ite_eq_left hj] at this
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact h j hj
    · exact Formula.realize_top.mpr trivial

@[simp]
theorem realize_padTupF {m : ℕ} {f : Fin m → Fin D} {u x : Fin D → γ} :
    (padTupF (L := L) f u x).Realize v ↔
      PadTup f (fun j => v (u j)) fun j => v (x j) := by
  rw [padTupF, Formula.realize_inf, realize_canonF, realize_listInf, PadTup]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h ψ hψ => ?_⟩
  · have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [dite_eq_left hj] at this
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact h j hj
    · exact Formula.realize_top.mpr trivial

end RealizeBuilders

end DescriptiveComplexity
