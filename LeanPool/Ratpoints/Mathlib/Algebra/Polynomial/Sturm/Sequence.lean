/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence

import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Sturm sequences of positive multiples and generalized Sturm sequences

Candidates for `Mathlib.Algebra.Polynomial.Sturm.Sequence`: the Sturm sequence commutes with a map
of fields (`Polynomial.sturmSeq_map`); over an ordered field, the Sturm sequences of positive
multiples are entrywise positive multiples (`Polynomial.forall₂_posAssoc_sturmSeq`), and a list of
nonzero polynomials, each from the third on a positive multiple of the negated remainder of the
two before and the last a unit, is entrywise a list of positive multiples of the entries of the
Sturm sequence of its first two (`Polynomial.forall₂_posAssoc_sturmSeq_of_getElem`): a generalized
Sturm sequence, such as the remainder chain that integer arithmetic computes.

## Main definitions

* `Polynomial.PosAssoc`: one polynomial a positive constant times another.

## Main statements

* `Polynomial.sturmSeq_map`: the Sturm sequence of the images under a map of fields.
* `Polynomial.forall₂_posAssoc_sturmSeq`: the Sturm sequences of positive multiples.
* `Polynomial.forall₂_posAssoc_sturmSeq_of_getElem`: a generalized Sturm sequence.
-/

@[expose] public section

namespace Polynomial

section Map

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

/-- The Sturm sequence commutes with a map of fields. -/
theorem sturmSeq_map (φ : K →+* L) (p q : K[X]) :
    sturmSeq (p.map φ) (q.map φ) = (sturmSeq p q).map (map φ) := by
  induction p, q using sturmSeq.induct with
  | case1 q => simp
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp, sturmSeq_cons ((Polynomial.map_ne_zero_iff φ.injective).mpr hp),
      List.map_cons, ← ih, map_mod, Polynomial.map_neg]

end Map

section Ordered

variable {K : Type*} [Field K] [LinearOrder K]

/-- `q` is a positive constant times `p`. -/
def PosAssoc (p q : K[X]) : Prop :=
  ∃ c : K, 0 < c ∧ C c * p = q

theorem PosAssoc.eq_zero_iff {p q : K[X]} (h : PosAssoc p q) : p = 0 ↔ q = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc.ne']

theorem PosAssoc.natDegree_eq {p q : K[X]} (h : PosAssoc p q) : q.natDegree = p.natDegree := by
  obtain ⟨c, hc, rfl⟩ := h
  exact natDegree_C_mul hc.ne'

theorem PosAssoc.neg_mod {p p' q q' : K[X]} (hp : PosAssoc p p') (hq : PosAssoc q q') :
    PosAssoc (-p % q) (-p' % q') := by
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨c', hc', rfl⟩ := hq
  exact ⟨c, hc, by rw [mod_C_mul hc'.ne', ← mul_neg, C_mul_mod]⟩

/-- The Sturm sequences of positive multiples are entrywise positive multiples, of the same
length. -/
theorem forall₂_posAssoc_sturmSeq [DecidableEq K] {p p' q q' : K[X]} (hp : PosAssoc p p')
    (hq : PosAssoc q q') :
    List.Forall₂ PosAssoc (sturmSeq p q) (sturmSeq p' q') := by
  induction p, q using sturmSeq.induct generalizing p' q' with
  | case1 q => simp [(hp.eq_zero_iff.mp rfl)]
  | case2 p q hp0 ih =>
    rw [sturmSeq_cons hp0, sturmSeq_cons fun h ↦ hp0 (hp.eq_zero_iff.mpr h)]
    exact .cons hp (ih hq (hp.neg_mod hq))

variable [IsStrictOrderedRing K]

theorem PosAssoc.refl (p : K[X]) : PosAssoc p p :=
  ⟨1, one_pos, by simp⟩

theorem PosAssoc.symm {p q : K[X]} (h : PosAssoc p q) : PosAssoc q p := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c⁻¹, inv_pos.mpr hc, by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc.ne', C_1, one_mul]⟩

theorem PosAssoc.trans {p q r : K[X]} (h : PosAssoc p q) (h' : PosAssoc q r) : PosAssoc p r := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨c' * c, mul_pos hc' hc, by rw [C_mul, mul_assoc]⟩

/-- Two lists of positive multiples of the entries of a third are entrywise positive multiples of
each other. -/
theorem forall₂_posAssoc_of_forall₂_of_forall₂ {l₁ l₂ l₃ : List K[X]}
    (h₁ : List.Forall₂ PosAssoc l₁ l₃) (h₂ : List.Forall₂ PosAssoc l₂ l₃) :
    List.Forall₂ PosAssoc l₁ l₂ := by
  induction h₁ generalizing l₂ with
  | nil => cases h₂; exact .nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hcb h₂ => exact .cons (hab.trans hcb.symm) (ih h₂)

variable [DecidableEq K]

/-- A list `[a, b]` of nonzero polynomials with `b` a unit is, entrywise, the Sturm sequence of
`a` and `b`. -/
theorem forall₂_posAssoc_sturmSeq_pair {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hu : IsUnit b) :
    List.Forall₂ PosAssoc [a, b] (sturmSeq a b) := by
  rw [sturmSeq_cons ha, EuclideanDomain.mod_eq_zero.mpr hu.dvd, sturmSeq_zero_right,
    ite_eq_right hb]
  exact .cons (.refl a) (.cons (.refl b) .nil)

/-- A list `b :: l` of positive multiples of the entries of the Sturm sequence of `b` and a positive
multiple of `-a % b`, preceded by `a ≠ 0`, is entrywise the Sturm sequence of `a` and `b`. -/
theorem forall₂_posAssoc_sturmSeq_cons {a b c : K[X]} {l : List K[X]} (ha : a ≠ 0)
    (hc : PosAssoc (-a % b) c) (h : List.Forall₂ PosAssoc (b :: l) (sturmSeq b c)) :
    List.Forall₂ PosAssoc (a :: b :: l) (sturmSeq a b) := by
  rw [sturmSeq_cons ha]
  exact .cons (.refl a) (forall₂_posAssoc_of_forall₂_of_forall₂ h
    (forall₂_posAssoc_sturmSeq (.refl b) hc))

/-- A list `s₀, s₁, …, s_m` of nonzero polynomials whose last entry is a unit and in which each
`s_(k+2)` is a positive multiple of `-s_k % s_(k+1)` is, entrywise, a list of positive multiples of
the entries of `sturmSeq s₀ s₁`: a generalized (scaled) Sturm sequence. -/
theorem forall₂_posAssoc_sturmSeq_of_getElem {L : List K[X]} (hlen : 2 ≤ L.length)
    (h0 : ∀ p ∈ L, p ≠ 0)
    (hrem : ∀ k (hk : k + 2 < L.length), PosAssoc (-L[k] % L[k + 1]) L[k + 2])
    (hu : IsUnit (L.getLast (List.ne_nil_of_length_pos (by lia)))) :
    List.Forall₂ PosAssoc L (sturmSeq (L[0]'(by lia)) (L[1]'(by lia))) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, L = a :: b :: rest := by
    match L, hlen with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  induction rest generalizing a b with
  | nil =>
    exact forall₂_posAssoc_sturmSeq_pair (h0 a (by simp)) (h0 b (by simp)) (by simpa using hu)
  | cons e rest ih =>
    exact forall₂_posAssoc_sturmSeq_cons (h0 a (by simp)) (hrem 0 (by simp))
      (ih b e (by simp) (fun p hp ↦ h0 p (by simp_all))
        (fun k hk ↦ hrem (k + 1) (by simpa using hk)) (by simpa using hu))

end Ordered

end Polynomial

end
