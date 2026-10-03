/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ListEdgeColoringComplete.Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde

/-! # The extended-star polynomial of the line graph of `K_V`

Fix a labelling `f : V ≃ Fin n`. The variables are the actual edges of the complete graph
on `V` together with one artificial vertex `inr u` for every `u : V`. The extended star
clique at `u` has the `n` members `starMember f u k` (`k : Fin n`): the edge `s(u, f⁻¹ k)`
when `f⁻¹ k ≠ u`, and the artificial vertex `inr u` when `f⁻¹ k = u`.

`starPoly f u` is the (transposed) Vandermonde determinant of the star at `u`, expanded as
a sum over permutations, and `graphPoly f` is the product of all of them. A nonzero value
of `graphPoly f` forces distinct values on every star (`starPoly_eval_ne_zero`), and the
coefficient of the certificate monomial is `±1` (`coeff_graphPoly_certificate`), by the
uniqueness of the certificate (`certificate_unique`).
-/

@[expose] public section

namespace LeanPool.ListEdgeColoringComplete

open MvPolynomial Finset

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-- Variables: actual edges of the complete graph, and one artificial vertex per star. -/
abbrev StarVar (V : Type*) := (⊤ : SimpleGraph V).edgeSet ⊕ V

/-- The `k`-th member of the extended star clique at `u`. -/
def starMember (f : V ≃ Fin n) (u : V) (k : Fin n) : StarVar V :=
  if h : f.symm k = u then Sum.inr u
  else Sum.inl ⟨s(u, f.symm k), by simpa [eq_comm] using h⟩

theorem starMember_self (f : V ≃ Fin n) (u : V) : starMember f u (f u) = Sum.inr u := by
  simp [starMember]

theorem starMember_of_ne (f : V ≃ Fin n) {u w : V} (h : w ≠ u) :
    starMember f u (f w) = Sum.inl ⟨s(u, w), by simpa [eq_comm] using h⟩ := by
  simp [starMember, h]

theorem starMember_injective (f : V ≃ Fin n) (u : V) :
    Function.Injective (starMember f u) := by
  intro k k' h
  unfold starMember at h
  split_ifs at h with h1 h2 h2
  · exact f.symm.injective (h1.trans h2.symm)
  · simp only [Sum.inl.injEq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact f.symm.injective h
    · exact absurd h h1

/-- The members of the star at `u` equal to a given artificial vertex. -/
theorem starMember_eq_inr (f : V ≃ Fin n) (u w : V) (k : Fin n) :
    starMember f u k = Sum.inr w ↔ u = w ∧ k = f u := by
  unfold starMember
  split_ifs with h
  · simp only [Sum.inr.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, by rw [← h]; simp⟩
    · rintro ⟨rfl, -⟩; rfl
  · simp only [false_iff, not_and]
    rintro rfl rfl
    simp at h

/-- The members of the star at `u` equal to a given actual edge `s(a, b)`. -/
theorem starMember_eq_inl (f : V ≃ Fin n) (u a b : V) (k : Fin n)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    starMember f u k = Sum.inl ⟨s(a, b), hab⟩ ↔
      (u = a ∧ k = f b) ∨ (u = b ∧ k = f a) := by
  have hne : a ≠ b := by simpa using hab
  unfold starMember
  split_ifs with h
  · simp only [false_iff, not_or, not_and]
    constructor
    · rintro rfl rfl; exact hne (by simpa using h.symm)
    · rintro rfl rfl; exact hne (by simpa using h)
  · simp only [Sum.inl.injEq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk]
    constructor
    · rintro (⟨rfl, h2⟩ | ⟨rfl, h2⟩)
      · exact Or.inl ⟨rfl, by rw [← h2]; simp⟩
      · exact Or.inr ⟨rfl, by rw [← h2]; simp⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, by simp⟩
      · exact Or.inr ⟨rfl, by simp⟩

/-- The transposed Vandermonde determinant of the extended star at `u`, written out as a
sum over permutations: the member `k` gets exponent `π k`. -/
noncomputable def starPoly (f : V ≃ Fin n) (u : V) : MvPolynomial (StarVar V) ℚ :=
  ∑ π : Equiv.Perm (Fin n),
    C ((Equiv.Perm.sign π : ℤ) : ℚ) * ∏ k, X (starMember f u k) ^ (π k : ℕ)

/-- The product of the extended-star polynomials over all vertices. -/
noncomputable def graphPoly [Fintype V] (f : V ≃ Fin n) : MvPolynomial (StarVar V) ℚ :=
  ∏ u, starPoly f u

/-- The exponent vector of the term indexed by a family of permutations. -/
noncomputable def expo [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) : StarVar V →₀ ℕ :=
  ∑ u, ∑ k, Finsupp.single (starMember f u k) (P u k : ℕ)

/-- The sign of the term indexed by a family of permutations. -/
noncomputable def termSign [Fintype V] (P : V → Equiv.Perm (Fin n)) : ℚ :=
  ∏ u, ((Equiv.Perm.sign (P u) : ℤ) : ℚ)

theorem eval_starPoly (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ) :
    eval x (starPoly f u) =
      (Matrix.vandermonde (fun k => x (starMember f u k))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [starPoly, map_sum, map_mul, eval_C, map_prod, map_pow, eval_X]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [Matrix.vandermonde]

/-- A nonzero value of a star polynomial forces distinct values on the star. -/
theorem starPoly_eval_ne_zero (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ)
    (h : eval x (starPoly f u) ≠ 0) :
    Function.Injective (fun k => x (starMember f u k)) := by
  rw [eval_starPoly] at h
  intro k k' hk
  by_contra hne
  exact h (Matrix.det_vandermonde_eq_zero_iff.mpr ⟨k, k', hk, hne⟩)

theorem graphPoly_eq [Fintype V] (f : V ≃ Fin n) :
    graphPoly f = ∑ P : V → Equiv.Perm (Fin n), monomial (expo f P) (termSign P) := by
  unfold graphPoly starPoly
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [X_pow_eq_monomial]
  rw [Finset.prod_congr rfl fun u _ => (monomial_sum_one _ _).symm, ← monomial_sum_one,
    C_mul_monomial, mul_one]
  rfl

theorem expo_inr [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (u : V) :
    expo f P (Sum.inr u) = P u (f u) := by
  simp only [expo, Finsupp.finsetSum_apply, Finsupp.single_apply, starMember_eq_inr]
  rw [Fintype.sum_eq_single u, Fintype.sum_eq_single (f u)]
  · simp
  · intro k hk
    simp [hk]
  · intro w hw
    exact Finset.sum_eq_zero fun k _ => by simp [hw]

theorem expo_inl [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (a b : V)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    expo f P (Sum.inl ⟨s(a, b), hab⟩) = P a (f b) + P b (f a) := by
  have hne : a ≠ b := by simpa using hab
  simp only [expo, Finsupp.finsetSum_apply, Finsupp.single_apply, starMember_eq_inl]
  rw [Fintype.sum_eq_add a b hne, Fintype.sum_eq_single (f b), Fintype.sum_eq_single (f a)]
  · simp [hne, Ne.symm hne]
  · intro k hk
    simp [hk, Ne.symm hne]
  · intro k hk
    simp [hk, hne]
  · rintro w ⟨hwa, hwb⟩
    exact Finset.sum_eq_zero fun k _ => by simp [hwa, hwb]

theorem degree_expo [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) :
    (expo f P).degree = Fintype.card V * ∑ k : Fin n, (k : ℕ) := by
  simp only [expo, map_sum, Finsupp.degree_single]
  rw [Finset.sum_congr rfl fun u _ => Equiv.sum_comp (P u) (fun k : Fin n => (k : ℕ))]
  simp

/-- The canonical family of permutations: the rank rows of the certificate. -/
noncomputable def canonicalPerm (f : V ≃ Fin n) (u : V) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (canonicalRow (f u))
    (Finite.injective_iff_bijective.mp (canonicalRow_injective _))

omit [DecidableEq V] in
theorem canonicalPerm_apply (f : V ≃ Fin n) (u : V) (k : Fin n) :
    canonicalPerm f u k = canonicalRow (f u) k := rfl

/-- Only the canonical family of permutations produces the certificate monomial. This is
where the uniqueness of the certificate enters. -/
theorem eq_canonicalPerm_of_expo_eq [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n))
    (h : expo f P = expo f (canonicalPerm f)) : P = canonicalPerm f := by
  have hr := certificate_unique (n := n) (fun i j => P (f.symm i) j)
    (fun i => (P (f.symm i)).injective)
    (fun i => by
      have := congrArg (fun m => m (Sum.inr (f.symm i))) h
      simp only [expo_inr, canonicalPerm_apply, Equiv.apply_symm_apply] at this
      rw [this]
      exact canonicalRow_spec.2.1 i)
    (fun i j hij => by
      have hne : f.symm i ≠ f.symm j := fun h' => hij (f.symm.injective h')
      have hab : s(f.symm i, f.symm j) ∈ (⊤ : SimpleGraph V).edgeSet := by simpa using hne
      have := congrArg (fun m => m (Sum.inl ⟨_, hab⟩)) h
      simp only [expo_inl, canonicalPerm_apply, Equiv.apply_symm_apply] at this
      rw [this]
      exact canonicalRow_spec.2.2 i j hij)
  funext u
  ext k
  have := congrFun (congrFun hr (f u)) k
  simpa [canonicalPerm_apply] using congrArg Fin.val this

omit [DecidableEq V] in
theorem termSign_ne_zero [Fintype V] (P : V → Equiv.Perm (Fin n)) : termSign P ≠ 0 := by
  unfold termSign
  rw [Finset.prod_ne_zero_iff]
  intro u _
  rcases Int.units_eq_one_or (Equiv.Perm.sign (P u)) with h | h <;> simp [h]

/-- **The certificate coefficient is `±1`.** -/
theorem coeff_graphPoly_certificate [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) = termSign (canonicalPerm f) := by
  rw [graphPoly_eq, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (canonicalPerm f)]
  · simp
  · intro P _ hP
    exact ite_eq_right_iff.mpr fun h => absurd (eq_canonicalPerm_of_expo_eq f P h) hP
  · simp

theorem coeff_graphPoly_certificate_ne_zero [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) ≠ 0 := by
  rw [coeff_graphPoly_certificate]
  exact termSign_ne_zero _

/-- The total degree of the polynomial equals the degree of the certificate monomial. -/
theorem totalDegree_graphPoly [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).totalDegree = (expo f (canonicalPerm f)).degree := by
  apply le_antisymm
  · rw [graphPoly_eq]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun P _ => ?_)
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    change (expo f P).degree = _
    rw [degree_expo, degree_expo]
  · have hm : expo f (canonicalPerm f) ∈ (graphPoly f).support :=
      mem_support_iff.mpr (coeff_graphPoly_certificate_ne_zero f)
    exact le_totalDegree hm

end LeanPool.ListEdgeColoringComplete
