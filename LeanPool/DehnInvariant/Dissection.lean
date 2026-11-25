/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Isometry
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026): the bridge layer of Dehn's theorem.

Study 1 defined the Dehn invariant on a list of edges and proved the arithmetic (rational angles
give 0,
arccos(1/3) is not a rational multiple of π).  This study proves the geometry that study 1 took as
given:
cutting a convex polytope into convex polytopes and moving the pieces rigidly does not change the
Dehn
invariant.

* `dehnSet P` (file Dehn2Local): the Dehn invariant of a set in 3-space, defined from the set alone.
* `dehnSet_cut` (Dehn2Cut): additive under a cut by a plane.
* `dehnSet_image` (Dehn2Motion): unchanged by rigid motions.
* `dissection_additive` (Dehn2Poly): the refinement argument.
* here: `dehnSet_dissection`, `dehnSet_eq_of_scissorsCongruent` (Dehn 1901), and for polyhedra
  that need
  not be convex `dehnSum_eq_of_same_union`, `dehnSum_eq_of_scissors`.

Credits: Dehn (1901); Jessen's tensor form of the invariant. Prior Lean work: FormalBook ch. 10
(PR #157, merged 6 Oct 2026) proves Hilbert's third problem in an abstract segment-and-angle model
and
states that it does not bridge geometric decompositions to that model; nothing is borrowed from it
here.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fact (finrank ℝ E = 3)]

/-- **The Dehn invariant is additive over dissections.** If a convex polytope `P` in 3-space is
the union of
finitely many convex polytopes `p k` with pairwise disjoint interiors, then
`dehnSet P = Σ k, dehnSet (p k)`. -/
theorem dehnSet_dissection {κ : Type} [Fintype κ] {P : Set E} {p : κ → Set E} (hP : IsPoly P)
    (hp : ∀ k, IsPoly (p k)) (hU : (⋃ k, p k) = P)
    (hdisj : Pairwise fun i j => Disjoint (interior (p i)) (interior (p j))) :
    dehnSet P = ∑ k, dehnSet (p k) := by
  have h3 : finrank ℝ E = 3 := Fact.out
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  exact dissection_additive dehnSet (fun Q hQ c d hc => dehnSet_cut hQ c d hc) hP hp hU hdisj

/-- `P` and `Q` are scissors congruent (equidecomposable) with convex pieces: `P` is cut into
finitely many
convex polytopes `p k` with pairwise disjoint interiors, each piece is moved by an isometry `g k`
of the
space, and the moved pieces fill `Q`, again with pairwise disjoint interiors. -/
def ScissorsCongruent (P Q : Set E) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (p : κ → Set E) (g : κ → E ≃ᵃⁱ[ℝ] E),
    (∀ k, IsPoly (p k)) ∧ (⋃ k, p k) = P ∧
    (Pairwise fun i j => Disjoint (interior (p i)) (interior (p j))) ∧
    (⋃ k, g k '' p k) = Q ∧
    (Pairwise fun i j => Disjoint (interior (g i '' p i)) (interior (g j '' p j)))

/-- **Dehn's theorem, the bridge.** Scissors-congruent convex polytopes in 3-space have the same
Dehn
invariant. -/
theorem dehnSet_eq_of_scissorsCongruent {P Q : Set E} (hP : IsPoly P) (hQ : IsPoly Q)
    (h : ScissorsCongruent P Q) : dehnSet P = dehnSet Q := by
  obtain ⟨κ, _, p, g, hp, hUP, hdP, hUQ, hdQ⟩ := h
  rw [dehnSet_dissection hP hp hUP hdP,
    dehnSet_dissection hQ (fun k => (hp k).image (g k)) hUQ hdQ]
  exact Finset.sum_congr rfl fun k _ => (dehnSet_image (g k) (p k)).symm

/-- Contrapositive: convex polytopes with different Dehn invariants are not scissors congruent. -/
theorem not_scissorsCongruent_of_dehnSet_ne {P Q : Set E} (hP : IsPoly P) (hQ : IsPoly Q)
    (h : dehnSet P ≠ dehnSet Q) : ¬ ScissorsCongruent P Q :=
  fun hs => h (dehnSet_eq_of_scissorsCongruent hP hQ hs)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fact (finrank ℝ E = 3)] in
/-- The intersection of two convex polytopes is a convex polytope. -/
lemma IsPoly.inter {P Q : Set E} (hP : IsPoly P) (hQ : IsPoly Q) : IsPoly (P ∩ Q) := by
  obtain ⟨hb, ι, _, a, b, rfl⟩ := hP
  obtain ⟨-, ι', _, a', b', rfl⟩ := hQ
  refine ⟨hb.subset inter_subset_left, ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', ?_⟩
  ext x; constructor
  · rintro ⟨h1, h2⟩ (i | j)
    · exact h1 i
    · exact h2 j
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩

/-- **Polyhedra that need not be convex: the Dehn invariant does not depend on the dissection.**
Two families of convex polytopes, each with pairwise disjoint interiors, that fill the same set
have the same
total Dehn invariant. So `Σ k, dehnSet (p k)` is an invariant of the polyhedron `⋃ k, p k`. -/
theorem dehnSum_eq_of_same_union {κ κ' : Type} [Fintype κ] [Fintype κ'] {p : κ → Set E}
    {q : κ' → Set E} (hp : ∀ k, IsPoly (p k)) (hq : ∀ l, IsPoly (q l))
    (hdp : Pairwise fun i j => Disjoint (interior (p i)) (interior (p j)))
    (hdq : Pairwise fun i j => Disjoint (interior (q i)) (interior (q j)))
    (hU : (⋃ k, p k) = ⋃ l, q l) :
    ∑ k, dehnSet (p k) = ∑ l, dehnSet (q l) := by
  have h1 : ∀ k, dehnSet (p k) = ∑ l, dehnSet (p k ∩ q l) := by
    intro k
    apply dehnSet_dissection (hp k) (fun l => (hp k).inter (hq l))
    · rw [← inter_iUnion, ← hU]; exact inter_eq_left.2 (subset_iUnion p k)
    · intro i j hij
      exact (hdq hij).mono (interior_mono inter_subset_right) (interior_mono inter_subset_right)
  have h2 : ∀ l, dehnSet (q l) = ∑ k, dehnSet (p k ∩ q l) := by
    intro l
    apply dehnSet_dissection (hq l) (fun k => (hp k).inter (hq l))
    · rw [← iUnion_inter, hU]; exact inter_eq_right.2 (subset_iUnion q l)
    · intro i j hij
      exact (hdp hij).mono (interior_mono inter_subset_left) (interior_mono inter_subset_left)
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_congr rfl (fun l _ => h2 l)]
  exact Finset.sum_comm

/-- **Dehn's theorem for polyhedra that need not be convex.** Let the polyhedron `⋃ k, p k` be cut
into the
convex pieces `p k`, and let the moved pieces `g k '' p k` fill a second polyhedron. Then every
dissection
`p₁` of the first polyhedron into convex polytopes and every dissection `p₂` of the second have
the same
total Dehn invariant. -/
theorem dehnSum_eq_of_scissors {κ κ₁ κ₂ : Type} [Finite κ] [Fintype κ₁] [Fintype κ₂]
    {p : κ → Set E} {g : κ → E ≃ᵃⁱ[ℝ] E} {p₁ : κ₁ → Set E} {p₂ : κ₂ → Set E}
    (hp : ∀ k, IsPoly (p k))
    (hdp : Pairwise fun i j => Disjoint (interior (p i)) (interior (p j)))
    (hdg : Pairwise fun i j => Disjoint (interior (g i '' p i)) (interior (g j '' p j)))
    (hp₁ : ∀ k, IsPoly (p₁ k))
    (hd₁ : Pairwise fun i j => Disjoint (interior (p₁ i)) (interior (p₁ j)))
    (hU₁ : (⋃ k, p₁ k) = ⋃ k, p k)
    (hp₂ : ∀ k, IsPoly (p₂ k))
    (hd₂ : Pairwise fun i j => Disjoint (interior (p₂ i)) (interior (p₂ j)))
    (hU₂ : (⋃ k, p₂ k) = ⋃ k, g k '' p k) :
    ∑ k, dehnSet (p₁ k) = ∑ k, dehnSet (p₂ k) := by
  let := Fintype.ofFinite κ
  rw [dehnSum_eq_of_same_union hp₁ hp hd₁ hdp hU₁,
    dehnSum_eq_of_same_union hp₂ (fun k => (hp k).image (g k)) hd₂ hdg hU₂]
  exact Finset.sum_congr rfl fun k _ => (dehnSet_image (g k) (p k)).symm

end DehnCanon.Library
