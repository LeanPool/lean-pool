/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.DomainOperatorClosedRangeAdjoint

/-!
# Maximal adjoint realizations from one resolvent pair

A formal integration-by-parts identity only proves inclusion in the
Hilbert-space adjoint graph.  This file supplies the missing maximality
argument from a smaller, checkable operator-theoretic input: at one spectral
parameter the adjoint pencil is surjective and the conjugate original pencil
has dense range.

Surjectivity produces a candidate adjoint-domain representative.  Its
embedding error is orthogonal to the dense original-pencil range, hence
vanishes.  The same orthogonality argument, using completeness of the ambient
Hilbert space, derives density of the original bundled domain.  Thus no
maximal-domain or dense-domain premise is hidden in the constructor.

The last theorem,
`adjointRealization_and_closedGraph_of_formalAdjoint_reference`, extracts these
hypotheses from one forward reference resolver together with one
formal-adjoint surjectivity statement, which is the shape the numerical-range
resolvent criterion consumes.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace DomainOperator

universe u v w

open Set

variable {X : Type u} {D : Type v} {E : Type w}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {A : DomainOperator X D} {Astar : DomainOperator X E}

/-- The formal adjoint pairing, without any maximal-domain assertion. -/
def FormalAdjointPairing (A : DomainOperator X D)
    (Astar : DomainOperator X E) : Prop :=
  ∀ d : D, ∀ e : E,
    inner ℂ (A.op d) (Astar.embedding e) =
      inner ℂ (A.embedding d) (Astar.op e)

namespace FormalAdjointPairing

/-- The formal pairing intertwines conjugate pencils at the level of inner
products. -/
theorem inner_pencil_embedding
    (hpair : FormalAdjointPairing A Astar) (z : ℂ) (d : D) (e : E) :
    inner ℂ (A.pencil z d) (Astar.embedding e) =
      inner ℂ (A.embedding d) (Astar.pencil (star z) e) := by
  simp only [pencil, sub_apply, smul_apply, inner_sub_left,
    inner_smul_left, inner_sub_right, inner_smul_right, starRingEnd_apply]
  rw [hpair d e]

end FormalAdjointPairing

/-- A putative adjoint graph pair gives the corresponding pencil pairing. -/
theorem inner_pencil_eq_of_graph_pairing
    {y g : X}
    (hp : ∀ d : D,
      inner ℂ (A.op d) y = inner ℂ (A.embedding d) g)
    (z : ℂ) (d : D) :
    inner ℂ (A.pencil z d) y =
      inner ℂ (A.embedding d) ((star z) • y - g) := by
  simp only [pencil, sub_apply, smul_apply, inner_sub_left,
    inner_smul_left, inner_sub_right, inner_smul_right, starRingEnd_apply]
  rw [hp d]

/-- Formal adjointness, one surjective adjoint pencil, and density of the
conjugate original pencil force density of the original bundled domain. -/
theorem denseRange_embedding_of_formalAdjointPairing_of_surjective_pencil
    [CompleteSpace X]
    (hpair : FormalAdjointPairing A Astar) {z : ℂ}
    (hsurjectiveStar : Function.Surjective (Astar.pencil (star z)))
    (hdense : DenseRange (A.pencil z)) :
    DenseRange A.embedding := by
  have horth : A.embedding.rangeᗮ = ⊥ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨e, he⟩ := hsurjectiveStar y
      have hembeddingZero : Astar.embedding e = 0 := by
        apply hdense.eq_zero_of_inner_right ℂ
        intro d
        rw [hpair.inner_pencil_embedding z d e, he]
        exact Submodule.inner_right_of_mem_orthogonal
          (⟨d, rfl⟩ : A.embedding d ∈ A.embedding.range) hy
      have hezero : e = 0 := by
        apply Astar.embedding_injective
        simpa using hembeddingZero
      have hyzero : y = 0 := by
        rw [← he, hezero, map_zero]
      simp [hyzero]
    · exact bot_le
  have hclosure : A.embedding.range.topologicalClosure = ⊤ := by
    rw [← A.embedding.range.orthogonal_orthogonal_eq_closure, horth,
      Submodule.bot_orthogonal_eq_top]
  have hsetClosure : closure (A.embedding.range : Set X) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, hclosure, Submodule.top_coe]
  change Dense (Set.range A.embedding)
  have hrange : Set.range A.embedding = (A.embedding.range : Set X) := by
    ext x
    simp
  rw [hrange]
  exact dense_iff_closure_eq.mpr hsetClosure

/-- Construct the maximal adjoint realization from the formal pairing, a
surjective adjoint pencil at `star z`, and dense range of the original pencil
at `z`.  These hypotheses are strictly smaller than an adjoint graph
characterization. -/
theorem isAdjointRealization_of_formalAdjointPairing_of_surjective_pencil
    [CompleteSpace X]
    (hpair : FormalAdjointPairing A Astar) {z : ℂ}
    (hsurjectiveStar : Function.Surjective (Astar.pencil (star z)))
    (hdense : DenseRange (A.pencil z)) :
    A.IsAdjointRealization Astar where
  dense_domain :=
    denseRange_embedding_of_formalAdjointPairing_of_surjective_pencil
      hpair hsurjectiveStar hdense
  graph_iff := by
    intro y g
    constructor
    · rintro ⟨e, rfl, rfl⟩ d
      exact hpair d e
    · intro hp
      obtain ⟨e, he⟩ := hsurjectiveStar ((star z) • y - g)
      have herror : Astar.embedding e - y = 0 := by
        apply hdense.eq_zero_of_inner_right ℂ
        intro d
        rw [inner_sub_right, hpair.inner_pencil_embedding z d e, he,
          inner_pencil_eq_of_graph_pairing hp z d, sub_self]
      have hembedding : Astar.embedding e = y := sub_eq_zero.mp herror
      have hoperation : Astar.op e = g := by
        have he' := he
        change (star z) • Astar.embedding e - Astar.op e =
          (star z) • y - g at he'
        rw [hembedding] at he'
        exact sub_right_inj.mp he'
      exact ⟨e, hembedding, hoperation⟩

end DomainOperator

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}

/-- A chosen right inverse makes every pencil in its resolver set
surjective. -/
theorem surjective_pencil
    (h : HasResolventOn A S) {z : ℂ} (hz : z ∈ S) :
    Function.Surjective (A.pencil z) := by
  intro x
  refine ⟨h.inv z x, ?_⟩
  have hright := congrArg (fun T : X →L[ℂ] X ↦ T x) (h.right_inv z hz)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hright

end HasResolventOn

namespace DomainOperator

universe u v w

variable {X : Type u} {D : Type v} {E : Type w}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {A : DomainOperator X D} {Astar : DomainOperator X E}
  {S T : Set ℂ}

/--
One forward reference resolver and one conjugate formal-adjoint surjectivity
statement supply exactly the closed-graph and maximal-adjoint inputs used by
the numerical-range resolvent criterion.

The forward resolver is used in two independent ways: its left inverse cuts
out the graph of `A` as a closed kernel, while its right inverse makes the
reference pencil dense.  No closedness or adjoint-domain maximality is assumed.
-/
theorem adjointRealization_and_closedGraph_of_formalAdjoint_reference
    (hpair : FormalAdjointPairing A Astar)
    (hreference : HasResolventOn A S) {z0 : ℂ} (hz0 : z0 ∈ S)
    (hsurjectiveStar : Function.Surjective (Astar.pencil (star z0))) :
    A.IsAdjointRealization Astar ∧ A.IsClosedGraph := by
  constructor
  · exact A.isAdjointRealization_of_formalAdjointPairing_of_surjective_pencil
      hpair hsurjectiveStar (hreference.surjective_pencil hz0).denseRange
  · exact A.isClosedGraph_of_leftInverse z0 (hreference.inv z0)
      (hreference.left_inv z0 hz0)

end DomainOperator

end

end FastDynamo
