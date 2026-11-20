/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.FixedSectorBasic

/-!
# Closed range and adjoint criteria for bundled-domain operators

This module records the functional-analysis step that turns coercive estimates
for a closed, densely defined operator and its Hilbert-space adjoint into
surjectivity of a spectral pencil.  In particular, closedness and density of
the pencil range are conclusions rather than hypotheses.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace DomainOperator

universe u v w

open Filter Topology

variable {X : Type u} {D : Type v} {E : Type w}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A closed ambient graph and a lower bound in the ambient-state norm imply
that the pencil range is closed.  Completeness is needed only for the ambient
space: a convergent sequence of pencil values first determines the limit of
the embedded domain vectors, and graph closedness then recovers a domain
vector realizing the limiting value. -/
theorem isClosed_range_pencil_of_isClosedGraph_of_ambient_lower
    [CompleteSpace X]
    (A : DomainOperator X D) (hgraph : A.IsClosedGraph)
    (z : ℂ) (d0 : ℝ) (hd0 : 0 < d0)
    (hlower : ∀ d : D,
      d0 * ‖A.embedding d‖ ≤ ‖A.pencil z d‖) :
    IsClosed (Set.range (A.pencil z)) := by
  refine IsSeqClosed.isClosed ?_
  intro f y hf hfy
  choose u hu using hf
  have hfCauchy : CauchySeq f := hfy.cauchySeq
  have hembCauchy : CauchySeq (fun n ↦ A.embedding (u n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hfCauchy)
      (d0 * ε) (mul_pos hd0 hε)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hdist := hN m hm n hn
    rw [dist_eq_norm] at hdist ⊢
    have hl := hlower (u m - u n)
    simp only [map_sub, hu] at hl
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hembCauchy
  have hop : Tendsto (fun n ↦ A.op (u n)) atTop
      (nhds (z • x - y)) := by
    have heq : (fun n ↦ A.op (u n)) =
        (fun n ↦ z • A.embedding (u n) - f n) := by
      funext n
      rw [← hu n]
      change A.op (u n) = z • A.embedding (u n) -
        (z • A.embedding (u n) - A.op (u n))
      abel
    rw [heq]
    exact (hx.const_smul z).sub hfy
  have hpair : Tendsto (fun n ↦ (A.embedding (u n), A.op (u n)))
      atTop (nhds (x, z • x - y)) := by
    simpa only [nhds_prod_eq] using hx.prodMk hop
  have hmem : ∀ n, (A.embedding (u n), A.op (u n)) ∈ A.graphSet := by
    intro n
    exact ⟨u n, rfl⟩
  have hlimit : (x, z • x - y) ∈ A.graphSet :=
    hgraph.isSeqClosed hmem hpair
  obtain ⟨d, hd⟩ := hlimit
  refine ⟨d, ?_⟩
  have hemb : A.embedding d = x := congrArg Prod.fst hd
  have hopd : A.op d = z • x - y := congrArg Prod.snd hd
  change z • A.embedding d - A.op d = y
  rw [hemb, hopd]
  abel

/-- `Astar` realizes the Hilbert-space adjoint of the densely defined
operator represented by `A`.  The equivalence is the maximal adjoint-domain
condition, not merely the formal integration-by-parts identity. -/
structure IsAdjointRealization (A : DomainOperator X D)
    (Astar : DomainOperator X E) : Prop where
  dense_domain : DenseRange A.embedding
  graph_iff : ∀ y g : X,
    (∃ e : E, Astar.embedding e = y ∧ Astar.op e = g) ↔
      ∀ d : D, inner ℂ (A.op d) y = inner ℂ (A.embedding d) g

namespace IsAdjointRealization

variable {A : DomainOperator X D} {Astar : DomainOperator X E}

/-- Maximality of the realized adjoint domain. -/
theorem exists_of_pairing (h : IsAdjointRealization A Astar) (y g : X)
    (hp : ∀ d : D, inner ℂ (A.op d) y = inner ℂ (A.embedding d) g) :
    ∃ e : E, Astar.embedding e = y ∧ Astar.op e = g :=
  (h.graph_iff y g).mpr hp

end IsAdjointRealization

/-- A lower bound for the conjugate adjoint pencil forces the original
pencil to have dense range. -/
theorem denseRange_pencil_of_adjoint_lower
    [CompleteSpace X]
    (A : DomainOperator X D) (Astar : DomainOperator X E)
    (hadj : IsAdjointRealization A Astar) (z : ℂ) (dstar : ℝ)
    (hdstar : 0 < dstar)
    (hlowerStar : ∀ e : E,
      dstar * ‖Astar.embedding e‖ ≤ ‖Astar.pencil (star z) e‖) :
    DenseRange (A.pencil z) := by
  let P : D →L[ℂ] X := A.pencil z
  have horth : P.rangeᗮ = ⊥ := by
    apply le_antisymm
    · intro y hy
      have hyzero : y = 0 := by
        have hpair : ∀ d : D,
            inner ℂ (A.op d) y = inner ℂ (A.embedding d) ((star z) • y) := by
          intro d
          have hzero : inner ℂ (P d) y = 0 :=
            Submodule.inner_right_of_mem_orthogonal
              (⟨d, rfl⟩ : P d ∈ P.range) hy
          rw [show P d = z • A.embedding d - A.op d by rfl,
            inner_sub_left, inner_smul_left] at hzero
          rw [inner_smul_right]
          exact (sub_eq_zero.mp hzero).symm
        obtain ⟨e, hemb, hop⟩ := hadj.exists_of_pairing y ((star z) • y) hpair
        have hpencil : Astar.pencil (star z) e = 0 := by
          rw [show Astar.pencil (star z) e =
            (star z) • Astar.embedding e - Astar.op e by rfl,
            hemb, hop, sub_self]
        have hl := hlowerStar e
        rw [hpencil, norm_zero] at hl
        have : ‖y‖ = 0 := by
          rw [← hemb]
          nlinarith [norm_nonneg (Astar.embedding e)]
        exact norm_eq_zero.mp this
      simp [hyzero]
    · exact bot_le
  have hclosure : P.range.topologicalClosure = ⊤ := by
    rw [← P.range.orthogonal_orthogonal_eq_closure, horth,
      Submodule.bot_orthogonal_eq_top]
  have hsetClosure : closure (P.range : Set X) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, hclosure, Submodule.top_coe]
  change Dense (Set.range P)
  have hrange : Set.range P = (P.range : Set X) := by
    ext x
    simp
  rw [hrange]
  exact dense_iff_closure_eq.mpr hsetClosure

/-- The closed-range estimate for `A` and the conjugate-pencil estimate for
its Hilbert adjoint together imply surjectivity of `z - A`. -/
theorem surjective_pencil_of_isClosedGraph_of_ambient_lower_of_adjoint_lower
    [CompleteSpace X]
    (A : DomainOperator X D) (Astar : DomainOperator X E)
    (hadj : IsAdjointRealization A Astar)
    (hgraph : A.IsClosedGraph) (z : ℂ) (d0 dstar : ℝ)
    (hd0 : 0 < d0) (hdstar : 0 < dstar)
    (hlower : ∀ d : D,
      d0 * ‖A.embedding d‖ ≤ ‖A.pencil z d‖)
    (hlowerStar : ∀ e : E,
      dstar * ‖Astar.embedding e‖ ≤ ‖Astar.pencil (star z) e‖) :
    Function.Surjective (A.pencil z) := by
  have hclosed : IsClosed (Set.range (A.pencil z)) :=
    A.isClosed_range_pencil_of_isClosedGraph_of_ambient_lower
      hgraph z d0 hd0 hlower
  have hdense : DenseRange (A.pencil z) :=
    A.denseRange_pencil_of_adjoint_lower Astar hadj z dstar hdstar hlowerStar
  have hclosure : closure (Set.range (A.pencil z)) = Set.univ :=
    dense_iff_closure_eq.mp hdense
  rw [hclosed.closure_eq] at hclosure
  exact Set.range_eq_univ.mp hclosure

end DomainOperator

end

end FastDynamo
