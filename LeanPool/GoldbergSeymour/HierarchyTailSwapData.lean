/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength

/-!
# Shared terminal swap data for hierarchy advancement

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An elementary tail prefix retains missing colors under the terminal Kempe swap. -/
theorem HierarchyMinimumCounterexampleContext.tailSwapData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {C : HierarchyCounterexample base}
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (A B : TreeSequence G e0) (hAT : TreeSequenceInitialSegment A T)
    (hBT : TreeSequenceInitialSegment B T)
    (starEq : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A)
    (fullB : HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1) = B)
    (elementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B))
    (vertexMem : ∀ (U : TreeSequence G e0) (j : Fin (U.length + 1)),
      U.vertex j ∈ TreeSequenceVertexSet U)
    (componentData : ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
      IsProperEdgeColoring G psi → ∀ (vertices : Finset V),
      ColoredVertexSetElementary G psi vertices → ∀ u v w : V,
      u ∈ vertices → v ∈ vertices → u ≠ v → w ≠ u → w ≠ v →
      a ∈ MissingColors G psi u → b ∈ MissingColors G psi v →
      (a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) →
      TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
      Disjoint (TwoColorComponent G psi a b (Sum.inl w))
        (TwoColorComponent G psi a b (Sum.inl u)) ∧
      TwoColorPathComponent G psi a b (Sum.inl w) ∧
      ∀ x ∈ vertices, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
        MissingColors G psi x)
    (alpha theta : Fin k) (jm jnext : Fin (B.length + 1))
    (afterA : A.length < jm.val) (ordered : jm.val < jnext.val)
    (beforeLast : jnext.val < T.length)
    (haM : alpha ∈ MissingColors G phi (B.vertex jm))
    (htheta : theta ∈ MissingColors G phi (B.vertex jnext))
    (haLast : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hAlphaStored : alpha ∉ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount))
    (hThetaStored : theta ∉ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount))
    (haRaw : alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (hthetaRaw : theta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (iaEq : (HierarchyFirstMissingPosition phi T alpha).val = jm.val)
    (ibEq : (HierarchyFirstMissingPosition phi T theta).val = jnext.val)
    (haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < jnext.val →
      phi (T.edge t) ≠ some alpha) :
    alpha ≠ theta ∧
    TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) ∧
    ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) ∧
    (alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
      theta ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) ∧
    (∀ x ∈ TreeSequenceVertexSet B,
      MissingColors G (TwoColorComponentSwap G phi alpha theta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G phi x) ∧
    (∀ v ∈ TreeSequenceVertexSet A,
      TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition phi T alpha))) := by
  classical
  have hne : alpha ≠ theta := by
    intro he
    have hvertices : B.vertex jm ≠ B.vertex jnext := by
      intro hh
      have hh := congrArg Fin.val (B.vertex_injective hh)
      omega
    exact Finset.disjoint_left.mp (elementary
      (vertexMem B jm) (vertexMem B jnext) hvertices) haM (he ▸ htheta)
  have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) jm =
      HierarchyFirstMissingPosition phi T alpha := Fin.ext iaEq.symm
  have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jnext =
      HierarchyFirstMissingPosition phi T theta := Fin.ext ibEq.symm
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) :=
    ⟨_, _, rfl, rfl, by omega⟩
  have hunused : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition phi T theta).val ∧
        phi (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    exact haUnused t hlo (by rw [ibEq] at hhi; exact hhi) hc
  have haB : alpha ∈ TreeMissingColors phi B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jm, vertexMem B jm, haM⟩
  have hthetaB : theta ∈ TreeMissingColors phi B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jnext, vertexMem B jnext, htheta⟩
  have hprefixP : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C
        (HierarchyFullTailLength C - 1))) := by
    rw [fullB]
    exact elementary
  have hmissingP : alpha ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
      theta ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))
         := by
    rw [fullB]
    exact ⟨haB, hthetaB⟩
  have change := ChangeLemma G k e0 input T phi
    ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung
    ctx.fewerDividers ctx.lexicographicMinimality hprefixP
    ctx.largeMissingSet alpha theta hne hmissingP
    (by dsimp only; rw [starEq]; intro _; exact ⟨hordered, hunused⟩)
  have hdisStored : Disjoint ({alpha, theta} : Finset (Fin k))
      (HierarchyStoredColorsAt C.hierarchy
        (Fin.last C.hierarchy.dividerCount)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hAlphaStored hd
    · exact hThetaStored hd
  have hdisRaw : Disjoint ({alpha, theta} : Finset (Fin k))
      (TashkinovStoredColors ett.series.data
        (Fin.last ett.rounds)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact haRaw hd
    · exact hthetaRaw hd
  have hsame : TwoColorComponent G phi alpha theta (Sum.inl (B.vertex jm)) =
      TwoColorComponent G phi alpha theta (Sum.inl (B.vertex jnext)) := by
    have hh : TwoColorComponent G phi alpha theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) =
        TwoColorComponent G phi alpha theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) := by
      by_cases hq : C.hierarchy.dividerCount = 0
      · exact change.2.1 ⟨hq, Or.inr hdisRaw⟩
      · exact change.1 ⟨by omega, Or.inr hdisStored⟩
    rw [← jaEq, ← jbEq, hBT.2.1 jm, hBT.2.1 jnext] at hh
    exact hh
  obtain ⟨hdis, hpath, hmissing⟩ := componentData phi alpha theta hne
    ctx.proper (TreeSequenceVertexSet B) (elementary)
    (B.vertex jm) (B.vertex jnext) (T.vertex (Fin.last T.length))
    (vertexMem B jm) (vertexMem B jnext)
    (by intro hh; have hh := congrArg Fin.val (B.vertex_injective hh)
        omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jm).symm)
        have hh := congrArg Fin.val hh
        change T.length = jm.val at hh
        omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jnext).symm)
        have hh := congrArg Fin.val hh
        change T.length = jnext.val at hh
        omega)
    haM htheta (Or.inl haLast) hsame
  have hprecedes : ∀ v ∈ TreeSequenceVertexSet A,
      TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition phi T alpha)) := by
    intro v hv
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hAT.1) j, _, (hAT.2.1 j).trans hj, rfl, ?_⟩
    change j.val < (HierarchyFirstMissingPosition phi T alpha).val
    rw [iaEq]
    have := j.isLt
    omega
  exact ⟨hne, hordered, hprefixP, hmissingP, hmissing, hprecedes⟩

end GoldbergSeymour

end
