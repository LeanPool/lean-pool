/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidencePathFacts
public import LeanPool.GoldbergSeymour.MissingColors

public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath

/-!
# Paths Starting at Incidence Leaves

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A leaf of a nontrivial component starts a spanning path
whose other endpoint is missing a color. -/
theorem TwoColorComponent.pathFromLeaf.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G :
    LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k), IsProperEdgeColoring G
    phi → ∀ (a b : Fin k), let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b; (∀
    (v : V), (H.neighborSet (Sum.inl v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈
    MissingColors G phi v) → ∀ (v : V) (c : V ⊕ E), Sum.inl v ∈ TwoColorComponent G phi a b c
    → (H.neighborSet (Sum.inl v)).Subsingleton → (∃ (e : E), Sum.inr e ∈ TwoColorComponent G
    phi a b c) → ∃ (s : V) (p : H.Walk (Sum.inl v) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈
    p.support} = TwoColorComponent G phi a b c ∧ v ≠ s ∧ (a ∈ MissingColors G phi s ∨ b ∈
    MissingColors G phi s) := by
  classical
  intro V E _ _ G k phi hproper a b H endpoint_missing v c hvC hvleaf hnontrivial
  let _ := Fintype.ofFinite V
  obtain ⟨u, w, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G phi a b hproper c
  have hvP : Sum.inl v ∈ p.support := by
    change Sum.inl v ∈ {y | y ∈ p.support}
    rw [hps]
    exact hvC
  have hvEnd : Sum.inl v = u ∨ Sum.inl v = w := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hvleaf) hvP
  obtain ⟨t, q, hq, hqs⟩ : ∃ (t : Sum V E)
      (q : H.Walk (Sum.inl v) t),
      q.IsPath ∧ {y | y ∈ q.support} =
        TwoColorComponent G phi a b c := by
    rcases hvEnd with hvu | hvw
    · subst u
      exact ⟨w, p, hp, hps⟩
    · subst w
      refine ⟨u, p.reverse, hp.reverse, ?_⟩
      ext y
      change y ∈ p.reverse.support ↔
        y ∈ TwoColorComponent G phi a b c
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact Set.ext_iff.mp hps y
  have hqnon : ¬ q.Nil := by
    intro hnil
    obtain ⟨e, heC⟩ := hnontrivial
    have heQ : Sum.inr e ∈ q.support := by
      change Sum.inr e ∈ {y | y ∈ q.support}
      rw [hqs]
      exact heC
    rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at heQ
    simp at heQ
  have hend_neighbor : ∀ y, H.Adj t y → y = q.getVert (q.length - 1) :=
    degreeTwoComponentPathEndNeighbor q hq
      (TwoColorIncidenceDegreeAtMostTwo G phi a b hproper)
      hvleaf hqs
  have hendLeaf : Set.Subsingleton (H.neighborSet t) := by
    intro y hy y' hy'
    exact (hend_neighbor y hy).trans (hend_neighbor y' hy').symm
  have hqpos : 0 < q.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hqnon
  have hendVertex : ∃ s : V, t = Sum.inl s := incidenceLeafEndVertex q hqpos hendLeaf
  obtain ⟨s, hs⟩ := hendVertex
  subst t
  have hvs : v ≠ s := by
    intro hvs
    apply hqnon
    exact hq.nil_iff_eq.mpr (by simp [hvs])
  exact ⟨s, q, hq, hqs, hvs, endpoint_missing s hendLeaf⟩

end GoldbergSeymour

end
