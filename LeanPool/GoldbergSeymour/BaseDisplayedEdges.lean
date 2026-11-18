/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.CombinedStableColoring

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# P2813_T1_Base Displayed Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem P2813_T1_BaseDisplayedEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (sigma : PartialEdgeColoring E k)
    (hone : IsOneEdgeUncolored phi e0)
    (hsone : IsOneEdgeUncolored sigma e0)
    (hstable :
      let n := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma) :
    ∀ t : Fin base.core.length,
      sigma (base.core.edge t) = phi (base.core.edge t) := by
  classical
  let n := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
    CombinedStableColoring Tn base.closure Dn phi sigma
    else StableColoring Tn Dn phi sigma) at hstable
  have hnStable : StableColoring Tn Dn phi sigma := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (ite_eq_left hp ▸ hstable).1
    · simpa only [hp, ite_false] using hstable
  have treeFixed (t : Fin Tn.length) :
      sigma (Tn.edge t) = phi (Tn.edge t) := by
    by_cases ht : t.val = 0
    · have he : Tn.edge t = e0 := by
        rw [show t = ⟨0, Tn.positive⟩ from Fin.ext ht]
        exact Tn.first_edge
      rw [he, hone.1, hsone.1]
    · obtain ⟨c, hc⟩ := hone.2 (Tn.edge t) (by
        intro he
        have hh : Tn.edge t = Tn.edge ⟨0, Tn.positive⟩ :=
          he.trans Tn.first_edge.symm
        have hv := congrArg Fin.val (Tn.edge_injective hh)
        exact ht hv)
      let j : Fin ett.rounds := ⟨ett.rounds - 1, by
        have := ett.roundsPositive; omega⟩
      have hj : j.succ = n := Fin.ext (by
        dsimp [j, n]; have := ett.roundsPositive; omega)
      have hu : c ∈ TreeUsedColors (ett.series.data.coloring j.succ)
          (ett.series.data.tree j.succ.castSucc) := by
        simp only [hj, ← ett.generatingColoring, n]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, by omega, hc⟩
      have hm : c ∈ TreeMissingColors phi Tn ∪ Dn := by
        simpa only [hj, ← ett.generatingColoring, Tn, Dn, n] using
          (HkuTreeColorsControlled G k ett.rounds e0 input ett.series j).2.1 hu
      have hi : TreeIncidentEdge Tn (Tn.edge t) := by
        obtain ⟨i, hi⟩ := Tn.attaches t
        refine ⟨Tn.vertex t.succ, ?_, ?_⟩
        · simp only [TreeSequenceVertexSet, Finset.mem_image,
            Finset.mem_univ, true_and]
          exact ⟨t.succ, rfl⟩
        · rw [Incident, hi]
          exact Sym2.mem_mk_left _ _
      exact hnStable.1 _ hi ⟨c, hm, hc⟩
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have hrStable : StableColoring base.closure ∅ phi sigma :=
      (ite_eq_left hp ▸ hstable).2
    obtain ⟨union⟩ := (base.parallel hp).2.2
    let P := TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
      (Nat.le_of_lt_succ base.supportPosition.isLt)
    have hPN : TreeSequenceInitialSegment P Tn :=
      ⟨Nat.le_of_lt_succ base.supportPosition.isLt, fun _ => rfl, fun _ => rfl⟩
    have hseq : TashkinovAugmentationSequence phi P base.closure :=
      (base.parallel hp).2.1.1
    have hPR := TashkinovAugmentationSequenceInitialSegment phi P base.closure hseq
    have closureFixed (t : Fin base.closure.length) :
        sigma (base.closure.edge t) = phi (base.closure.edge t) := by
      by_cases ht : t.val < P.length
      · let u : Fin P.length := ⟨t.val, ht⟩
        have he : Fin.castLE hPR.1 u = t := Fin.ext rfl
        rw [← he, hPR.2.2 u, ← hPN.2.2 u]
        exact treeFixed _
      · obtain ⟨hlen, hinit, c, hcol, hm⟩ :=
          (TashkinovAugmentationSequencePosition phi P base.closure hseq t (by omega)).1
        have hcolR : phi (base.closure.edge t) = some c := by
          convert hcol using 1
          congr 2
        obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
        have hprefix : TreeSequenceInitialSegment
            (TreeSequencePrefix base.closure t.val
              (le_trans P.positive (by omega)) (Nat.le_of_lt t.isLt))
            base.closure := ⟨Nat.le_of_lt t.isLt, fun _ => rfl, fun _ => rfl⟩
        have hmR : c ∈ TreeMissingColors phi base.closure :=
          Finset.mem_biUnion.mpr
            ⟨v, TreeSequenceInitialSegmentVertexSetSubset hprefix hv, hvm⟩
        have hiR : TreeIncidentEdge base.closure (base.closure.edge t) := by
          obtain ⟨i, hi⟩ := base.closure.attaches t
          refine ⟨base.closure.vertex t.succ, ?_, ?_⟩
          · simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and]
            exact ⟨t.succ, rfl⟩
          · rw [Incident, hi]
            exact Sym2.mem_mk_left _ _
        exact hrStable.1 _ hiR ⟨c, Finset.mem_union_left ∅ hmR, hcolR⟩
    intro t
    by_cases ht : t.val < Tn.length
    · let u : Fin Tn.length := ⟨t.val, ht⟩
      have he : Fin.castLE union.leftSegment.1 u = t := Fin.ext rfl
      rw [← he, union.leftSegment.2.2 u]
      exact treeFixed u
    · obtain ⟨i, hi, _⟩ := union.newEntryFromRight t (Nat.le_of_not_gt ht)
      rw [hi]
      exact closureFixed i
  · rw [base.nonparallel hp]
    exact treeFixed

end GoldbergSeymour

end
