/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Fin.Basic

/-!
# Nine N

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hcontribution_261.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : ℕ → TreeSequence G e0 := fun (i : ℕ) => TreeSequencePrefix T (min (A.length + i)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + i) T.length) =>
    by
          omega
    ) (Nat.min_le_right (A.length + i) T.length);
    let B : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun (v : V) => MissingColors G phi v;
    let U : ℕ → Finset (Fin k) := fun (i : ℕ) => {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + i ∧ phi (T.edge r) = some
        c};
    let X : ℕ → Finset (Fin k) := fun (i : ℕ) => (TreeMissingColors phi (Ty i) \ B) \ U i;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (good.gamma q);
    ∀ (i : ℕ),
    let C : Finset (Fin k) := X i ∩ (Gamma ∪ D);
    let Q : Fin k → Finset (Fin k) := fun (eta : Fin k) => good.gamma q eta ∪ { eta };
    let F : Finset (Fin k) := {eta ∈ D | Q eta ⊆ C};
    ∀ (_ : (
    ∀ eta ∈ D, (Q eta).card = (3 : ℕ))),
    ∀ eta ∈ D, (Q eta ∩ C).card ≤ (2 : ℕ) + if eta ∈ F then (1 : ℕ) else (0 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good n Tn q A Ty B U X D Gamma i C Q F hQcard
      eta heta
  by_cases hf : eta ∈ F
  · have hc := Finset.card_le_card
      (show Q eta ∩ C ⊆ Q eta from Finset.inter_subset_left)
    rw [hQcard eta heta] at hc
    simpa [hf] using hc
  · have hstrict : Q eta ∩ C ⊂ Q eta := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      apply hf
      apply Finset.mem_filter.mpr
      refine ⟨heta, ?_⟩
      intro c hc
      have hcc : c ∈ Q eta ∩ C := heq.symm ▸ hc
      exact (Finset.mem_inter.mp hcc).2
    have hc := Finset.card_lt_card hstrict
    rw [hQcard eta heta] at hc
    simp only [hf, ↓reduceIte, Nat.add_zero]
    omega

private theorem helper_hUcard_229.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : ℕ → TreeSequence G e0 := fun (i : ℕ) => TreeSequencePrefix T (min (A.length + i)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + i) T.length) => (
    by first  | omega
    )) (Nat.min_le_right (A.length + i) T.length);
    let U : ℕ → Finset (Fin k) := fun (i : ℕ) => {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + i ∧ phi (T.edge r) = some
        c};
    ∀ (i : ℕ) (_ : (Ty i).length = A.length + i),
    let N : Finset V := TreeSequenceVertexSet (Ty i) \ TreeSequenceVertexSet A;
    ∀ (_ : N.card = i), (U i).card ≤ i := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H q A Ty U i hilen N hNcard
  have witnesses : ∀ c ∈ U i, ∃ r : Fin T.length,
      A.length ≤ r.val ∧ r.val < A.length + i ∧ phi (T.edge r) = some c := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  let r := fun c : {c // c ∈ U i} => Classical.choose (witnesses c.val c.property)
  have hr (c : {c // c ∈ U i}) := Classical.choose_spec (witnesses c.val c.property)
  let f : {c // c ∈ U i} → Fin i := fun c =>
    ⟨(r c).val - A.length, by have := hr c; dsimp [r]; omega⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hc := hr c
    have hd := hr d
    have hval := congrArg Fin.val hcd
    change (r c).val - A.length = (r d).val - A.length at hval
    have he : r c = r d := by apply Fin.ext; dsimp [r] at *; omega
    apply Subtype.ext
    apply Option.some.inj
    exact hc.2.2.symm.trans ((congrArg (fun s => phi (T.edge s)) he).trans hd.2.2)
  simpa using Fintype.card_le_of_injective f hf

private theorem helper_hQdis_274.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (good : GoodHierarchy H),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (good.gamma q);
    let Q : Fin k → Finset (Fin k) := fun (eta : Fin k) => good.gamma q eta ∪ { eta };
    ∀ (_ : Disjoint Gamma D),
    (↑D : Set (Fin k)).PairwiseDisjoint Q := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good q D Gamma Q hreserved eta heta theta
      htheta hne
  change Disjoint (Q eta) (Q theta)
  rw [Finset.disjoint_left]
  intro c hc hd
  simp only [Q, Finset.mem_union, Finset.mem_singleton] at hc hd
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact Finset.disjoint_left.mp (good.disjointPairs q eta theta heta htheta hne) hc hd
  · exact Finset.disjoint_left.mp hreserved
      (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩) (hd.symm ▸ htheta)
  · exact Finset.disjoint_left.mp hreserved
      (Finset.mem_biUnion.mpr ⟨theta, htheta, hd⟩) (hc.symm ▸ heta)
  · exact hne (hc.symm.trans hd)

private theorem helper_hcover_287.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : ℕ → TreeSequence G e0 := fun (i : ℕ) => TreeSequencePrefix T (min (A.length + i)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + i) T.length) => (
    by first  | omega
    )) (Nat.min_le_right (A.length + i) T.length);
    let B : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun (v : V) => MissingColors G phi v;
    let U : ℕ → Finset (Fin k) := fun (i : ℕ) => {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + i ∧ phi (T.edge r) = some
        c};
    let X : ℕ → Finset (Fin k) := fun (i : ℕ) => (TreeMissingColors phi (Ty i) \ B) \ U i;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (good.gamma q);
    ∀ (i : ℕ),
    let C : Finset (Fin k) := X i ∩ (Gamma ∪ D);
    let Q : Fin k → Finset (Fin k) := fun (eta : Fin k) => good.gamma q eta ∪ { eta }; C =
        D.biUnion fun (eta : Fin k) => Q eta ∩ C := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good n Tn q A Ty B U X D Gamma i C Q
  ext c
  constructor
  · intro hc
    have hstored := (Finset.mem_inter.mp hc).2
    rcases Finset.mem_union.mp hstored with hg | hd
    · obtain ⟨eta, heta, hce⟩ := Finset.mem_biUnion.mp hg
      exact Finset.mem_biUnion.mpr
        ⟨eta, heta, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hce, hc⟩⟩
    · exact Finset.mem_biUnion.mpr
        ⟨c, hd, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self c), hc⟩⟩
  · intro hc
    obtain ⟨eta, _, hce⟩ := Finset.mem_biUnion.mp hc
    exact (Finset.mem_inter.mp hce).2

private theorem helper_continuation_351.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : ℕ → TreeSequence G e0 := fun (i : ℕ) => TreeSequencePrefix T (min (A.length + i)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + i) T.length) => (
    by first  | omega
    )) (Nat.min_le_right (A.length + i) T.length);
    let B : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun (v : V) => MissingColors G phi v;
    let U : ℕ → Finset (Fin k) := fun (i : ℕ) => {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + i ∧ phi (T.edge r) = some
        c};
    let X : ℕ → Finset (Fin k) := fun (i : ℕ) => (TreeMissingColors phi (Ty i) \ B) \ U i;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (good.gamma q);
    ∀ (i : ℕ) (_ : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (X i).card) (_ : (X i \ (Gamma ∪ D)).card ≤
        (4 : ℕ)),
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ TreeMissingColors phi (Ty i) ∧ Disjoint (good.gamma q
        (eta h) ∪ {eta h}) (U i) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good n Tn q A Ty B U X D Gamma i havailable hsmall
  let C := X i ∩ (Gamma ∪ D)
  let Q := fun eta => good.gamma q eta ∪ {eta}
  let F := D.filter fun eta => Q eta ⊆ C
  have hCcard : 2 * ett.rounds + 7 ≤ C.card := by
    have hc := Finset.card_inter_add_card_sdiff (X i) (Gamma ∪ D)
    change C.card + (X i \ (Gamma ∪ D)).card = (X i).card at hc
    omega
  have hreserved : Disjoint Gamma D := (GoodHierarchyReservedDisjoint good q).2
  have hQcard : ∀ eta ∈ D, (Q eta).card = 3 := by
    intro eta heta
    have hn : eta ∉ good.gamma q eta := by
      intro he
      exact Finset.disjoint_left.mp hreserved
        (Finset.mem_biUnion.mpr ⟨eta, heta, he⟩) heta
    simp only [Q, Finset.union_singleton, Finset.card_insert_of_notMem hn,
      good.twoColors q eta heta]
  have hQdis : (D : Set (Fin k)).PairwiseDisjoint Q := by
    exact @helper_hQdis_274 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base H good hreserved
  have hcover : C = D.biUnion (fun eta => Q eta ∩ C) := by
    exact @helper_hcover_287 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base H good i
  have hCsum : C.card = ∑ eta ∈ D, (Q eta ∩ C).card := by
    calc
      C.card = (D.biUnion fun eta => Q eta ∩ C).card := congrArg Finset.card hcover
      _ = ∑ eta ∈ D, (Q eta ∩ C).card := ?_
    apply Finset.card_biUnion
    intro eta heta theta htheta hne
    change Disjoint (Q eta ∩ C) (Q theta ∩ C)
    rw [Finset.disjoint_left]
    intro c hc hd
    exact Finset.disjoint_left.mp (hQdis heta htheta hne)
      (Finset.mem_inter.mp hc).1 (Finset.mem_inter.mp hd).1
  have hcontribution : ∀ eta ∈ D,
      (Q eta ∩ C).card ≤ 2 + if eta ∈ F then 1 else 0 := by
    exact @helper_hcontribution_261 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base H good i hQcard
  have hFsub : F ⊆ D := Finset.filter_subset _ _
  have hindicator : (∑ eta ∈ D, if eta ∈ F then (1 : ℕ) else 0) = F.card := by
    rw [← Finset.sum_filter]
    have hfilter : D.filter (fun eta => eta ∈ F) = F := by
      ext eta
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hFsub h, h⟩⟩
    rw [hfilter]
    simp
  have hupper : C.card ≤ 2 * D.card + F.card := by
    rw [hCsum]
    calc
      (∑ eta ∈ D, (Q eta ∩ C).card) ≤
          ∑ eta ∈ D, (2 + if eta ∈ F then 1 else 0) :=
        Finset.sum_le_sum hcontribution
      _ = 2 * D.card + F.card := by
        rw [Finset.sum_add_distrib, hindicator]
        simp [Nat.mul_comm]
  have hseven : 7 ≤ F.card := by
    have hd : D.card ≤ ett.rounds := HierarchyStoredColorsCardinality H q
    omega
  obtain ⟨eta, heta⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 7) (s := F) (by simpa using hseven)
  refine ⟨eta, eta.injective, ?_⟩
  intro h
  have hf : eta h ∈ F := heta ⟨h, rfl⟩
  obtain ⟨hd, hfull⟩ := Finset.mem_filter.mp hf
  have hCX : C ⊆ X i := Finset.inter_subset_left
  have hself : eta h ∈ Q (eta h) := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hx : eta h ∈ X i := hCX (hfull hself)
  refine ⟨hd, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1, ?_⟩
  rw [Finset.disjoint_left]
  intro c hc hu
  exact (Finset.mem_sdiff.mp (hCX (hfull hc))).2 hu

private theorem helper_continuation_195.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let Ty : ℕ → TreeSequence G e0 := fun (i : ℕ) => TreeSequencePrefix T (min (A.length + i)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + i) T.length) =>
    by
          omega
    ) (Nat.min_le_right (A.length + i) T.length);
    let B : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun (v : V) => MissingColors G phi v;
    let U : ℕ → Finset (Fin k) := fun (i : ℕ) => {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + i ∧ phi (T.edge r) = some
        c};
    let X : ℕ → Finset (Fin k) := fun (i : ℕ) => (TreeMissingColors phi (Ty i) \ B) \ U i;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (good.gamma q);
    ∀ (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet (Ty (ell - (1 : ℕ))))) (_ : (2
        : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) (_ :
        TreeSequenceInitialSegment A T) (_ : TreeSequenceVertexSet base.core ⊆
        TreeSequenceVertexSet A) (_ : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core)
        (_ : MaximumDegree G + (1 : ℕ) ≤ k) (_ : (
    ∀ j ≤ ell, (Ty j).length = A.length + j)) (_ : (
    ∀ (a b : ℕ) (_ : (Ty a).length ≤ (Ty b).length), TreeSequenceVertexSet (Ty a) ⊆
        TreeSequenceVertexSet (Ty b))) (_ : (
    ∀ {S R : TreeSequence G e0} (_ : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet R),
        TreeMissingColors phi S ⊆ TreeMissingColors phi R)),
    ∀ i < ell, i ≤ ell - (1 : ℕ) → (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (X i).card ∧ ((X i \ (Gamma ∪
        D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ TreeMissingColors phi (Ty i) ∧ Disjoint (good.gamma q
        (eta h) ∪ {eta h}) (U i)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good n Tn q A ell Ty B U X D Gamma
      hprefixElementary hlarge hAT hcoreA hTnCore hdegree hTylen prefixMono missingMono i hi hiell
  have hilen := hTylen i (by omega)
  have hlastlen := hTylen (ell - 1) (by omega)
  have hYiLast := prefixMono i (ell - 1) (by omega)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet (Ty i)) := by
    intro u hu v hv huv
    exact hprefixElementary (hYiLast hu) (hYiLast hv) huv
  have hAY : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet (Ty i) := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨r, hr⟩ := hv
    obtain ⟨hlen, hver, _⟩ := hAT
    refine ⟨⟨r.val, by have := r.isLt; omega⟩, ?_⟩
    change T.vertex _ = v
    exact (hver r).trans hr
  let N := TreeSequenceVertexSet (Ty i) \ TreeSequenceVertexSet A
  let M := N.biUnion fun v => MissingColors G phi v
  have hNcard : N.card = i := by
    have hcard (S : TreeSequence G e0) : (TreeSequenceVertexSet S).card = S.length + 1 := by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective, S.vertex_injective]
    have hc := Finset.card_sdiff_add_card_eq_card hAY
    change N.card + (TreeSequenceVertexSet A).card =
      (TreeSequenceVertexSet (Ty i)).card at hc
    rw [hcard, hcard, hilen] at hc
    omega
  have hMcard : i ≤ M.card := by
    have hdis : (N : Set V).PairwiseDisjoint (fun v => MissingColors G phi v) := by
      intro u hu v hv huv
      exact helem (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1 huv
    change i ≤ (N.biUnion fun v => MissingColors G phi v).card
    rw [Finset.card_biUnion hdis]
    calc
      i = ∑ v ∈ N, (1 : ℕ) := by simp [hNcard]
      _ ≤ ∑ v ∈ N, (MissingColors G phi v).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact Finset.one_le_card.mpr (MissingColorsNonemptyOfMaximumDegree G phi hdegree v)
  have unionDisjoint : ∀ (P Q : Finset V),
      P ⊆ TreeSequenceVertexSet (Ty i) → Q ⊆ TreeSequenceVertexSet (Ty i) →
      Disjoint P Q → Disjoint (P.biUnion fun v => MissingColors G phi v)
        (Q.biUnion fun v => MissingColors G phi v) := by
    intro P Q hP hQ hd
    rw [Finset.disjoint_left]
    intro c hc hd'
    obtain ⟨u, hu, hcu⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hd'
    have hne : u ≠ v := by
      intro huv
      exact Finset.disjoint_left.mp hd hu (huv.symm ▸ hv)
    exact Finset.disjoint_left.mp (helem (hP hu) (hQ hv) hne) hcu hcv
  have hAMdis : Disjoint (TreeMissingColors phi A) M := by
    apply unionDisjoint (TreeSequenceVertexSet A) N hAY
      (fun v hv => (Finset.mem_sdiff.mp hv).1)
    rw [Finset.disjoint_left]
    exact fun v hv hn => (Finset.mem_sdiff.mp hn).2 hv
  have hAMeq : TreeMissingColors phi A ∪ M = TreeMissingColors phi (Ty i) := by
    ext c
    simp only [TreeMissingColors, M, N, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_sdiff]
    constructor
    · rintro (⟨v, hv, hc⟩ | ⟨v, ⟨hv, _⟩, hc⟩)
      · exact ⟨v, hAY hv, hc⟩
      · exact ⟨v, hv, hc⟩
    · rintro ⟨v, hv, hc⟩
      by_cases ha : v ∈ TreeSequenceVertexSet A
      · exact Or.inl ⟨v, ha, hc⟩
      · exact Or.inr ⟨v, ⟨hv, ha⟩, hc⟩
  have hAMcard : (TreeMissingColors phi A).card + M.card =
      (TreeMissingColors phi (Ty i)).card := by
    rw [← hAMeq, Finset.card_union_of_disjoint hAMdis]
  have hTnA := hTnCore.trans hcoreA
  have hTBdis : Disjoint (TreeMissingColors phi Tn) B := by
    apply unionDisjoint (TreeSequenceVertexSet Tn)
      (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn)
      (hTnA.trans hAY)
      (fun v hv => hAY (hcoreA (Finset.mem_sdiff.mp hv).1))
    rw [Finset.disjoint_left]
    exact fun v hv hn => (Finset.mem_sdiff.mp hn).2 hv
  have hTBA : TreeMissingColors phi Tn ∪ B ⊆ TreeMissingColors phi A := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact missingMono hTnA hc
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨v, hcoreA (Finset.mem_sdiff.mp hv).1, hcv⟩
  have hbaseCount : (TreeMissingColors phi Tn).card + B.card ≤
      (TreeMissingColors phi A).card := by
    rw [← Finset.card_union_of_disjoint hTBdis]
    exact Finset.card_le_card hTBA
  have hUcard : (U i).card ≤ i := by
    exact @helper_hUcard_229 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base H i hilen hNcard
  have havailable : 2 * ett.rounds + 11 ≤ (X i).card := by
    have hfirst : (TreeMissingColors phi (Ty i)).card ≤
        (TreeMissingColors phi (Ty i) \ B).card + B.card :=
      Finset.card_le_card_sdiff_add_card
    have hsecond : (TreeMissingColors phi (Ty i) \ B).card ≤ (X i).card + (U i).card :=
      Finset.card_le_card_sdiff_add_card
    omega
  refine ⟨havailable, ?_⟩
  intro hsmall
  exact @helper_continuation_351 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base H good i havailable hsmall
theorem NineN {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (_ : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hprefixElementary :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := fun i : ℕ =>
        TreeSequencePrefix T (min (A.length + i) T.length)
          (by have hA := A.positive; have hT := T.positive; omega)
          (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (Ty (ell - 1))))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := T.length - A.length
    let Ty := fun i : ℕ =>
      TreeSequencePrefix T (min (A.length + i) T.length)
        (by have hA := A.positive; have hT := T.positive; omega) (Nat.min_le_right _ _)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion fun v =>
        MissingColors G phi v)
    let tailUsed := fun i : ℕ =>
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < A.length + i ∧ phi (T.edge r) = some c
    let available := fun i : ℕ =>
      (TreeMissingColors phi (Ty i) \ baseExtraMissing) \ tailUsed i
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (good.gamma q)
    ∀ i : ℕ,
    i < ell →
    2 * ett.rounds + 11 ≤ (available i).card ∧
      ((available i \ (Gamma ∪ D)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k,
          Function.Injective eta ∧
            ∀ h : Fin 7,
              eta h ∈ D ∧
                eta h ∈ TreeMissingColors phi (Ty i) ∧
                  Disjoint (good.gamma q (eta h) ∪ {eta h}) (tailUsed i)) := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := T.length - A.length
  let Ty := fun i : ℕ =>
    TreeSequencePrefix T (min (A.length + i) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
  let B := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
    fun v => MissingColors G phi v
  let U := fun i : ℕ => (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length,
      A.length ≤ r.val ∧ r.val < A.length + i ∧ phi (T.edge r) = some c
  let X := fun i : ℕ => (TreeMissingColors phi (Ty i) \ B) \ U i
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (good.gamma q)
  change ColoredVertexSetElementary G phi
    (TreeSequenceVertexSet (Ty (ell - 1))) at hprefixElementary
  change 2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card at hlarge
  change ∀ i : ℕ, i < ell →
    2 * ett.rounds + 11 ≤ (X i).card ∧
      ((X i \ (Gamma ∪ D)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h : Fin 7, eta h ∈ D ∧
            eta h ∈ TreeMissingColors phi (Ty i) ∧
            Disjoint (good.gamma q (eta h) ∪ {eta h}) (U i))
  have stageMono : Monotone (fun j => TreeSequenceVertexSet (H.stage j)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    exact TreeSequenceInitialSegmentVertexSetSubset (H.nested j)
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hA : A = base.core := by
        have hq : q = 0 := by apply Fin.ext; simp [q, hz]
        simp [A, HierarchyStarredStage, hq]
      have ht : H.stage ⟨1, by omega⟩ = T := by
        convert H.terminalStage using 1; congr 1; apply Fin.ext; simp [hz]
      simpa only [hA, ht] using H.coreInsideFirst
    · let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by apply Fin.ext; simp [q, r]; omega
      have hA : A = H.stage r.succ.castSucc := by
        change HierarchyStarredStage H q = _
        rw [hq]
        rfl
      have ht : q.succ = Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [q]
      have hc : H.stage r.succ.succ = T := by
        simpa only [hq] using (congrArg H.stage ht).trans H.terminalStage
      simpa only [hq, ← hA, hc] using H.nested q
  have hcoreA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A := by
    by_cases hz : H.dividerCount = 0
    · have hA : A = base.core := by
        have hq : q = 0 := by apply Fin.ext; simp [q, hz]
        simp [A, HierarchyStarredStage, hq]
      rw [hA]
    · let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by apply Fin.ext; simp [q, r]; omega
      have hA : A = H.stage r.succ.castSucc := by
        change HierarchyStarredStage H q = _
        rw [hq]
        rfl
      rw [hA]
      exact (TreeSequenceInitialSegmentVertexSetSubset H.coreInsideFirst).trans
        (stageMono (by change 1 ≤ r.val + 1; omega))
  have hTnCore : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      exact TreeSequenceInitialSegmentVertexSetSubset u.leftSegment
    · have hc := base.nonparallel hp
      change base.core = Tn at hc
      rw [hc]
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have hzero := ett.series.certified 0
    cases hzero with
    | initial triple => exact triple.2.2.1
  have hAlen : A.length ≤ T.length := hAT.choose
  have hTylen : ∀ j, j ≤ ell → (Ty j).length = A.length + j := by
    intro j hj
    change min (A.length + j) T.length = A.length + j
    apply Nat.min_eq_left
    dsimp [ell] at hj
    omega
  have prefixMono : ∀ a b, (Ty a).length ≤ (Ty b).length →
      TreeSequenceVertexSet (Ty a) ⊆ TreeSequenceVertexSet (Ty b) := by
    intro a b hab v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨r, hr⟩ := hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hab) r, ?_⟩
    simpa only [Ty, TreeSequencePrefix, Fin.castLE] using hr
  have missingMono : ∀ {S R : TreeSequence G e0},
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet R →
        TreeMissingColors phi S ⊆ TreeMissingColors phi R := by
    intro S R h c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, h hv, hcv⟩
  intro i hi
  have hiell : i ≤ ell - 1 := by omega
  exact @helper_continuation_195 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base H good hprefixElementary hlarge hAT hcoreA hTnCore hdegree hTylen
      prefixMono missingMono i hi hiell
end GoldbergSeymour

end
