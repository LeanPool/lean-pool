/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ClosedSetTwoColorComponentAvoidance
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Hierarchy Counterexample One Addition Zero Divider Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hstar_138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core; HierarchyStarredStage H (Fin.last H.dividerCount) = A
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H A
  have hz : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) := by
    apply Fin.ext
    exact hzero
  rw [hz]
  rfl

private theorem helper_hfirst_144.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy; H.stage (⟨(1 : ℕ),
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H
  have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
      Fin.last (H.dividerCount + 1) := by
    apply Fin.ext
    simp only [Fin.val_last]
    change 1 = C.hierarchy.dividerCount + 1
    omega
  rw [hi]
  exact H.terminalStage

private theorem helper_hlen_155.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base), (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount); T.length -
        A.length = (1 : ℕ)) → C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core; HierarchyStarredStage H (Fin.last H.dividerCount) = A
        → TreeSequenceInitialSegment A T → T.length = A.length + (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C honeAddition hzero H A hstar hAT
  change T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length = 1
    at honeAddition
  rw [hstar] at honeAddition
  have := hAT.1
  omega

private theorem helper_prefixMem_161.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length); TreeSequenceInitialSegment A T → T.length =
        A.length + (1 : ℕ) →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet T → v ≠ y → v ∈ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hAT hlen v hv hne
  obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
  have hival : i.val < T.length := by
    by_contra hn
    have hiLast : i = Fin.last T.length := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    exact hne (hi.symm.trans (congrArg T.vertex hiLast))
  let j : Fin (A.length + 1) := ⟨i.val, by omega⟩
  have hji : Fin.castLE (Nat.succ_le_succ hAT.1) j = i := by
    apply Fin.ext
    rfl
  apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  exact (hAT.2.1 j).symm.trans (by simpa only [hji] using hi)

private theorem helper_hyNot_179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length); TreeSequenceInitialSegment A T → T.length =
        A.length + (1 : ℕ) → y ∉ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hAT hlen hy
  obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hy
  have hidx := T.vertex_injective ((hAT.2.1 i).trans hi)
  have hv := congrArg Fin.val hidx
  simp only [Fin.val_castLE, Fin.val_last] at hv
  have := i.isLt
  omega

private theorem helper_hAElementary_187.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base), (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            omega
    ) (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            omega
    ); ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty)) → C.hierarchy.dividerCount =
        (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core; HierarchyStarredStage H (Fin.last H.dividerCount) = A
        → TreeSequenceInitialSegment A T → T.length = A.length + (1 : ℕ) →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hprefixElementary hzero H A hstar hAT hlen
  let p := min (A.length + ((T.length - A.length) - 1)) T.length
  have hp : p = A.length := by dsimp [p]; omega
  let P := TreeSequencePrefix T p
    (by have := A.positive; dsimp [p]; omega) (Nat.min_le_right _ _)
  have hP : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) := by
    have hp := @hprefixElementary
    dsimp only at hp
    simp only [show HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A
      from hstar] at hp
    exact @hp
  have hvertices : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet P := by
    intro v hv
    obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    let j : Fin (p + 1) := ⟨i.val, by rw [hp]; exact i.isLt⟩
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    change T.vertex (Fin.castLE _ j) = v
    have hji : Fin.castLE (Nat.succ_le_succ (Nat.min_le_right _ _)) j =
        Fin.castLE (Nat.succ_le_succ hAT.1) i := by
      apply Fin.ext
      rfl
    rw [hji]
    exact (hAT.2.1 i).trans hi
  intro u hu v hv huv
  exact hP (hvertices hu) (hvertices hv) huv

private theorem helper_branch_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length); T.length = A.length + (1 : ℕ) → (
    ∀ {v : V}, v ∈ TreeSequenceVertexSet T → v ≠ y → v ∈ TreeSequenceVertexSet A) →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) → (
    ∀ alpha ∈ TreeMissingColors phi A, alpha ∉ MissingColors G phi y) →
    ∀ {u : V}, u ∈ TreeSequenceVertexSet T →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet T → u ≠ v → ¬u = y → Disjoint (MissingColors G phi u)
        (MissingColors G phi v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hlen prefixMem hAElementary hn u hu v
      hv huv huy
  have huA := prefixMem hu huy
  by_cases hvy : v = y
  · apply Finset.disjoint_left.mpr
    intro alpha hau hav
    exact hn alpha (Finset.mem_biUnion.mpr ⟨u, huA, hau⟩) (hvy ▸ hav)
  · exact hAElementary huA (prefixMem hv hvy) huv

private theorem helper_outsideEndpoint_233.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hlen : T.length = A.length + (1 : ℕ)), y ∉ TreeSequenceVertexSet A →
    ∀ (f : E) (u v : V), u ∈ TreeSequenceVertexSet A → G.ends f = s(u, v) → T.edge (⟨A.length,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              have := GoldbergSeymour.TreeSequence.positive A
              omega
    ⟩ : Fin T.length) = f → y = v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hlen hyNot f u v hu hends hf
  obtain ⟨i, hi⟩ := T.attaches ⟨A.length, by omega⟩
  have hyIncident : Incident G y f := by
    unfold Incident
    rw [← hf, hi]
    have hlast : (⟨A.length, by omega⟩ : Fin T.length).succ =
        Fin.last T.length := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    simp only [hlast, y, Sym2.mem_iff, true_or]
  have hyCases : y = u ∨ y = v := by
    simpa only [Incident, hends, Sym2.mem_iff] using hyIncident
  exact hyCases.resolve_left (by intro hyu; exact hyNot (by simpa only [hyu] using hu))

private theorem helper_commonPrefix_250.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero X Y Z hXZ hYZ hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro j
    have hx := hXZ.2.1 j
    have hy := hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) j)
    exact hy.symm.trans (by simpa only [Fin.castLE] using hx)
  · intro j
    have hx := hXZ.2.2 j
    have hy := hYZ.2.2 (Fin.castLE hXY j)
    exact hy.symm.trans (by simpa only [Fin.castLE] using hx)

private theorem helper_equalTrees_263.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero X Y hXY hl
  cases X with
  | mk lx px vx ex vix eix fx ax =>
    cases Y with
    | mk ly py vy ey viy eiy fy ay =>
      simp only at hl
      subst ly
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext j
        simpa only [Fin.castLE] using (hXY.2.1 j).symm
      · apply heq_of_eq
        funext j
        simpa only [Fin.castLE] using (hXY.2.2 j).symm

private theorem helper_leaf_279.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (u : V), a ∈ MissingColors G psi u ∨ b ∈ MissingColors G psi u → ((TwoColorIncidenceGraph G
        psi a b).neighborSet (Sum.inl u)).Subsingleton := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero psi a b hp u hm
  by_cases hab : a = b
  · subst b
    have ha : a ∈ MissingColors G psi u := hm.elim id id
    have hn : a ∉ PresentColors G psi u := by simpa [MissingColors] using ha
    intro z hz w hw
    exfalso
    cases z with
    | inl z => simp [TwoColorIncidenceGraph] at hz
    | inr f =>
      have hf : Incident G u f ∧ psi f = some a := by
        simpa [TwoColorIncidenceGraph] using hz
      exact hn (by simpa [PresentColors] using
        (show ∃ e, Incident G u e ∧ psi e = some a from ⟨f, hf⟩))
  · let : Fintype ((TwoColorIncidenceGraph G psi a b).neighborSet (Sum.inl u)) :=
      Fintype.ofFinite _
    have hd : (TwoColorIncidenceGraph G psi a b).degree (Sum.inl u) ≤ 1 := by
      rcases hm with hm | hm
      · exact MissingColorIncidenceEndpoint G psi a b hab hp u hm
      · have hd := MissingColorIncidenceEndpoint G psi b a (Ne.symm hab) hp u hm
        have hgraph : TwoColorIncidenceGraph G psi b a = TwoColorIncidenceGraph G psi a b := by
          ext z w
          cases z <;> cases w <;> simp [TwoColorIncidenceGraph, or_comm]
        rw [hgraph] at hd
        exact hd
    rw [← SimpleGraph.card_neighborSet_eq_degree] at hd
    have hsub := Fintype.card_le_one_iff.mp hd
    intro z hz w hw
    exact congrArg Subtype.val (hsub ⟨z, hz⟩ ⟨w, hw⟩)

private theorem helper_cycleEndpoint_314.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (cycle : TwoColorCycle G psi a b) (f : E) (u v
        : V), G.ends f = s(u, v) → Sum.inr f ∈ cycle.walk.support → Sum.inl v ∈ cycle.walk.support
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero psi a b cycle f u v hends hf
  let p := cycle.walk.rotate (Sum.inr f) hf
  have hp : p.IsCycle := cycle.isCycle.rotate hf
  have adjacent (z : Sum V E)
      (hz : (TwoColorIncidenceGraph G psi a b).Adj (Sum.inr f) z) :
      z = Sum.inl u ∨ z = Sum.inl v := by
    cases z with
    | inr e => exact hz.elim
    | inl w =>
      have hw : w = u ∨ w = v := by
        simpa only [Incident, hends, Sym2.mem_iff] using hz.1
      exact hw.elim (fun h => Or.inl (congrArg Sum.inl h))
        (fun h => Or.inr (congrArg Sum.inl h))
  have hs := adjacent p.snd (p.adj_snd hp.not_nil)
  have ht := adjacent p.penultimate (p.adj_penultimate hp.not_nil).symm
  by_contra hv
  have hsMem : p.snd ∈ cycle.walk.support := by
    apply (cycle.walk.mem_support_rotate_iff (Sum.inr f) hf).mp
    exact List.mem_of_mem_tail (p.snd_mem_tail_support hp.not_nil)
  have htMem : p.penultimate ∈ cycle.walk.support := by
    apply (cycle.walk.mem_support_rotate_iff (Sum.inr f) hf).mp
    exact List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp.not_nil)
  have hs' : p.snd = Sum.inl u := hs.resolve_right (by intro h; exact hv (h ▸ hsMem))
  have ht' : p.penultimate = Sum.inl u := ht.resolve_right (by intro h; exact hv (h ▸ htMem))
  exact hp.snd_ne_penultimate (hs'.trans ht'.symm)

private theorem helper_cycleMissing_343.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (u : V), a ∈ MissingColors G psi u ∨ b ∈ MissingColors G psi u → ((TwoColorIncidenceGraph G
        psi a b).neighborSet (Sum.inl u)).Subsingleton) →
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (cycle : TwoColorCycle G psi a b) (v : V), Sum.inl v ∈ cycle.walk.support → a ∈
        MissingColors G psi v ∨ b ∈ MissingColors G psi v → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero leaf psi a b hp cycle v hv hm
  let p := cycle.walk.rotate (Sum.inl v) hv
  have hcy : p.IsCycle := cycle.isCycle.rotate hv
  exact hcy.snd_ne_penultimate
    (leaf psi a b hp v hm (p.adj_snd hcy.not_nil)
      (p.adj_penultimate hcy.not_nil).symm)

private theorem helper_outsideCommon_352.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base), (
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card) → C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length); y ∉ TreeSequenceVertexSet A → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (u : V), a ∈ MissingColors G psi u ∨ b ∈ MissingColors G psi u → ((TwoColorIncidenceGraph G
        psi a b).neighborSet (Sum.inl u)).Subsingleton) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V), Sum.inl u ∈ TwoColorComponent G psi a
        b (Sum.inl u)) →
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
        TreeInterchangeable G A psi a b → a ∈ TreeMissingColors psi A → b ∈ TreeMissingColors psi
        A → a ∈ MissingColors G psi y ∨ b ∈ MissingColors G psi y →
    ∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ TwoColorComponent G psi a b (Sum.inl y) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C _ hzero A y hyNot leaf selfMem psi a b hab hp
      hi ha hb hym
  let I := TwoColorIncidenceGraph G psi a b
  obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hb
  have huPath : TwoColorPathComponent G psi a b (Sum.inl u) :=
    ⟨hab, Sum.inl u, selfMem psi a b u, leaf psi a b hp u (Or.inl hum)⟩
  have hwPath : TwoColorPathComponent G psi a b (Sum.inl w) :=
    ⟨hab, Sum.inl w, selfMem psi a b w, leaf psi a b hp w (Or.inr hwm)⟩
  have hyPath : TwoColorPathComponent G psi a b (Sum.inl y) :=
    ⟨hab, Sum.inl y, selfMem psi a b y, leaf psi a b hp y hym⟩
  have huw := hi _ _ huPath hwPath
    ⟨u, hu, selfMem psi a b u⟩ ⟨w, hw, selfMem psi a b w⟩
  intro v hv hvC
  have hyu := hi _ _ hyPath huPath ⟨v, hv, hvC⟩ ⟨u, hu, selfMem psi a b u⟩
  have hyC : Sum.inl y ∈ TwoColorComponent G psi a b (Sum.inl u) := by
    rw [← hyu]
    exact selfMem psi a b y
  by_cases heq : u = w
  · have hbU : b ∈ MissingColors G psi u := by simpa only [heq] using hwm
    have hempty : I.neighborSet (Sum.inl u) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      cases z with
      | inl z => simp [I, TwoColorIncidenceGraph] at hz
      | inr e =>
        have he : Incident G u e ∧ (psi e = some a ∨ psi e = some b) := hz
        have hna : a ∉ PresentColors G psi u := by simpa [MissingColors] using hum
        have hnb : b ∉ PresentColors G psi u := by simpa [MissingColors] using hbU
        rcases he.2 with hec | hec
        · exact hna (by simpa [PresentColors] using
            (show ∃ e, Incident G u e ∧ psi e = some a from ⟨e, he.1, hec⟩))
        · exact hnb (by simpa [PresentColors] using
            (show ∃ e, Incident G u e ∧ psi e = some b from ⟨e, he.1, hec⟩))
    have hreach : I.Reachable (Sum.inl y) (Sum.inl u) :=
      SimpleGraph.ConnectedComponent.exact hyC
    exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
      (by intro he; exact hyNot (by simpa only [Sum.inl.inj he] using hu)) hempty hreach
  · obtain ⟨s, t, p, hpPath, hsupp⟩ :=
      TwoColorComponentSpanningPath G psi a b hp (Sum.inl u)
    have endpoint (r : V)
        (hr : Sum.inl r ∈ TwoColorComponent G psi a b (Sum.inl u))
        (hm : a ∈ MissingColors G psi r ∨ b ∈ MissingColors G psi r) :
        Sum.inl r = s ∨ Sum.inl r = t := by
      have hrp : Sum.inl r ∈ p.support := by
        change Sum.inl r ∈ {x | x ∈ p.support}
        rw [hsupp]
        exact hr
      by_contra hn
      push Not at hn
      exact (hpPath.isTrail.notMem_support_of_subsingleton_neighborSet
        hn.1 hn.2 (leaf psi a b hp r hm)) hrp
    have huend := endpoint u (selfMem psi a b u) (Or.inl hum)
    have hwend := endpoint w (by rw [huw]; exact selfMem psi a b w) (Or.inr hwm)
    have hyend := endpoint y hyC hym
    have hyu : y ≠ u := by rintro rfl; exact hyNot hu
    have hyw : y ≠ w := by rintro rfl; exact hyNot hw
    rcases huend with hus | hut <;> rcases hwend with hws | hwt <;>
      rcases hyend with hys | hyt
    all_goals first
      | exact heq (Sum.inl.inj (hus.trans hws.symm))
      | exact heq (Sum.inl.inj (hut.trans hwt.symm))
      | exact hyu (Sum.inl.inj (hys.trans hus.symm))
      | exact hyu (Sum.inl.inj (hyt.trans hut.symm))
      | exact hyw (Sum.inl.inj (hys.trans hws.symm))
      | exact hyw (Sum.inl.inj (hyt.trans hwt.symm))

private theorem helper_hfixed_432.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (a b : Fin k), (
    ∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ TwoColorComponent G phi a b (Sum.inl y)) →
    ∀ (f : E), TreeIncidentEdge A f → TwoColorComponentSwap G phi a b (Sum.inl y) f = phi f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y a b havoid f hf
  obtain ⟨v, hv, hvf⟩ := hf
  by_cases he : Sum.inr f ∈ TwoColorComponent G phi a b (Sum.inl y)
  · by_cases hc : phi f = some a ∨ phi f = some b
    · have hadj : (TwoColorIncidenceGraph G phi a b).Adj (Sum.inl v) (Sum.inr f) :=
        ⟨hvf, hc⟩
      have hc' := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hvC : Sum.inl v ∈ TwoColorComponent G phi a b (Sum.inl y) :=
        hc'.trans he
      exact (havoid v hv hvC).elim
    · simp only [not_or] at hc
      simp [TwoColorComponentSwap, he, hc.1, hc.2]
  · simp [TwoColorComponentSwap, he]

private theorem helper_branch_448.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        IsOneEdgeUncolored phi e0 → C.hierarchy.dividerCount = (0 : ℕ) →
    let y : V := T.vertex (Fin.last T.length);
    ∀ (a b : Fin k), a ≠ b → IsOneEdgeUncolored (TwoColorComponentSwap G phi a b (Sum.inl y)) e0
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone hzero y a b hab
  have hnone (f : E) : TwoColorComponentSwap G phi a b (Sum.inl y) f = none ↔ phi f = none := by
    by_cases hc : Sum.inr f ∈ TwoColorComponent G phi a b (Sum.inl y)
    · by_cases ha : phi f = some a
      · simp [TwoColorComponentSwap, hc, ha]
      · by_cases hb : phi f = some b
        · simp [TwoColorComponentSwap, hc, hb, Ne.symm hab]
        · simp [TwoColorComponentSwap, hc, ha, hb]
    · simp [TwoColorComponentSwap, hc]
  constructor
  · exact (hnone e0).mpr hone.1
  · intro f hfe
    obtain ⟨c, hc⟩ := hone.2 f hfe
    cases hs : TwoColorComponentSwap G phi a b (Sum.inl y) f with
    | none =>
      exfalso
      have hn : phi f ≠ none := by rw [hc]; simp
      exact hn ((hnone f).mp hs)
    | some d => exact ⟨d, rfl⟩

private theorem helper_hTnFinal_763.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds), TashkinovClosure (ett.series.data.coloring i.succ)
        (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ) →
        (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length
        → n = i.succ → TashkinovAugmentationSequence phi Tn (ett.series.data.tree (Fin.last
        (ett.rounds + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero n Tn i closedExtension strictExtension hslot
  have hphi : phi = ett.series.data.coloring i.succ := by
    simpa only [n, hslot] using ett.generatingColoring
  have hfinal : i.succ.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    have hh := congrArg Fin.val hslot
    simp only [n, Fin.val_last, Fin.val_succ] at hh ⊢
    omega
  simpa only [Tn, hslot, hfinal, ← hphi] using closedExtension.1

private theorem helper_hstep_780.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core; T.length = A.length + (1 : ℕ) → (
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y) →
    ∀ (i : Fin ett.rounds), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length → TashkinovAugmentationSequence phi A T → TashkinovAugmentation phi A
        T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A hlen equalTrees i strictExtension hrouteA
  have oneStep (X : TreeSequence G e0) (hXT : TashkinovAugmentationSequence phi X T) :
      T.length = X.length + 1 → TashkinovAugmentation phi X T := by
    unfold TashkinovAugmentationSequence at hXT
    induction hXT using Relation.ReflTransGen.head_induction_on with
    | refl => intro h; omega
    | @head X B hXB hBT ih =>
      intro h
      have hBTseg := TashkinovAugmentationSequenceInitialSegment phi B T hBT
      have hBlen : B.length = T.length := by
        have := hXB.1
        have := hBTseg.1
        omega
      have hB := equalTrees hBTseg hBlen
      subst B
      exact hXB
  exact oneStep A hrouteA hlen

private theorem helper_hfy_804.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hlen : T.length = A.length + (1 : ℕ)) (i : Fin ett.rounds), (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → T.length = A.length
        + (1 : ℕ) →
    let f : E := T.edge (⟨A.length,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            omega
    ⟩ : Fin T.length); Incident G y f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hlen i strictExtension hstepLen f
  obtain ⟨j, hj⟩ := T.attaches ⟨A.length, by omega⟩
  change y ∈ G.ends f
  rw [hj]
  have hi : (⟨A.length, by omega⟩ : Fin T.length).succ = Fin.last T.length := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  simp [hi, y]

private theorem helper_stableOn_862.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (alpha : Fin k) (i : Fin ett.rounds), (ett.series.data.tree i.succ.castSucc).length <
        (ett.series.data.tree i.succ.succ).length → T.length = A.length + (1 : ℕ) →
    ∀ (theta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha (Sum.inl y); (
    ∀ (f : E), TreeIncidentEdge A f → TwoColorComponentSwap G phi theta alpha (Sum.inl y) f = phi
        f) → (
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G (TwoColorComponentSwap G phi theta alpha
        (Sum.inl y)) v = MissingColors G phi v) →
    ∀ (X : TreeSequence G e0) (D : Finset (Fin k)), TreeSequenceVertexSet X ⊆
        TreeSequenceVertexSet A → StableColoring X D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y alpha i strictExtension hstepLen
      theta sigma hfixed hmissing X D hX
  constructor
  · intro e he hc
    obtain ⟨v, hv, hve⟩ := he
    exact hfixed e ⟨v, hX hv, hve⟩
  · intro v hv
    exact hmissing v (hX hv)

private theorem helper_huA_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hlen : T.length = A.length + (1 : ℕ)), (
    ∀ {v : V}, v ∈ TreeSequenceVertexSet T → v ≠ y → v ∈ TreeSequenceVertexSet A) →
    ∀ (i : Fin ett.rounds), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length → T.length = A.length + (1 : ℕ) →
    ∀ (j : Fin ((↑(⟨A.length,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have := GoldbergSeymour.TreeSequence.positive A
                    omega
    ⟩ : Fin T.length) : ℕ) + (1 : ℕ))),
    let u : V := T.vertex (j.castLT (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            omega
    )); u ∈ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero A y hlen prefixMem i strictExtension
      hstepLen j u
  apply prefixMem
  · exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro huy
    have hidx := congrArg Fin.val (T.vertex_injective huy)
    have hjLt := j.isLt
    simp only [Fin.val_castLT, Fin.val_last] at hidx
    omega

private theorem helper_branch_931.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → C.hierarchy.dividerCount = (0 :
        ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let y : V := T.vertex (Fin.last T.length); H.stage (⟨(1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = T →
    ∀ (hlen : T.length = A.length + (1 : ℕ)),
    ∀ alpha ∈ TreeMissingColors phi A, alpha ∈ MissingColors G phi y → (
    ∀ (f : E) (u v : V), u ∈ TreeSequenceVertexSet A → v ∉ TreeSequenceVertexSet A → G.ends f =
        s(u, v) → T.edge (⟨A.length,
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive A
                        omega
    ⟩ : Fin T.length) = f → y = v) →
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data i.castSucc) : Finset (Fin k)) choice.selected pi →
        Disjoint (MissingColors G pi choice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree i.succ.castSucc))) → ett.series.data.coloring i.succ =
        choice.selected → ett.series.data.connectingEdges i.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind i.succ = some TashkinovExtensionKind.SE → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → n = i.succ → False
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hzero H A n Tn y hfirst hlen alpha
      hAlphaA hAlphaY outsideEndpoint i choice seriesAlternative currentColoring currentEdges
      currentKind strictExtension hslot
  have hkind : ett.series.data.kind n = some TashkinovExtensionKind.SE := by
    rw [hslot]
    exact currentKind
  have hcore : A = Tn := base.nonparallel (by rw [hkind]; decide)
  have hphi : phi = choice.selected := ett.generatingColoring.trans
    (by change ett.series.data.coloring n = choice.selected
        rw [hslot]; exact currentColoring)
  have hedges : ett.series.data.connectingEdges n = {choice.edge} := by
    rw [hslot]
    exact currentEdges
  obtain ⟨r, hr, hedge⟩ := HierarchyNonparallelFirstEdge H choice.edge
    (Or.inl hkind) hedges
  have hedgeT : T.edge ⟨A.length, by omega⟩ = choice.edge := by
    have hcore' : A = ett.series.data.tree (Fin.last ett.rounds).castSucc := hcore
    have hr' : r.val = A.length := by simpa only [← hcore'] using hr
    have hentry : ∃ s : Fin T.length, s.val = A.length ∧ T.edge s = choice.edge := by
      have hh : ∃ s : Fin (H.stage ⟨1, by omega⟩).length, s.val = A.length ∧
          (H.stage ⟨1, by omega⟩).edge s = choice.edge := ⟨r, hr', hedge⟩
      rw [hfirst] at hh
      exact hh
    obtain ⟨s, hs, he⟩ := hentry
    have hs' : s = ⟨A.length, by omega⟩ := Fin.ext hs
    simpa only [hs'] using he
  have htree : A = ett.series.data.tree i.succ.castSucc := by
    simpa only [Tn, hslot] using hcore
  have hy : y = choice.otherEndpoint := outsideEndpoint choice.edge
    choice.vertex choice.otherEndpoint
    (by rw [htree]; exact choice.vertexDefective.1)
    (by rw [htree]; exact choice.otherOutside) choice.edgeEnds hedgeT
  have hstable : StableColoring (ett.series.data.tree i.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc))
      choice.selected phi := by
    exact ⟨fun f _ _ => congrArg (fun psi => psi f) hphi,
      fun v _ => congrArg (fun psi => MissingColors G psi v) hphi⟩
  have hdisjoint := seriesAlternative phi hproper hone hstable
  exact Finset.disjoint_left.mp hdisjoint
    (by simpa only [hy] using hAlphaY) (by simpa only [htree] using hAlphaA)

private theorem helper_hedgeT_992.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; H.stage (⟨(1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = T →
    ∀ (hlen : T.length = A.length + (1 : ℕ)) (i : Fin ett.rounds) (available :
        RevisitingExtensionCertificate ett.series.data i.castSucc), (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → A = Tn →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).edge r = available.edge → T.edge (⟨A.length,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            omega
    ⟩ : Fin T.length) = available.edge := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H A n Tn hfirst hlen i available
      strictExtension hcore r hr hedge
  have hcore' : A = ett.series.data.tree (Fin.last ett.rounds).castSucc := hcore
  have hr' : r.val = A.length := by simpa only [← hcore'] using hr
  obtain ⟨s, hs, he⟩ : ∃ s : Fin T.length,
      s.val = A.length ∧ T.edge s = available.edge := by
    have hh : ∃ s : Fin (H.stage ⟨1, by omega⟩).length, s.val = A.length ∧
        (H.stage ⟨1, by omega⟩).edge s = available.edge := ⟨r, hr', hedge⟩
    rw [hfirst] at hh
    exact hh
  simpa only [show s = ⟨A.length, by omega⟩ from Fin.ext hs] using he

private theorem helper_hstart_1006.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy; (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V), Sum.inl u ∈ TwoColorComponent G psi a
        b (Sum.inl u)) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
        i.castSucc), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → available.delta ∈ TreeMissingColors
        (ett.series.data.coloring available.earlier) (ett.series.data.tree available.earlier.succ)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H selfMem i available strictExtension r hr
  have hkind := available.earlierPE
  have hd := available.earlierDelta
  have certH := ett.series.certified available.earlier
  generalize hh : available.earlier = h at certH
  cases certH with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    rw [hh, initialKind] at hkind
    simp at hkind
  | SE j pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
    rw [hh, ck] at hkind
    simp at hkind
  | RE j pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
    rw [hh, ck] at hkind
    simp at hkind
  | PE j pp po pc pn nr choice alt gamma gr second sp so sr ew
      cc cp cu cs ce ck cv co cd cg cl oe st =>
    have hdelta : choice.color = available.delta := by
      rw [hh, cd] at hd
      exact Option.some.inj hd
    have hgammaMissing : gamma ∈ MissingColors G second choice.vertex := by
      rw [sr.2 choice.vertex choice.vertexDefective.1]
      exact gr.1
    have hchoiceColor : second choice.edge = some choice.color :=
      (sr.1 choice.edge ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
          choice.edgeColor⟩).trans choice.edgeColor
    have hne : gamma ≠ choice.color := by
      intro heq
      have hn : gamma ∉ PresentColors G second choice.vertex := by
        simpa [MissingColors] using hgammaMissing
      apply hn
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, by simpa only [heq] using hchoiceColor⟩
    have hm := (TwoColorComponentSwapMissingBehavior G second gamma choice.color hne sp
      (Sum.inl choice.vertex)).2.1 choice.vertex (selfMem second gamma choice.color choice.vertex)
        hgammaMissing
    rw [cc]
    apply Finset.mem_biUnion.mpr
    refine ⟨choice.vertex, TreeSequenceInitialSegmentVertexSetSubset oe
      choice.vertexDefective.1, ?_⟩
    simpa only [hdelta] using hm

private theorem helper_transport_1051.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
        i.castSucc), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → available.delta ∈ TreeMissingColors
        (ett.series.data.coloring available.earlier) (ett.series.data.tree available.earlier.succ)
        →
    ∀ (m : ℕ), (↑available.earlier : ℕ) ≤ m → m ≤ (↑i : ℕ) →
    ∀ (j : Fin (ett.rounds + (1 : ℕ))), (↑j : ℕ) = m → available.delta ∈ TreeMissingColors
        (ett.series.data.coloring j) (ett.series.data.tree j.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H i available strictExtension r hr hstart
      m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hmi j hj
    have heq : j = available.earlier := Fin.ext hj
    simpa only [heq] using hstart
  | succ m hm ih =>
    intro hmi j hj
    let p : Fin (ett.rounds + 1) := ⟨m, by have := i.isLt; omega⟩
    have hprev := ih (by omega) p rfl
    have hjkind := available.interveningRevisiting j (by omega) (by omega) (by
      change j.val ≤ i.val
      omega)
    have certJ := ett.series.certified j
    generalize hjSlot : j = js at certJ
    cases certJ with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [hjSlot, initialKind] at hjkind
      simp at hjkind
    | SE q pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
      rw [hjSlot, ck] at hjkind
      simp at hjkind
    | PE q pp po pc pn nr choice alt gamma gr second sp so sr ew
        cc cp cu cs ce ck cv co cd cg cl oe st =>
      rw [hjSlot, ck] at hjkind
      simp at hjkind
    | RE q pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
      have hqp : q.castSucc = p := by
        apply Fin.ext
        have hh := congrArg Fin.val hjSlot
        simp only [Fin.val_succ] at hh
        dsimp [p]
        omega
      have hqpTree : p.succ = q.succ.castSucc := by
        apply Fin.ext
        have := congrArg Fin.val hqp
        simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
        omega
      rw [cc]
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hprev
      apply Finset.mem_biUnion.mpr
      refine ⟨v, TreeSequenceInitialSegmentVertexSetSubset oe
        (by simpa only [hqpTree] using hv), ?_⟩
      simpa only [hqp] using hvm

private theorem helper_hcycleY_1104.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hlen : T.length = A.length + (1 : ℕ)), (
    ∀ (f : E) (u v : V), u ∈ TreeSequenceVertexSet A → v ∉ TreeSequenceVertexSet A → G.ends f =
        s(u, v) → T.edge (⟨A.length,
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive A
                        omega
    ⟩ : Fin T.length) = f → y = v) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (cycle : TwoColorCycle G psi a b) (f : E) (u v
        : V), G.ends f = s(u, v) → Sum.inr f ∈ cycle.walk.support → Sum.inl v ∈
        cycle.walk.support) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
        i.castSucc), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → y = available.outsideEndpoint → Sum.inl y ∈
        available.cycle.walk.support := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H A y hlen outsideEndpoint cycleEndpoint
      i available strictExtension r hr hy
  have hy' := cycleEndpoint (ett.series.data.coloring i.castSucc)
    available.gamma available.delta available.cycle available.edge
    available.insideEndpoint available.outsideEndpoint available.edgeEnds
    available.edgeOnCycle
  simpa only [hy] using hy'

private theorem helper_hclosed_1114.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    ∀ (i : Fin ett.rounds), ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → phi =
        ett.series.data.coloring i.castSucc → A = ett.series.data.tree i.succ.castSucc →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → ColoredVertexSetClosed G phi (TreeSequenceVertexSet A) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H A i previousClosed strictExtension hphi
      htree r hr f c v hf hv hfc hm
  have hf' : f ∈ BoundaryEdges G
      (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
    simpa only [htree] using hf
  have hv' : v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) := by
    simpa only [htree] using hv
  exact previousClosed hf' hv' (by simpa only [hphi] using hfc)
    (by simpa only [hphi] using hm)

private theorem helper_branch_1178.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hlen : T.length = A.length + (1 : ℕ)) (alpha : Fin k), (
    ∀ (f : E) (u v : V), u ∈ TreeSequenceVertexSet A → v ∉ TreeSequenceVertexSet A → G.ends f =
        s(u, v) → T.edge (⟨A.length,
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive A
                        omega
    ⟩ : Fin T.length) = f → y = v) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (cycle : TwoColorCycle G psi a b) (f : E) (u v
        : V), G.ends f = s(u, v) → Sum.inr f ∈ cycle.walk.support → Sum.inl v ∈
        cycle.walk.support) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (cycle : TwoColorCycle G psi a b) (v : V), Sum.inl v ∈ cycle.walk.support → a ∈
        MissingColors G psi v ∨ b ∈ MissingColors G psi v → False) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
        i.castSucc), (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length →
    ∀ (r : Fin (H.stage (⟨(1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length), (↑r : ℕ) = (ett.series.data.tree (Fin.last
        ett.rounds).castSucc).length → y = available.outsideEndpoint →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi available.delta alpha
        (Sum.inl y); available.delta ∈ MissingColors G sigma y →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
        corr.replacementSeries.data.connectingEdges n = ({ available.edge } : Finset E) →
        available.delta ∈ corr.replacementSeries.data.stored n →
    ∀ (q : Fin ett.rounds), IsProperEdgeColoring G (corr.replacementSeries.data.coloring
        q.castSucc) →
    ∀ (av : RevisitingExtensionCertificate corr.replacementSeries.data q.castSucc),
        corr.replacementSeries.data.coloring q.succ = corr.replacementSeries.data.coloring
        q.castSucc → corr.replacementSeries.data.stored q.succ = (insert av.delta ({ av.gamma } :
        Finset (Fin k)) : Finset (Fin k)) → corr.replacementSeries.data.connectingEdges q.succ =
        ({ av.edge } : Finset E) → (corr.replacementSeries.data.tree q.succ.castSucc).length <
        (corr.replacementSeries.data.tree q.succ.succ).length → n = q.succ → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hzero H A n y hlen alpha outsideEndpoint
      cycleEndpoint cycleMissing i available strictExtension r hr hy sigma hDeltaY corr hRepEdges
      hRepDelta q pp av cc cs ce st hRepSlot
  have hf : av.edge = available.edge := by
    have hh : av.edge ∈ corr.replacementSeries.data.connectingEdges n := by
      rw [hRepSlot, ce]
      simp
    rw [hRepEdges] at hh
    exact Finset.mem_singleton.mp hh
  have hcolor : sigma = corr.replacementSeries.data.coloring q.castSucc :=
    corr.finalGeneratingColoring.trans (by
      change corr.replacementSeries.data.coloring n =
        corr.replacementSeries.data.coloring q.castSucc
      rw [hRepSlot]; exact cc)
  have hcyEdge : Sum.inr available.edge ∈ av.cycle.walk.support := by
    simpa only [hf] using av.edgeOnCycle
  have hcyY : Sum.inl y ∈ av.cycle.walk.support := by
    have hh := cycleEndpoint (corr.replacementSeries.data.coloring q.castSucc)
      av.gamma av.delta av.cycle available.edge
      available.insideEndpoint available.outsideEndpoint available.edgeEnds hcyEdge
    simpa only [hy] using hh
  rw [hRepSlot, cs] at hRepDelta
  have hpair : available.delta = av.delta ∨ available.delta = av.gamma := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hRepDelta
  apply cycleMissing (corr.replacementSeries.data.coloring q.castSucc)
    av.gamma av.delta pp av.cycle y hcyY
  rcases hpair with hd | hg
  · exact Or.inr (by simpa only [← hd, hcolor] using hDeltaY)
  · exact Or.inl (by simpa only [← hg, hcolor] using hDeltaY)

private theorem helper_branch_1205.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → LowerRoundInductionHypothesis G k
        e0 ett.rounds → C.hierarchy.dividerCount = (0 : ℕ) →
    let _ : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let y : V := T.vertex (Fin.last T.length); TreeSequenceInitialSegment A T → T.length =
        A.length + (1 : ℕ) → (
    ∀ {v : V}, v ∈ TreeSequenceVertexSet T → v ≠ y → v ∈ TreeSequenceVertexSet A) →
    ∀ alpha ∈ TreeMissingColors phi A, alpha ∈ MissingColors G phi y → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V), Sum.inl u ∈ TwoColorComponent G psi a
        b (Sum.inl u)) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
        TreeInterchangeable G A psi a b → a ∈ TreeMissingColors psi A → b ∈ TreeMissingColors psi
        A → a ∈ MissingColors G psi y ∨ b ∈ MissingColors G psi y →
    ∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ TwoColorComponent G psi a b (Sum.inl y)) → (
    ∀ (a b : Fin k), a ≠ b → (
    ∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ TwoColorComponent G phi a b (Sum.inl y)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi a b (Sum.inl y);
        IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧ (
    ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) ∧
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (i : Fin ett.rounds) (_ : Fin k), ett.series.data.kind i.succ = some
        TashkinovExtensionKind.PE → TashkinovClosure (ett.series.data.coloring i.succ)
        (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ) →
        (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length
        → n = i.succ → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hzero H A n Tn y hAT hlen
      prefixMem alpha hAlphaA hAlphaY commonPrefix equalTrees selfMem outsideCommon outsideSwap i
      gamma currentKind closedExtension strictExtension hslot
  have hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
    rw [hslot]
    exact currentKind
  obtain ⟨union⟩ := (base.parallel hPE).2.2
  have hTnA : TreeSequenceInitialSegment Tn A := union.leftSegment
  have hTnFinal : TashkinovAugmentationSequence phi Tn
      (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
    exact @helper_hTnFinal_763 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@i) (@closedExtension)
        (@strictExtension) (@hslot)
  have hTnT : TreeSequenceInitialSegment Tn T :=
    commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hTnFinal)
      ett.belowFinal (le_trans hTnA.1 hAT.1)
  have hrouteT : TashkinovAugmentationSequence phi Tn T :=
    TashkinovAugmentationSequenceRestrict phi _ _ _ hTnFinal hTnT ett.belowFinal
  have hrouteA : TashkinovAugmentationSequence phi A T :=
    TashkinovAugmentationSequenceSuffix phi _ _ _ hrouteT hTnA hAT
  have hstep : TashkinovAugmentation phi A T := by
    exact @helper_hstep_780 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen) (@equalTrees)
        (@i) (@strictExtension) (@hrouteA)
  obtain ⟨hstepLen, hstepSegment, beta, hBetaEdge, hBetaA⟩ := hstep
  let f := T.edge ⟨A.length, by omega⟩
  have hBetaF : phi f = some beta := by
    convert hBetaEdge using 2
    apply congrArg T.edge
    apply Fin.ext
    rfl
  have hfy : Incident G y f := by
    exact @helper_hfy_804 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen) (@i)
        (@strictExtension) (@hstepLen)
  have hAlphaBeta : alpha ≠ beta := by
    intro heq
    have hn : alpha ∉ PresentColors G phi y := by simpa [MissingColors] using hAlphaY
    exact hn (by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, hfy, by simpa only [heq] using hBetaF⟩)
  let M := ((TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) \
    (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0))
  have hMcard : 4 ≤ M.card := (C.good.parallelBase hPE).2
  obtain ⟨theta, htM, htAvoid⟩ : ∃ theta ∈ M, theta ∉ ({alpha, beta} : Finset (Fin k)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have habcard : ({alpha, beta} : Finset (Fin k)).card ≤ 2 := by
      calc
        ({alpha, beta} : Finset (Fin k)).card ≤ ({beta} : Finset (Fin k)).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  have hThetaAlpha : theta ≠ alpha := by intro he; exact htAvoid (by simp [he])
  have hThetaBeta : theta ≠ beta := by intro he; exact htAvoid (by simp [he])
  have hThetaTn : theta ∈ TreeMissingColors phi Tn :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp htM).1).1
  have hThetaR : theta ∈ TreeMissingColors phi base.closure :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp htM).1).2
  have hThetaA : theta ∈ TreeMissingColors phi A := by
    obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaTn
    exact Finset.mem_biUnion.mpr
      ⟨u, TreeSequenceInitialSegmentVertexSetSubset hTnA hu, hum⟩
  have hstablePhi : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi phi :=
    ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl⟩,
      ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩
  have hThetaClosed := InterchangePECommonMissingClosed G k e0 input T phi phi
    ett C.maximum C.positive hlower hPE base hproper hone hstablePhi theta hThetaTn hThetaR
  have hInter := (interchange G k e0 input T phi phi ett C.maximum C.positive
    hlower hPE base hproper hone hstablePhi theta alpha).2.2.1 hThetaA hThetaClosed
  have havoid := outsideCommon phi theta alpha hThetaAlpha hproper
    hInter hThetaA hAlphaA (Or.inr hAlphaY)
  let sigma := TwoColorComponentSwap G phi theta alpha (Sum.inl y)
  obtain ⟨hsigmaProper, hsigmaOne, hfixed, hmissing⟩ :=
    outsideSwap theta alpha hThetaAlpha havoid
  have hThetaY : theta ∈ MissingColors G sigma y :=
    (TwoColorComponentSwapMissingBehavior G phi theta alpha hThetaAlpha
      hproper (Sum.inl y)).2.2.1 y (selfMem phi theta alpha y) hAlphaY
  have hmissingA : TreeMissingColors sigma A = TreeMissingColors phi A := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hmissing v hv
  have hRsub : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
    rw [union.vertexSet]
    exact Finset.subset_union_right
  have stableOn (X : TreeSequence G e0) (D : Finset (Fin k))
      (hX : TreeSequenceVertexSet X ⊆ TreeSequenceVertexSet A) :
      StableColoring X D phi sigma := by
    exact @helper_stableOn_862 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@alpha) (@i)
        (@strictExtension) (@hstepLen) (@theta) (@hfixed) (@hmissing) (@X) (@D) (@hX)
  have hsigmaStable : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi sigma :=
    ⟨stableOn Tn _ (TreeSequenceInitialSegmentVertexSetSubset hTnA),
      stableOn base.closure ∅ hRsub⟩
  have hThetaTnSigma : theta ∈ TreeMissingColors sigma Tn := by
    obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaTn
    exact Finset.mem_biUnion.mpr ⟨u, hu, by
      rw [hsigmaStable.1.2 u hu]; exact hum⟩
  have hThetaRSigma : theta ∈ TreeMissingColors sigma base.closure := by
    obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaR
    exact Finset.mem_biUnion.mpr ⟨u, hu, by
      rw [hsigmaStable.2.2 u hu]; exact hum⟩
  have hThetaClosedSigma := InterchangePECommonMissingClosed G k e0 input T phi sigma
    ett C.maximum C.positive hlower hPE base hsigmaProper hsigmaOne hsigmaStable
    theta hThetaTnSigma hThetaRSigma
  have hThetaASigma : theta ∈ TreeMissingColors sigma A := by rwa [hmissingA]
  have hBetaASigma : beta ∈ TreeMissingColors sigma A := by rwa [hmissingA]
  have hInterSigma := (interchange G k e0 input T phi sigma ett C.maximum C.positive
    hlower hPE base hsigmaProper hsigmaOne hsigmaStable theta beta).2.2.1
    hThetaASigma hThetaClosedSigma
  have havoidSigma := outsideCommon sigma theta beta hThetaBeta hsigmaProper
    hInterSigma hThetaASigma hBetaASigma (Or.inl hThetaY)
  obtain ⟨j, hj⟩ := T.attaches ⟨A.length, by omega⟩
  let u := T.vertex (Fin.castLT j (Nat.lt_trans j.isLt
    (Nat.succ_lt_succ (show A.length < T.length by omega))))
  have huA : u ∈ TreeSequenceVertexSet A := by
    exact @helper_huA_896 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen) (@prefixMem) (@i)
        (@strictExtension) (@hstepLen) (@j)
  have huf : Incident G u f := by
    change u ∈ G.ends f
    rw [hj]
    exact Sym2.mem_mk_right _ _
  have hSigmaF : sigma f = some beta :=
    (hfixed f ⟨u, huA, huf⟩).trans hBetaF
  have hyAdj : (TwoColorIncidenceGraph G sigma theta beta).Adj (Sum.inl y) (Sum.inr f) :=
    ⟨hfy, Or.inr hSigmaF⟩
  have huAdj : (TwoColorIncidenceGraph G sigma theta beta).Adj (Sum.inl u) (Sum.inr f) :=
    ⟨huf, Or.inr hSigmaF⟩
  have huC : Sum.inl u ∈ TwoColorComponent G sigma theta beta (Sum.inl y) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huAdj).trans
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyAdj).symm
  exact havoidSigma u huA huC

private theorem helper_branch_1573.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → LowerRoundInductionHypothesis G k e0 ett.rounds →
        C.hierarchy.dividerCount = (0 : ℕ) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := base.core;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let y : V := T.vertex (Fin.last T.length); H.stage (⟨(1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = T → TreeSequenceInitialSegment A T →
    ∀ (hlen : T.length = A.length + (1 : ℕ)), y ∉ TreeSequenceVertexSet A →
    ∀ alpha ∈ TreeMissingColors phi A, alpha ∈ MissingColors G phi y → (
    ∀ (f : E) (u v : V), u ∈ TreeSequenceVertexSet A → v ∉ TreeSequenceVertexSet A → G.ends f =
        s(u, v) → T.edge (⟨A.length,
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive A
                        omega
    ⟩ : Fin T.length) = f → y = v) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V), Sum.inl u ∈ TwoColorComponent G psi a
        b (Sum.inl u)) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (cycle : TwoColorCycle G psi a b) (f : E) (u v
        : V), G.ends f = s(u, v) → Sum.inr f ∈ cycle.walk.support → Sum.inl v ∈
        cycle.walk.support) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), IsProperEdgeColoring G psi →
    ∀ (cycle : TwoColorCycle G psi a b) (v : V), Sum.inl v ∈ cycle.walk.support → a ∈
        MissingColors G psi v ∨ b ∈ MissingColors G psi v → False) → (
    ∀ (a b : Fin k), a ≠ b → (
    ∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ TwoColorComponent G phi a b (Sum.inl y)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi a b (Sum.inl y);
        IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧ (
    ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) ∧
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (i : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) →
        ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate ett.series.data i.castSucc),
        ett.series.data.coloring i.succ = ett.series.data.coloring i.castSucc →
        ett.series.data.stored i.succ = (insert available.delta ({ available.gamma } : Finset (Fin
        k)) : Finset (Fin k)) → ett.series.data.connectingEdges i.succ = ({ available.edge } :
        Finset E) → ett.series.data.kind i.succ = some TashkinovExtensionKind.RE →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) available.edge adjoined → TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → n = i.succ → False
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hlower hzero H A n Tn y hfirst hAT hlen
      hyNot alpha hAlphaA hAlphaY outsideEndpoint commonPrefix equalTrees selfMem cycleEndpoint
      cycleMissing outsideSwap i previousProper previousClosed available currentColoring
      currentStored currentEdges currentKind adjoined adjoinedExactly closedExtension
      strictExtension hslot
  have hRE : ett.series.data.kind n = some TashkinovExtensionKind.RE := by
    rw [hslot]
    exact currentKind
  have hcore : A = Tn := base.nonparallel (by rw [hRE]; decide)
  have hphi : phi = ett.series.data.coloring i.castSucc :=
    ett.generatingColoring.trans (by
      change ett.series.data.coloring n = ett.series.data.coloring i.castSucc
      rw [hslot]; exact currentColoring)
  have htree : A = ett.series.data.tree i.succ.castSucc := by
    simpa only [Tn, hslot] using hcore
  have hedges : ett.series.data.connectingEdges n = {available.edge} := by
    rw [hslot]
    exact currentEdges
  obtain ⟨r, hr, hedge⟩ := HierarchyNonparallelFirstEdge H available.edge
    (Or.inr hRE) hedges
  have hedgeT : T.edge ⟨A.length, by omega⟩ = available.edge := by
    exact @helper_hedgeT_992 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hfirst) (@hlen) (@i)
        (@available) (@strictExtension) (@hcore) (@r) (@hr) (@hedge)
  have hy : y = available.outsideEndpoint := outsideEndpoint available.edge
    available.insideEndpoint available.outsideEndpoint
    (by rw [htree]; exact available.insideInCurrent)
    (by rw [htree]; exact available.outsideNotCurrent) available.edgeEnds hedgeT
  have hstart : available.delta ∈ TreeMissingColors
      (ett.series.data.coloring available.earlier)
      (ett.series.data.tree available.earlier.succ) := by
    exact @helper_hstart_1006 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@selfMem) (@i)
        (@available) (@strictExtension) (@r) (@hr)
  have transport : ∀ m : ℕ, available.earlier.val ≤ m → m ≤ i.val →
      ∀ j : Fin (ett.rounds + 1), j.val = m →
        available.delta ∈ TreeMissingColors (ett.series.data.coloring j)
          (ett.series.data.tree j.succ) := by
    exact @helper_transport_1051 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@i)
        (@available) (@strictExtension) (@r) (@hr) (@hstart)
  have hDeltaA : available.delta ∈ TreeMissingColors phi A := by
    have hm := transport i.val available.earlierAtMost (le_rfl) i.castSucc rfl
    have hiTree : i.castSucc.succ = i.succ.castSucc := by apply Fin.ext; rfl
    simpa only [hphi, htree, hiTree] using hm
  have hcycleY : Sum.inl y ∈ available.cycle.walk.support := by
    exact @helper_hcycleY_1104 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen)
        (@outsideEndpoint) (@cycleEndpoint) (@i) (@available) (@strictExtension) (@r) (@hr) (@hy)
  by_cases hda : available.delta = alpha
  · exact cycleMissing (ett.series.data.coloring i.castSucc)
      available.gamma available.delta previousProper available.cycle y hcycleY
      (Or.inr (by simpa only [hda, hphi] using hAlphaY))
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet A) := by
    exact @helper_hclosed_1114 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@i) (@previousClosed)
        (@strictExtension) (@hphi) (@htree) (@r) (@hr)
  obtain ⟨u, hu, huDelta⟩ := Finset.mem_biUnion.mp hDeltaA
  obtain ⟨v, hv, hvAlpha⟩ := Finset.mem_biUnion.mp hAlphaA
  have havoid := (ClosedSetTwoColorComponentAvoidance G phi available.delta alpha
    (TreeSequenceVertexSet A) y u v hclosed hyNot hu hv huDelta hvAlpha).1
  let sigma := TwoColorComponentSwap G phi available.delta alpha (Sum.inl y)
  obtain ⟨hsigmaProper, hsigmaOne, hfixed, hmissing⟩ := outsideSwap available.delta alpha hda havoid
  have hDeltaY : available.delta ∈ MissingColors G sigma y :=
    (TwoColorComponentSwapMissingBehavior G phi available.delta alpha hda hproper
      (Sum.inl y)).2.2.1 y (selfMem phi available.delta alpha y) hAlphaY
  have hsigmaStable : StableColoring Tn (TashkinovStoredColors ett.series.data n)
      phi sigma := by
    rw [← hcore]
    exact ⟨fun f hf hc => hfixed f hf, hmissing⟩
  have hmod := Td G k e0 input T phi ett C.maximum C.positive hlower sigma
    hsigmaProper hsigmaOne (by simpa only [← ett.generatingColoring] using hsigmaStable)
  have hadjoinedFinal := TashkinovAugmentationSequenceInitialSegment
    (ett.series.data.coloring i.succ) _ _ closedExtension.1
  have hfinal : i.succ.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    have hh := congrArg Fin.val hslot
    simp only [n, Fin.val_last, Fin.val_succ] at hh ⊢
    omega
  rw [hfinal] at hadjoinedFinal
  have hadjoinedLen : adjoined.length = T.length := by
    have := adjoinedExactly.1
    rw [← htree] at this
    omega
  have hadjoinedT : adjoined = T := equalTrees
    (commonPrefix hadjoinedFinal ett.belowFinal (by omega)) hadjoinedLen
  have hseed : TreeSequenceAdjoinEdge Tn available.edge T := by
    simpa only [Tn, hslot, hadjoinedT] using adjoinedExactly
  obtain ⟨corr⟩ := hmod.2.2 T (by
      change TreeSequenceInitialSegment Tn T
      rw [← hcore]; exact hAT)
    (by change Tn.length < T.length; rw [← hcore]; omega)
    (Or.inr ⟨Or.inr hRE, available.edge, T, hedges, hseed, Relation.ReflTransGen.refl⟩)
  have hRepKind := (corr.extensionKindsAgree n).trans hRE
  have hRepEdges := (corr.connectingEdgesAgree n).trans hedges
  have hRepDelta : available.delta ∈ corr.replacementSeries.data.stored n := by
    rw [corr.storedColorsAgree, hslot, currentStored]
    simp
  have repCert := corr.replacementSeries.certified n
  generalize hRepSlot : n = repSlot at repCert
  cases repCert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    rw [hRepSlot, initialKind] at hRepKind
    simp at hRepKind
  | SE q pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
    rw [hRepSlot, ck] at hRepKind
    simp at hRepKind
  | PE q pp po pc pn nr choice alt gamma gr second sp so sr ew
      cc cp cu cs ce ck cv co cd cg cl oe st =>
    rw [hRepSlot, ck] at hRepKind
    simp at hRepKind
  | RE q pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
      exact @helper_branch_1178 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen) (@alpha)
          (@outsideEndpoint) (@cycleEndpoint) (@cycleMissing) (@i) (@available)
          (@strictExtension) (@r) (@hr) (@hy) (@hDeltaY) (@corr) (@hRepEdges) (@hRepDelta) (@q)
          (@pp) (@av) (@cc) (@cs) (@ce) (@st) (@hRepSlot)

theorem HierarchyCounterexampleOneAdditionZeroDividerImpossible
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (_ : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (_ : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (_ :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (honeAddition :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      T.length - A.length = 1)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hzero : C.hierarchy.dividerCount = 0) : False := by
  classical
  let H := C.hierarchy
  let A := base.core
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let y := T.vertex (Fin.last T.length)
  have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) = A := by
    exact @helper_hstar_138 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero)
  have hfirst : H.stage ⟨1, by omega⟩ = T := by
    exact @helper_hfirst_144 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero)
  have hAT : TreeSequenceInitialSegment A T := by
    simpa only [hfirst] using H.coreInsideFirst
  have hlen : T.length = A.length + 1 := by
    exact @helper_hlen_155 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@honeAddition) (@hzero) (@hstar) (@hAT)
  have prefixMem : ∀ {v : V}, v ∈ TreeSequenceVertexSet T →
      v ≠ y → v ∈ TreeSequenceVertexSet A := by
    exact @helper_prefixMem_161 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hAT) (@hlen)
  have hyNot : y ∉ TreeSequenceVertexSet A := by
    exact @helper_hyNot_179 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hAT) (@hlen)
  have hAElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    exact @helper_hAElementary_187 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@hprefixElementary) (@hzero) (@hstar) (@hAT) (@hlen)
  obtain ⟨alpha, hAlphaA, hAlphaY⟩ : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi A ∧ alpha ∈ MissingColors G phi y := by
    by_contra hnone
    have hn : ∀ alpha, alpha ∈ TreeMissingColors phi A →
        alpha ∉ MissingColors G phi y := by
      intro alpha ha hy
      exact hnone ⟨alpha, ha, hy⟩
    apply C.notElementary
    intro u hu v hv huv
    by_cases huy : u = y
    · have hvA := prefixMem hv (by intro hvy; exact huv (huy.trans hvy.symm))
      apply Finset.disjoint_left.mpr
      intro alpha hau hav
      exact hn alpha (Finset.mem_biUnion.mpr ⟨v, hvA, hav⟩) (huy ▸ hau)
    · exact @helper_branch_227 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen) (@prefixMem)
        (@hAElementary) (@hn) (@u) (@hu) (@v) (@hv) (@huv) (@huy)
  have outsideEndpoint (f : E) (u v : V)
      (hu : u ∈ TreeSequenceVertexSet A) (hv : v ∉ TreeSequenceVertexSet A)
      (hends : G.ends f = Sym2.mk u v)
      (hf : T.edge ⟨A.length, by omega⟩ = f) : y = v := by
    exact @helper_outsideEndpoint_233 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@hlen)
        (@hyNot) (@f) (@u) (@v) (@hu) (@hends) (@hf)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    exact @helper_commonPrefix_250 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@X) (@Y)
        (@Z) (@hXZ) (@hYZ) (@hXY)
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hl : X.length = Y.length) : X = Y := by
    exact @helper_equalTrees_263 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@X) (@Y)
        (@hXY) (@hl)
  have leaf (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hp : IsProperEdgeColoring G psi) (u : V)
      (hm : a ∈ MissingColors G psi u ∨ b ∈ MissingColors G psi u) :
      Set.Subsingleton ((TwoColorIncidenceGraph G psi a b).neighborSet (Sum.inl u)) := by
    exact @helper_leaf_279 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@psi) (@a) (@b) (@hp) (@u)
        (@hm)
  have selfMem (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V) :
      Sum.inl u ∈ TwoColorComponent G psi a b (Sum.inl u) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have cycleEndpoint (psi : PartialEdgeColoring E k) (a b : Fin k)
      (cycle : TwoColorCycle G psi a b) (f : E) (u v : V)
      (hends : G.ends f = Sym2.mk u v)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      Sum.inl v ∈ cycle.walk.support := by
    exact @helper_cycleEndpoint_314 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@psi)
        (@a) (@b) (@cycle) (@f) (@u) (@v) (@hends) (@hf)
  have cycleMissing (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hp : IsProperEdgeColoring G psi) (cycle : TwoColorCycle G psi a b)
      (v : V) (hv : Sum.inl v ∈ cycle.walk.support)
      (hm : a ∈ MissingColors G psi v ∨ b ∈ MissingColors G psi v) : False := by
    exact @helper_cycleMissing_343 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@leaf)
        (@psi) (@a) (@b) (@hp) (@cycle) (@v) (@hv) (@hm)
  have outsideCommon (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hab : a ≠ b) (hp : IsProperEdgeColoring G psi)
      (hi : TreeInterchangeable G A psi a b)
      (ha : a ∈ TreeMissingColors psi A) (hb : b ∈ TreeMissingColors psi A)
      (hym : a ∈ MissingColors G psi y ∨ b ∈ MissingColors G psi y) :
      ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G psi a b (Sum.inl y) := by
    exact @helper_outsideCommon_352 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (by
        assumption) (@hzero) (@hyNot) (@leaf) (@selfMem) (@psi) (@a) (@b) (@hab) (@hp) (@hi)
            (@ha) (@hb) (@hym)
  have outsideSwap (a b : Fin k) (hab : a ≠ b)
      (havoid : ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G phi a b (Sum.inl y)) :
      let sigma := TwoColorComponentSwap G phi a b (Sum.inl y)
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
        (∀ f, TreeIncidentEdge A f → sigma f = phi f) ∧
        (∀ v ∈ TreeSequenceVertexSet A,
          MissingColors G sigma v = MissingColors G phi v) := by
    dsimp only
    have hfixed (f : E) (hf : TreeIncidentEdge A f) :
        TwoColorComponentSwap G phi a b (Sum.inl y) f = phi f := by
      exact @helper_hfixed_432 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hzero) (@a) (@b) (@havoid)
          (@f) (@hf)
    refine ⟨TwoColorComponentSwapProper G phi a b hab hproper (Sum.inl y), ?_,
      hfixed, ?_⟩
    · exact @helper_branch_448 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@hzero) (@a) (@b) (@hab)
    · intro v hv
      exact (TwoColorComponentSwapMissingBehavior G phi a b hab hproper (Sum.inl y)).1
        v (havoid v hv)
  have hnPositive : 0 < n.val := C.positive
  have cert := ett.series.certified n
  generalize hslot : n = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have hv := congrArg Fin.val hslot
    simp only [Fin.val_zero] at hv
    omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_931 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
              (@hone) (@hzero) (@hfirst) (@hlen) (@alpha) (@hAlphaA) (@hAlphaY)
              (@outsideEndpoint) (@i) (@choice) (@seriesAlternative) (@currentColoring)
              (@currentEdges) (@currentKind) (@strictExtension) (@hslot)
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1573 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
              (@hlower) (@hzero) (@hfirst) (@hAT) (@hlen) (@hyNot) (@alpha) (@hAlphaA) (@hAlphaY)
              (@outsideEndpoint) (@commonPrefix) (@equalTrees) (@selfMem) (@cycleEndpoint)
              (@cycleMissing) (@outsideSwap) (@i) (@previousProper) (@previousClosed)
              (@available) (@currentColoring) (@currentStored) (@currentEdges) (@currentKind)
              (@adjoined) (@adjoinedExactly) (@closedExtension) (@strictExtension) (@hslot)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1205 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
              (@hone) (@hlower) (@hzero) (@hAT) (@hlen) (@prefixMem) (@alpha) (@hAlphaA)
              (@hAlphaY) (@commonPrefix) (@equalTrees) (@selfMem) (@outsideCommon) (@outsideSwap)
              (@i) (@gamma) (@currentKind) (@closedExtension) (@strictExtension) (@hslot)
end GoldbergSeymour

end
