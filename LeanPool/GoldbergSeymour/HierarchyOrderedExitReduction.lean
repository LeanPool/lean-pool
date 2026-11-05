/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GoodHierarchyNewMissingClosed
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.TreeSequenceEdgeSet
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# rutcor

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_segmentTrans_101.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y
        Z → TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  rcases hXY with ⟨hxy, vxy, exy⟩
  rcases hYZ with ⟨hyz, vyz, eyz⟩
  refine ⟨le_trans hxy hyz, ?_, ?_⟩
  · intro i
    exact (vyz (Fin.castLE (Nat.succ_le_succ hxy) i)).trans (vxy i)
  · intro i
    exact (eyz (Fin.castLE hxy i)).trans (exy i)

private theorem helper_stageSegment_112.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage (⟨a,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H segmentTrans a d
  induction d with
  | zero => intro hb; exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | succ d ih =>
    intro hb
    exact segmentTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)

private theorem helper_starPositive_127.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (j : Fin
        (H.dividerCount + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → HierarchyStarredStage H j = H.stage
        j.castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H j hj
  have hn : j ≠ 0 := by
    intro hh
    have hval : j.val = 0 := congrArg Fin.val hh
    omega
  unfold HierarchyStarredStage
  rw [← Fin.succ_pred j hn]
  rfl

private theorem helper_starMono_140.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base), (
    ∀ (a b : Fin (H.dividerCount + (2 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → TreeSequenceInitialSegment
        (H.stage a) (H.stage b)) → (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → HierarchyStarredStage H j =
        H.stage j.castSucc) → (
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), (0 : ℕ) < (↑j : ℕ) → TreeSequenceInitialSegment
        base.core (H.stage j)) →
    ∀ (i j : Fin (H.dividerCount + (1 : ℕ))), (↑i : ℕ) ≤ (↑j : ℕ) → TreeSequenceInitialSegment
        (HierarchyStarredStage H i) (HierarchyStarredStage H j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H stageMono starPositive coreStage i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j; exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
    · have hjp : 0 < j.val := by
        by_contra hh
        apply hj
        apply Fin.ext
        change j.val = 0
        omega
      rw [starPositive j hjp]
      exact coreStage j.castSucc hjp
  · have hip : 0 < i.val := by
      by_contra hh
      apply hi
      apply Fin.ext
      change i.val = 0
      omega
    rw [starPositive i hip, starPositive j (by omega)]
    exact stageMono i.castSucc j.castSucc hij

private theorem helper_hATy_179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T →
        A.length < T.length →
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega
    ); TreeSequenceInitialSegment A Ty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H q A hAT hAlen Ty
  refine ⟨?_, ?_, ?_⟩
  · change A.length ≤ min (A.length + (T.length - A.length - 1)) T.length
    omega
  · intro i
    exact hAT.2.1 i
  · intro i
    exact hAT.2.2 i

private theorem helper_coreSegment_197.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    TreeSequenceInitialSegment Tn base.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base Tn
  by_cases hp : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
  · obtain ⟨union⟩ := (base.parallel hp).2.2
    exact union.leftSegment
  · rw [base.nonparallel hp]
    exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩

private theorem helper_descend_206.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ :
        GoodHierarchy H),
    ∀ alpha ∈ TreeMissingColors phi (HierarchyStarredStage H (Fin.last H.dividerCount)),
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H j))) →
    ∀ (d : ℕ) (j : Fin (H.dividerCount + (1 : ℕ))), H.dividerCount ≤ (↑j : ℕ) + d → (0 : ℕ) < (↑j
        : ℕ) → (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑j : ℕ) ≤ (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) → alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage H j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha halpha q elementaryStar d
  induction d with
  | zero =>
    intro j hj _ _
    have hjq : j = q := Fin.ext (by simp [q]; omega)
    simpa [hjq, q] using halpha
  | succ d ih =>
    intro j hj hjp hn
    by_cases hjq : j = q
    · simpa [hjq, q] using halpha
    · have hjlt : j.val < H.dividerCount := by
        have hne : j.val ≠ H.dividerCount := by
          intro hh; apply hjq; apply Fin.ext; simpa [q] using hh
        omega
      let i : Fin H.dividerCount := ⟨j.val, hjlt⟩
      have hic : i.castSucc = j := Fin.ext rfl
      have hnext := ih i.succ (by dsimp [i]; omega) (by simp)
        (fun s hs => hn s (by dsimp [i] at hs; omega))
      by_contra hold
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hnext
      have hvo : v ∉ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc) := by
        intro hvo
        exact hold (Finset.mem_biUnion.mpr ⟨v, by simpa [hic] using hvo, hvm⟩)
      have hnew : alpha ∈
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G phi v) :=
        Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvo⟩, hvm⟩
      have hc := GoodHierarchyNewMissingClosed good i (elementaryStar i.succ) alpha hnew
      apply hn i.succ (by dsimp [i]; omega)
      intro c hc'
      have : c = alpha := Finset.mem_singleton.mp hc'
      subst c
      exact hc

private theorem helper_reserved_251.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha : Fin k) (i : Fin H.dividerCount), alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage H i.succ) → ¬TreeColorSetClosed G phi (HierarchyStarredStage H
        i.succ) ({ alpha } : Finset (Fin k)) → alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion
        (good.gamma i.castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha i hm hn
  by_contra hh
  apply hn
  intro c hc
  have : c = alpha := Finset.mem_singleton.mp hc
  subst c
  exact good.minusClosed i alpha (Finset.mem_sdiff.mpr ⟨hm, hh⟩)

private theorem helper_cutoff_262.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (B : TreeSequence G e0),
    TreeSequenceInitialSegment B T →
    ∀ eta ∉ TreeMissingColors phi B,
    min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) B.length = B.length := by
  classical
  intro V E _ _ G k e0 T phi B hBT eta hm
  let _ := Fintype.ofFinite V
  have heq := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta B.length le_rfl
  have hempty : ¬ (Finset.univ.filter fun j : Fin (B.length + 1) =>
      eta ∈ MissingColors G phi (B.vertex j)).Nonempty := by
    rintro ⟨j, hj⟩
    apply hm
    apply Finset.mem_biUnion.mpr
    refine ⟨B.vertex j, ?_, (Finset.mem_filter.mp hj).2⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  rw [HierarchyFirstMissingPosition, dite_eq_right hempty] at heq
  simpa using heq.symm

private theorem helper_segmentAvoid_277.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha : Fin k),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ (i j : Fin (H.dividerCount + (1 : ℕ))), (↑i : ℕ) ≤ (↑j : ℕ) → TreeSequenceInitialSegment
        (HierarchyStarredStage H i) (HierarchyStarredStage H j)) → TreeSequenceInitialSegment A T
        → (
    ∀ (B : TreeSequence G e0), TreeSequenceInitialSegment B T →
    ∀ eta ∉ TreeMissingColors phi B, min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) B.length
        = B.length) →
    ∀ (i : Fin H.dividerCount), alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma
        i.castSucc) →
    ∀ (t : Fin (HierarchyStarredStage H i.succ).length), (HierarchyStarredStage H
        i.castSucc).length ≤ (↑t : ℕ) → phi ((HierarchyStarredStage H i.succ).edge t) ≠ some alpha
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha q A segmentTrans starMono hAT cutoff
      i hr
  obtain ⟨eta, heta, hgamma⟩ := Finset.mem_biUnion.mp hr
  have havoid := (Finset.mem_sdiff.mp
    (good.avoidance i.castSucc eta (HierarchyStoredColorsAntitone H i heta) hgamma)).2
  have hnm : eta ∉ TreeMissingColors phi (HierarchyStarredStage H i.succ) :=
    (Finset.mem_sdiff.mp heta).2
  have hBT := segmentTrans (starMono i.succ q (by simp [q])) hAT
  have hc := cutoff (HierarchyStarredStage H i.succ) hBT eta hnm
  intro t ht hcolor
  apply havoid
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, t, ht, ?_, hcolor⟩
  change min (HierarchyFirstMissingPosition phi T eta).val
    (H.stage i.castSucc.succ).length = (H.stage i.castSucc.succ).length at hc
  rw [hc]
  exact t.isLt

private theorem helper_intervalAvoid_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha : Fin k),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (i j : Fin (H.dividerCount + (1 : ℕ))), (↑i : ℕ) ≤ (↑j : ℕ) → TreeSequenceInitialSegment
        (HierarchyStarredStage H i) (HierarchyStarredStage H j)) → (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑j : ℕ) ≤ (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) → alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage H j)) → (
    ∀ (i : Fin H.dividerCount), alpha ∈ TreeMissingColors phi (HierarchyStarredStage H i.succ) →
        ¬TreeColorSetClosed G phi (HierarchyStarredStage H i.succ) ({ alpha } : Finset (Fin k)) →
        alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)) → (
    ∀ (i : Fin H.dividerCount), alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma
        i.castSucc) →
    ∀ (t : Fin (HierarchyStarredStage H i.succ).length), (HierarchyStarredStage H
        i.castSucc).length ≤ (↑t : ℕ) → phi ((HierarchyStarredStage H i.succ).edge t) ≠ some
        alpha) →
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) →
    ∀ (t : Fin A.length), (HierarchyStarredStage H r).length ≤ (↑t : ℕ) → phi (A.edge t) ≠ some
        alpha := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha q A starMono missingStage reserved
      segmentAvoid r hn
  have inductiveAvoid : ∀ d (s : Fin (H.dividerCount + 1)), s.val = r.val + d →
      ∀ t : Fin (HierarchyStarredStage H s).length,
        (HierarchyStarredStage H r).length ≤ t.val →
        phi ((HierarchyStarredStage H s).edge t) ≠ some alpha := by
    intro d
    induction d with
    | zero =>
      intro s hs t ht
      have : s = r := Fin.ext (by omega)
      subst s
      have := t.isLt
      omega
    | succ d ih =>
      intro s hs t ht
      let i : Fin H.dividerCount := ⟨s.val - 1, by omega⟩
      have his : i.succ = s := Fin.ext (by dsimp [i]; omega)
      have hprev : i.castSucc.val = r.val + d := by dsimp [i]; omega
      by_cases htp : t.val < (HierarchyStarredStage H i.castSucc).length
      · let u : Fin (HierarchyStarredStage H i.castSucc).length := ⟨t.val, htp⟩
        have hab := starMono i.castSucc s (by dsimp [i]; omega)
        have he : (HierarchyStarredStage H s).edge t =
            (HierarchyStarredStage H i.castSucc).edge u := by
          have he := hab.2.2 u
          have hi : Fin.castLE hab.1 u = t := Fin.ext rfl
          simpa [hi] using he
        rw [he]
        exact ih i.castSucc hprev u ht
      · have hn' := hn i.succ (by rw [his]; omega)
        have hm := missingStage i.succ (by simp)
          (fun z hz => hn z (by rw [his] at hz; omega))
        have ha := segmentAvoid i (reserved i hm hn')
        rw [his] at ha
        exact ha t (by omega)
  exact inductiveAvoid (H.dividerCount - r.val) q (by simp [q]; omega)

private theorem helper_unions_343.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha : Fin k), (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑j : ℕ) ≤ (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) → alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage H j)) → (
    ∀ (i : Fin H.dividerCount), alpha ∈ TreeMissingColors phi (HierarchyStarredStage H i.succ) →
        ¬TreeColorSetClosed G phi (HierarchyStarredStage H i.succ) ({ alpha } : Finset (Fin k)) →
        alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)) → (
    ∀ (i : Fin (H.dividerCount + (1 : ℕ))), ¬TreeColorSetClosed G phi (HierarchyStarredStage H i)
        ({ alpha } : Finset (Fin k))) →
    ∀ (i : Fin H.dividerCount), alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma
        i.castSucc) ∧ alpha ∈ (HierarchyStoredColorsAt H i.castSucc).biUnion (good.gamma
        i.castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha missingStage reserved hn i
  have hr := reserved i (missingStage i.succ (by simp) (fun s _ => hn s)) (hn i.succ)
  refine ⟨hr, ?_⟩
  obtain ⟨eta, heta, hg⟩ := Finset.mem_biUnion.mp hr
  exact Finset.mem_biUnion.mpr ⟨eta, HierarchyStoredColorsAntitone H i heta, hg⟩

private theorem helper_closedSingleton_356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (alpha : Fin k) (B : TreeSequence G e0),
        ColoredVertexSetClosed G phi (TreeSequenceVertexSet B) → alpha ∈ TreeMissingColors phi B →
        TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k)) := by
  classical
  intro V E _ _ G k e0 phi alpha B hc hm c hcs
  have : c = alpha := Finset.mem_singleton.mp hcs
  subst c
  obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hb, hcol⟩ := Finset.mem_filter.mp hf
  exact hc hb hv hcol hvm

private theorem helper_stableClosed_368.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (B : TreeSequence G e0) (C : Finset (Fin k)) (psi pi : PartialEdgeColoring E k),
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 → IsProperEdgeColoring G pi →
        IsOneEdgeUncolored pi e0 → StableColoring B C psi pi → ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet B) → ColoredVertexSetClosed G pi (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ G k e0 B C psi pi hpsi hpsiOne hpi hpiOne hs hc
  have hr : StableColoring B C pi psi :=
    (sc2 G e0 B C).symm
      (x := ⟨psi, hpsi, hpsiOne⟩) (y := ⟨pi, hpi, hpiOne⟩) hs
  intro f c v hb hv hcol hvm
  have hf : TreeIncidentEdge B f := by
    have hb' : ∃ u ∈ TreeSequenceVertexSet B, ∃ w ∉ TreeSequenceVertexSet B,
        G.ends f = Sym2.mk u w := by
      simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    obtain ⟨u, hu, w, hw, he⟩ := hb'
    refine ⟨u, hu, ?_⟩
    change u ∈ G.ends f
    rw [he]
    simp
  have hm : c ∈ TreeMissingColors pi B := Finset.mem_biUnion.mpr ⟨v, hv, hvm⟩
  have hsame := hr.1 f hf ⟨c, Finset.mem_union_left _ hm, hcol⟩
  have hvm' : c ∈ MissingColors G psi v := by rw [hr.2 v hv]; exact hvm
  exact hc hb hv (hsame.trans hcol) hvm'

private theorem helper_terminalPE_393.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (alpha : Fin
        k),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc; (
    ∀ (i : Fin (H.dividerCount + (1 : ℕ))), ¬TreeColorSetClosed G phi (HierarchyStarredStage H i)
        ({ alpha } : Finset (Fin k))) → alpha ∈ TreeMissingColors phi Tn → (
    ∀ (B : TreeSequence G e0), ColoredVertexSetClosed G phi (TreeSequenceVertexSet B) → alpha ∈
        TreeMissingColors phi B → TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k))) → (
    ∀ (B : TreeSequence G e0) (C : Finset (Fin k)) (psi pi : PartialEdgeColoring E k),
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 → IsProperEdgeColoring G pi →
        IsOneEdgeUncolored pi e0 → StableColoring B C psi pi → ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet B) → ColoredVertexSetClosed G pi (TreeSequenceVertexSet B)) →
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H alpha Tn hn missingTn closedSingleton stableClosed
  let p : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
  have hp : p.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    dsimp [p]
    have := ett.roundsPositive
    omega
  have hphi : phi = ett.series.data.coloring p.succ := by
    rw [hp]
    exact ett.generatingColoring
  have hTn : Tn = ett.series.data.tree p.succ.castSucc := by rw [hp]
  generalize heq : p.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero p heq).elim
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
          strictExtension =>
    have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
    subst ci
    rw [← hp]
    exact currentKind
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
    subst ci
    have hnot : ett.series.data.kind (Fin.last ett.rounds) ≠
        some TashkinovExtensionKind.PE := by rw [← hp, currentKind]; simp
    apply False.elim
    apply hn 0
    change TreeColorSetClosed G phi base.core {alpha}
    rw [base.nonparallel hnot]
    apply closedSingleton Tn
    · rw [hphi, currentColoring, hTn]
      exact previousClosed
    · exact missingTn
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
    subst ci
    have hnot : ett.series.data.kind (Fin.last ett.rounds) ≠
        some TashkinovExtensionKind.PE := by rw [← hp, currentKind]; simp
    apply False.elim
    apply hn 0
    change TreeColorSetClosed G phi base.core {alpha}
    rw [base.nonparallel hnot]
    apply closedSingleton Tn
    · rw [hphi, currentColoring, hTn]
      exact stableClosed _ _ _ _ previousProper previousOneUncolored
        choice.selectedProper choice.selectedOneUncolored choice.selectedStable previousClosed
    · exact missingTn

private theorem helper_witness_459.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (alpha : Fin k),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        TreeSequenceInitialSegment Tn T → alpha ∈ TreeMissingColors phi Tn →
    let a : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let va : V := T.vertex a; va ∈ TreeSequenceVertexSet Tn ∧ alpha ∈ MissingColors G phi va := by
  classical
  intro V E _ _ _ G k e0 input T phi ett alpha Tn TnT missingTn a va
  obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp missingTn
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨i, hi⟩ := hv
  let iT := Fin.castLE (Nat.succ_le_succ TnT.1) i
  have hmi : alpha ∈ MissingColors G phi (T.vertex iT) := by
    rw [TnT.2.1 i, hi]
    exact hvm
  let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
    alpha ∈ MissingColors G phi (T.vertex j)
  have hiC : iT ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmi⟩
  have hC : candidates.Nonempty := ⟨iT, hiC⟩
  have ha : a = candidates.min' hC := by
    dsimp [a, HierarchyFirstMissingPosition]
    rw [dite_eq_left hC]
  have hma : alpha ∈ MissingColors G phi va := by
    have hmA : a ∈ candidates := ha.symm ▸ Finset.min'_mem candidates hC
    exact (Finset.mem_filter.mp hmA).2
  have hai : a.val ≤ i.val := by
    rw [ha]
    exact Finset.min'_le candidates iT hiC
  let aN : Fin (Tn.length + 1) := ⟨a.val, by have := i.isLt; omega⟩
  have hcast : Fin.castLE (Nat.succ_le_succ TnT.1) aN = a := Fin.ext rfl
  refine ⟨?_, hma⟩
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨aN, ?_⟩
  exact (TnT.2.1 aN).symm.trans (congrArg T.vertex hcast)

private theorem helper_noMissingClosure_505.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (alpha : Fin
        k),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H j))) →
    let a : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let va : V := T.vertex a; va ∈ TreeSequenceVertexSet Tn ∧ alpha ∈ MissingColors G phi va → va
        ∉ TreeSequenceVertexSet base.closure → TreeSequenceVertexSet base.closure ⊆
        TreeSequenceVertexSet base.core → va ∈ TreeSequenceVertexSet base.core → alpha ∉
        TreeMissingColors phi base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H alpha Tn elementaryStar a va witness outside
      closureCore vaCore hm
  obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hm
  have hne : va ≠ w := by intro he; exact outside (he.symm ▸ hw)
  exact Finset.disjoint_left.mp
    (elementaryStar 0 vaCore (closureCore hw) hne) witness.2 hwm

private theorem helper_branch_575.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (alpha : Fin
        k),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let _ : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (i j : Fin (H.dividerCount + (1 : ℕ))), (↑i : ℕ) ≤ (↑j : ℕ) → TreeSequenceInitialSegment
        (HierarchyStarredStage H i) (HierarchyStarredStage H j)) → (
    ∀ (t : Fin base.core.length), Tn.length ≤ (↑t : ℕ) → phi (base.core.edge t) ≠ some alpha) →
    ∀ (t : Fin (HierarchyStarredStage H (Fin.last H.dividerCount)).length), (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length ≤ (↑t : ℕ) → phi ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).edge t) = some alpha → ¬base.core.length ≤ (↑t : ℕ) → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H alpha q Tn A starMono coreAvoid t ht hc htc
  let u : Fin base.core.length := ⟨t.val, by omega⟩
  have hab := starMono 0 q (by simp)
  change TreeSequenceInitialSegment base.core A at hab
  have he := hab.2.2 u
  have hi : Fin.castLE hab.1 u = t := Fin.ext rfl
  have he' : A.edge t = base.core.edge u := by simpa [hi] using he
  exact coreAvoid u ht (he' ▸ hc)

private theorem helper_closureEdges_852.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base) (alpha : Fin
        k),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ∀ (_ :
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z) (_ : alpha ∉
        TreeMissingColors phi base.closure) (_ : TashkinovClosure phi (TreeSequencePrefix
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)) base.closure),
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (t : Fin base.closure.length), phi (base.closure.edge t) = some alpha → base.closure.edge t
        ∈ TreeSequenceEdgeSet P := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H alpha Tn segmentTrans noMissingClosure hclosure P
  have seq : TashkinovAugmentationSequence phi P base.closure := hclosure.1
  have aux : ∀ {B : TreeSequence G e0}, TashkinovAugmentationSequence phi P B →
      TreeSequenceInitialSegment B base.closure →
      ∀ t : Fin B.length, phi (B.edge t) = some alpha → B.edge t ∈ TreeSequenceEdgeSet P := by
    intro B hs
    induction hs with
    | refl =>
      intro _ t _
      simp only [TreeSequenceEdgeSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨t, rfl⟩
    | @tail Y Z hPY hstep ih =>
      intro hZ t hc
      obtain ⟨hlen, hYZ, c, hcLast, hcm⟩ := hstep
      have hY := segmentTrans hYZ hZ
      by_cases ht : t.val < Y.length
      · let u : Fin Y.length := ⟨t.val, ht⟩
        have hi : Fin.castLE hYZ.1 u = t := Fin.ext rfl
        have he : Z.edge t = Y.edge u := by simpa [hi] using hYZ.2.2 u
        have hp := ih hY u (he ▸ hc)
        simpa only [he] using hp
      · have htLast : t = Fin.cast hlen.symm (Fin.last Y.length) := by
          apply Fin.ext
          have := t.isLt
          simp only [Fin.val_cast, Fin.val_last]
          omega
        have hca : c = alpha := Option.some.inj
          (hcLast.symm.trans (by simpa only [htLast] using hc))
        subst c
        apply False.elim
        apply noMissingClosure
        obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hcm
        exact Finset.mem_biUnion.mpr
          ⟨w, TreeSequenceInitialSegmentVertexSetSubset hY hw, hwm⟩
  exact aux seq ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩

private theorem helper_continuation_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (_ : (0 : ℕ) < H.dividerCount) (_ :
    let i : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              first
              | omega
              | ( have := GoldbergSeymour.TreeSequence.positive T
                  have := GoldbergSeymour.ExtendedTashkinovTree.roundsPositive ett
                  all_goals omega)
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet
        Tn)) (alpha : Fin k),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let _ : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ :
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z) (_ :
    ∀ (i j : Fin (H.dividerCount + (1 : ℕ))) (_ : (↑i : ℕ) ≤ (↑j : ℕ)), TreeSequenceInitialSegment
        (HierarchyStarredStage H i) (HierarchyStarredStage H j)) (_ :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H j))) (_ : TreeSequenceInitialSegment Tn
        base.core) (_ : TreeSequenceInitialSegment Tn T) (_ :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))) (_ : (0 : ℕ) < (↑j : ℕ)) (_ :
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑j : ℕ) ≤ (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))), alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage H j)) (_ :
    ∀ (i : Fin H.dividerCount) (_ : alpha ∈ TreeMissingColors phi (HierarchyStarredStage H
        i.succ)) (_ : ¬TreeColorSetClosed G phi (HierarchyStarredStage H i.succ) ({ alpha } :
        Finset (Fin k))), alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma
        i.castSucc)) (_ :
    ∀ (i : Fin H.dividerCount) (_ : alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma
        i.castSucc)) (t : Fin (HierarchyStarredStage H i.succ).length), (HierarchyStarredStage H
        i.castSucc).length ≤ (↑t : ℕ) → phi ((HierarchyStarredStage H i.succ).edge t) ≠ some
        alpha), ((
    ∃ (i : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H i)
        ({ alpha } : Finset (Fin k))) →
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ alpha } : Finset (Fin k)) → (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) → alpha ∉ ({c : Fin k |
    ∃ (t : Fin (HierarchyStarredStage H (Fin.last H.dividerCount)).length), (HierarchyStarredStage
        H r).length ≤ (↑t : ℕ) ∧ phi ((HierarchyStarredStage H (Fin.last H.dividerCount)).edge t)
        = some c} : Finset (Fin k))) ∧ ((
    ∀ (i : Fin (H.dividerCount + (1 : ℕ))), ¬TreeColorSetClosed G phi (HierarchyStarredStage H i)
        ({ alpha } : Finset (Fin k))) → (
    ∀ (j : Fin H.dividerCount), alpha ∈ (HierarchyStoredColorsAt H j.succ).biUnion (good.gamma
        j.castSucc) ∧ alpha ∈ (HierarchyStoredColorsAt H j.castSucc).biUnion (good.gamma
        j.castSucc)) ∧ ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
        ∧ T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) \ TreeSequenceVertexSet base.closure
        ∧ alpha ∉ ({c : Fin k |
    ∃ (t : Fin (HierarchyStarredStage H (Fin.last H.dividerCount)).length), (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length ≤ (↑t : ℕ) ∧ phi ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).edge t) = some c} : Finset (Fin k))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good hq hpreStepElementary alpha q Tn A
      segmentTrans starMono elementaryStar coreSegment TnT missingStage reserved segmentAvoid
  have intervalAvoid (r : Fin (H.dividerCount + 1))
      (hn : ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha}) :
      ∀ t : Fin A.length, (HierarchyStarredStage H r).length ≤ t.val →
        phi (A.edge t) ≠ some alpha := by
    apply helper_intervalAvoid_298 <;> assumption
  constructor
  · intro _ r _ hn hmem
    obtain ⟨t, ht, hc⟩ := (Finset.mem_filter.mp hmem).2
    exact intervalAvoid r hn t ht hc
  · intro hn
    have unions : ∀ i : Fin H.dividerCount,
        alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc) ∧
        alpha ∈ (HierarchyStoredColorsAt H i.castSucc).biUnion (good.gamma i.castSucc) := by
      apply helper_unions_343 <;> assumption
    let zero : Fin H.dividerCount := ⟨0, hq⟩
    obtain ⟨eta, heta, hg⟩ := Finset.mem_biUnion.mp (unions zero).2
    have missingTn : alpha ∈ TreeMissingColors phi Tn := by
      have hm := (Finset.mem_sdiff.mp (good.avoidance zero.castSucc eta heta hg)).1
      simpa [HierarchyStageMissingColors, zero, Tn] using hm
    have closedSingleton (B : TreeSequence G e0)
        (hc : ColoredVertexSetClosed G phi (TreeSequenceVertexSet B))
        (hm : alpha ∈ TreeMissingColors phi B) : TreeColorSetClosed G phi B {alpha} := by
      apply helper_closedSingleton_356 <;> assumption
    have stableClosed := @helper_stableClosed_368 (@V) (@E) inferInstance inferInstance (@G) (@k)
        (@e0)
    have terminalPE : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE := by
      apply helper_terminalPE_393 <;> assumption
    -- The least missing position is an actual witness in the ladder tree.
    let a := HierarchyFirstMissingPosition phi T alpha
    let va := T.vertex a
    have witness : va ∈ TreeSequenceVertexSet Tn ∧ alpha ∈ MissingColors G phi va := by
      apply helper_witness_459 <;> assumption
    have outside : va ∉ TreeSequenceVertexSet base.closure := by
      intro hv
      have commonClosed := ParallelCommonMissingClosed G k e0 input T phi phi ett
        (by have := ett.roundsPositive; omega) base ett.generatingColoring terminalPE
        hpreStepElementary
      have hmR : alpha ∈ TreeMissingColors phi base.closure :=
        Finset.mem_biUnion.mpr ⟨va, hv, witness.2⟩
      apply hn 0
      intro c hc
      have : c = alpha := Finset.mem_singleton.mp hc
      subst c
      exact commonClosed alpha (Finset.mem_inter.mpr ⟨missingTn, hmR⟩)
    obtain ⟨union⟩ := (base.parallel terminalPE).2.2
    have closureCore : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet base.core := by
      rw [union.vertexSet]
      exact Finset.subset_union_right
    have vaCore : va ∈ TreeSequenceVertexSet base.core :=
      TreeSequenceInitialSegmentVertexSetSubset coreSegment witness.1
    have noMissingClosure : alpha ∉ TreeMissingColors phi base.closure := by
      apply helper_noMissingClosure_505 <;> assumption
    have hclosure := (base.parallel terminalPE).2.1
    let P := TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
      (Nat.le_of_lt_succ base.supportPosition.isLt)
    have prefixTn : TreeSequenceInitialSegment P Tn :=
      ⟨Nat.le_of_lt_succ base.supportPosition.isLt, (fun _ => rfl), (fun _ => rfl)⟩
    -- Every added closure edge has a missing-color witness in the closure.
    have closureEdges : ∀ t : Fin base.closure.length,
        phi (base.closure.edge t) = some alpha →
        base.closure.edge t ∈ TreeSequenceEdgeSet P := by
      apply helper_closureEdges_852 <;> assumption
    have coreAvoid : ∀ t : Fin base.core.length, Tn.length ≤ t.val →
        phi (base.core.edge t) ≠ some alpha := by
      intro t ht hc
      obtain ⟨i, hi, _⟩ := union.newEntryFromRight t ht
      have hp := closureEdges i (hi ▸ hc)
      simp only [TreeSequenceEdgeSet, Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨j, hj⟩ := hp
      have hjn := prefixTn.2.2 j
      have hnc := union.leftSegment.2.2 (Fin.castLE prefixTn.1 j)
      have he : base.core.edge (Fin.castLE union.leftSegment.1 (Fin.castLE prefixTn.1 j)) =
          base.core.edge t := hnc.trans (hjn.trans (hj.trans hi.symm))
      have hv := congrArg Fin.val (base.core.edge_injective he)
      have := j.isLt
      have := prefixTn.1
      dsimp only [Fin.castLE] at hv
      omega
    refine ⟨unions, terminalPE, Finset.mem_sdiff.mpr ⟨witness.1, outside⟩, ?_⟩
    intro hm
    obtain ⟨t, ht, hc⟩ := (Finset.mem_filter.mp hm).2
    by_cases htc : base.core.length ≤ t.val
    · exact intervalAvoid 0 (fun s _ => hn s) t htc hc
    · exact @helper_branch_575 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@alpha) (@starMono)
        (@coreAvoid) (@t) (@ht) (@hc) (@htc)

theorem rutcor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hq : 0 < H.dividerCount)
    (hprefixElementary :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hpreStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by
        have hp := ett.roundsPositive
        omega⟩
      let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn))
    (alpha : Fin k)
    (halpha : alpha ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount))) :
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    let Tnq := HierarchyStarredStage H q
    ((∃ i : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H i) {alpha}) →
      ∀ r : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {alpha} →
        (∀ s : Fin (H.dividerCount + 1), r.val < s.val →
          ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha}) →
        alpha ∉ (Finset.univ.filter fun c =>
          ∃ t : Fin Tnq.length,
            (HierarchyStarredStage H r).length ≤ t.val ∧
              phi (Tnq.edge t) = some c)) ∧
    ((∀ i : Fin (H.dividerCount + 1),
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H i) {alpha}) →
      (∀ j : Fin H.dividerCount,
        alpha ∈ (HierarchyStoredColorsAt H j.succ).biUnion
            (good.gamma j.castSucc) ∧
          alpha ∈ (HierarchyStoredColorsAt H j.castSucc).biUnion
            (good.gamma j.castSucc)) ∧
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE ∧
      T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
        TreeSequenceVertexSet Tn \ TreeSequenceVertexSet base.closure ∧
      alpha ∉ (Finset.univ.filter fun c =>
        ∃ t : Fin Tnq.length,
          Tn.length ≤ t.val ∧ phi (Tnq.edge t) = some c)) := by
  classical
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  let A := HierarchyStarredStage H q
  change ((_ → _) ∧ (_ → _))
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) : TreeSequenceInitialSegment X Z := by
    apply helper_segmentTrans_101 <;> assumption
  have stageSegment : ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    apply helper_stageSegment_112; assumption
  have stageMono (a b : Fin (H.dividerCount + 2)) (hab : a.val ≤ b.val) :
      TreeSequenceInitialSegment (H.stage a) (H.stage b) := by
    clear * - stageSegment hab
    have hh := stageSegment a.val (b.val - a.val) (by omega)
    convert hh using 1; congr 1; apply Fin.ext; simp; omega
  have starPositive (j : Fin (H.dividerCount + 1)) (hj : 0 < j.val) :
      HierarchyStarredStage H j = H.stage j.castSucc := by
    apply helper_starPositive_127; assumption
  have coreStage (j : Fin (H.dividerCount + 2)) (hj : 0 < j.val) :
      TreeSequenceInitialSegment base.core (H.stage j) :=
    segmentTrans H.coreInsideFirst (stageMono ⟨1, by omega⟩ j (by change 1 ≤ j.val; omega))
  have starMono (i j : Fin (H.dividerCount + 1)) (hij : i.val ≤ j.val) :
      TreeSequenceInitialSegment (HierarchyStarredStage H i)
        (HierarchyStarredStage H j) := by
    apply helper_starMono_140 <;> assumption
  have hA : A = H.stage q.castSucc := starPositive q hq
  have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
  have hAT : TreeSequenceInitialSegment A T := by
    rw [hA]
    have hh := H.nested q
    rw [hlast, H.terminalStage] at hh
    exact hh
  have hAlen : A.length < T.length := by
    rw [hA]
    have hh := H.strict q
    rw [hlast, H.terminalStage] at hh
    exact hh
  let Ty := TreeSequencePrefix T
    (min (A.length + (T.length - A.length - 1)) T.length)
    (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
  have hATy : TreeSequenceInitialSegment A Ty := by
    apply helper_hATy_179 <;> assumption
  have elementaryA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv huv
    exact hprefixElementary (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) huv
  have elementaryStar (j : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet (HierarchyStarredStage H j)) := by
    intro u hu v hv huv
    have hs := starMono j q (by simp [q]; omega)
    exact elementaryA (TreeSequenceInitialSegmentVertexSetSubset hs hu)
      (TreeSequenceInitialSegmentVertexSetSubset hs hv) huv
  have coreSegment : TreeSequenceInitialSegment Tn base.core := by
    apply helper_coreSegment_197
  have TnT : TreeSequenceInitialSegment Tn T :=
    segmentTrans coreSegment (segmentTrans (starMono 0 q (by simp)) hAT)
  -- A newly missing color would close the next stage, so missingness descends.
  have descend : ∀ d (j : Fin (H.dividerCount + 1)),
      H.dividerCount ≤ j.val + d → 0 < j.val →
      (∀ s : Fin (H.dividerCount + 1), j.val ≤ s.val →
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha}) →
      alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j) := by
    apply helper_descend_206 <;> assumption
  have missingStage (j : Fin (H.dividerCount + 1)) (hj : 0 < j.val)
      (hn : ∀ s : Fin (H.dividerCount + 1), j.val ≤ s.val →
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha}) :
      alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j) :=
    descend H.dividerCount j (by omega) hj hn
  have reserved (i : Fin H.dividerCount)
      (hm : alpha ∈ TreeMissingColors phi (HierarchyStarredStage H i.succ))
      (hn : ¬ TreeColorSetClosed G phi (HierarchyStarredStage H i.succ) {alpha}) :
      alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc) := by
    apply helper_reserved_251 <;> assumption
  have cutoff (B : TreeSequence G e0) (hBT : TreeSequenceInitialSegment B T)
      (eta : Fin k) (hm : eta ∉ TreeMissingColors phi B) :
      min (HierarchyFirstMissingPosition phi T eta).val B.length = B.length := by
    apply helper_cutoff_262 <;> assumption
  have segmentAvoid (i : Fin H.dividerCount)
      (hr : alpha ∈ (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)) :
      ∀ t : Fin (HierarchyStarredStage H i.succ).length,
        (HierarchyStarredStage H i.castSucc).length ≤ t.val →
        phi ((HierarchyStarredStage H i.succ).edge t) ≠ some alpha := by
    apply helper_segmentAvoid_277 <;> assumption
  exact @helper_continuation_896 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@good) (@hq)
      (@hpreStepElementary) (@alpha) (@segmentTrans) (@starMono) (@elementaryStar) (@coreSegment)
      (@TnT) (@missingStage) (@reserved) (@segmentAvoid)
end GoldbergSeymour

end
