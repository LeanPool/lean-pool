/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.BaseControl

public import LeanPool.GoldbergSeymour.HierarchyOrderedExitReduction
public import LeanPool.GoldbergSeymour.BaseDisplayedEdges
public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable

/-!
# P2813_T1_Displayed Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem P2813_T1_DisplayedEdges_missingAtMax_188.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ :
        GoodHierarchy H),
    let q := Fin.last H.dividerCount;
    let A := HierarchyStarredStage H q;
    ∀ (_ : (
    ∀ (r s : Fin (H.dividerCount + 1)) (_ : r ≤ s), TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s))) (_ : (
    ∀ (r : Fin (H.dividerCount + 1)), ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        (HierarchyStarredStage H r)))) (_ : (
    ∀ {B S : TreeSequence G e0} (_ : TreeSequenceInitialSegment B S), TreeMissingColors phi B ⊆
        TreeMissingColors phi S)),
    ∀ c ∈ TreeMissingColors phi A,
    ∀ (r : Fin (H.dividerCount + 1)), (
    ∀ (s : Fin (H.dividerCount + 1)), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) { c }) → c ∈ TreeMissingColors phi (HierarchyStarredStage H r)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good q A starChain helemStar missingSubset c
      hcA r hmax
  let P (j : ℕ) := ∃ hj : j ≤ H.dividerCount,
    c ∈ TreeMissingColors phi (HierarchyStarredStage H ⟨j, by omega⟩)
  have hex : ∃ j, P j := ⟨H.dividerCount, le_rfl, hcA⟩
  let s := Nat.find hex
  obtain ⟨hs, hsm⟩ : P s := Nat.find_spec hex
  by_cases hsr : s ≤ r.val
  · exact missingSubset (starChain ⟨s, by omega⟩ r hsr) hsm
  · have hspos : 0 < s := by omega
    let i : Fin H.dividerCount := ⟨s - 1, by omega⟩
    have his : i.succ = (⟨s, by omega⟩ : Fin (H.dividerCount + 1)) :=
      Fin.ext (by simp [i]; omega)
    have hprev : c ∉ TreeMissingColors phi (HierarchyStarredStage H i.castSucc) := by
      intro hm
      have hh : P (s - 1) := ⟨by omega, hm⟩
      have hmin := Nat.find_min' hex hh
      change s ≤ s - 1 at hmin
      omega
    have hsm' : c ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
      simpa only [← his, HierarchyStarredStage, Fin.cases_succ] using hsm
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hsm'
    have hvnew : v ∉ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc) := by
      intro hh
      exact hprev (Finset.mem_biUnion.mpr ⟨v, hh, hvm⟩)
    have hnew := GoodHierarchyNewMissingClosed good i (helemStar i.succ) c
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvnew⟩, hvm⟩)
    apply False.elim
    apply hmax i.succ (by simp [i]; omega)
    intro d hd
    have heq : d = c := Finset.mem_singleton.mp hd
    subst d
    exact hnew

private theorem P2813_T1_DisplayedEdges_branch_320.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (alpha beta
        : Fin k) (sigma : PartialEdgeColoring E k),
    let q := Fin.last H.dividerCount;
    let A := HierarchyStarredStage H q;
    let n := Fin.last ett.rounds;
    let Tn := ett.series.data.tree n.castSucc;
    ∀ (_ : TreeSequenceInitialSegment A T) (_ : TreeSequenceInitialSegment Tn base.core) (_ :
        StableColoring Tn (TashkinovStoredColors ett.series.data n) phi sigma) (_ : (
    ∀ (f : E) (_ : phi f ≠ some alpha) (_ : phi f ≠ some beta), sigma f = phi f)) (_ : (
    ∀ (t : Fin A.length) (_ : base.core.length ≤ (↑t : ℕ)) (c : Fin k) (_ : c = alpha ∨ c = beta)
        (_ : c ∈ TreeMissingColors phi A) (_ : phi (A.edge t) = some c), sigma (A.edge t) = phi
        (A.edge t))) (_ : (
    have n := Fin.last ett.rounds;
    have Tn := ett.series.data.tree n.castSucc;
    have Dn := TashkinovStoredColors ett.series.data n; ett.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn T ∨ (ett.series.data.kind
        n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TreeIncidentEdge Tn f ∧ (
    ∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧ TashkinovAugmentationSequence phi seed
        T)) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S T) (t : Fin A.length) (_ :
        S.length ≤ (↑t : ℕ)) (c : Fin k) (_ : phi (A.edge t) = some c), c ∈ TreeMissingColors phi
        A)) (t : Fin A.length) (_ : ¬(↑t : ℕ) < base.core.length), sigma (A.edge t) = phi (A.edge
        t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H alpha beta sigma q A n Tn hAT coreChain
      hnStable fixedValue missingEdge route augmentationMissing t ht
  have htCore : base.core.length ≤ t.val := by omega
  by_cases ha : phi (A.edge t) = some alpha
  · by_cases hm : alpha ∈ TreeMissingColors phi A
    · exact missingEdge t htCore alpha (Or.inl rfl) hm ha
    · rcases route with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
      · exact (hm (augmentationMissing Tn hseq t (le_trans coreChain.1 htCore) alpha ha)).elim
      · by_cases hs : seed.length ≤ t.val
        · exact (hm (augmentationMissing seed hseq t hs alpha ha)).elim
        · have hseedT := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
          have htSeed : t.val = Tn.length := by
            have hseedLen : seed.length = Tn.length + 1 := hseed.1
            have hcoreLen : Tn.length ≤ base.core.length := coreChain.1
            omega
          let u : Fin seed.length := ⟨t.val, by omega⟩
          have he : Fin.castLE hseedT.1 u = Fin.castLE hAT.1 t := Fin.ext rfl
          have hf : A.edge t = f := by
            rw [← hAT.2.2 t, ← he, hseedT.2.2 u]
            have hu : u = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext htSeed
            rw [hu, hseed.2.2]
          rw [hf]
          exact hnStable.1 f hincident hcontrol
  · by_cases hb : phi (A.edge t) = some beta
    · by_cases hm : beta ∈ TreeMissingColors phi A
      · exact missingEdge t htCore beta (Or.inr rfl) hm hb
      · rcases route with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
        · exact (hm (augmentationMissing Tn hseq t (le_trans coreChain.1 htCore) beta hb)).elim
        · by_cases hs : seed.length ≤ t.val
          · exact (hm (augmentationMissing seed hseq t hs beta hb)).elim
          · have hseedT := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
            have htSeed : t.val = Tn.length := by
              have hseedLen : seed.length = Tn.length + 1 := hseed.1
              have hcoreLen : Tn.length ≤ base.core.length := coreChain.1
              omega
            let u : Fin seed.length := ⟨t.val, by omega⟩
            have he : Fin.castLE hseedT.1 u = Fin.castLE hAT.1 t := Fin.ext rfl
            have hf : A.edge t = f := by
              rw [← hAT.2.2 t, ← he, hseedT.2.2 u]
              have hu : u = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext htSeed
              rw [hu, hseed.2.2]
            rw [hf]
            exact hnStable.1 f hincident hcontrol
    · exact fixedValue _ ha hb

private theorem helper_stageChain_238.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base), (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) →
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H trans j
  induction j with
  | zero =>
      intro hj i hi
      have hi0 : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
      subst i
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj i hi
      by_cases heq : i.val = j + 1
      · have heq' : i = ⟨j + 1, hj⟩ := Fin.ext heq
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      · exact trans (ih (by omega) i (by omega))
          (H.nested ⟨j, by omega⟩)

private theorem helper_starChain_264.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base), (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → (
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ))))) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ)) →
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))), r ≤ s → TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H trans stageChain starStage r s hrs
  by_cases heq : r = s
  · subst s
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · have hrlt : r.val < s.val := by
      have := Fin.le_iff_val_le_val.mp hrs
      have : r.val ≠ s.val := fun h => heq (Fin.ext h)
      omega
    have hs : s ≠ 0 := by intro hs; subst s; simp at hrlt
    have hstar : HierarchyStarredStage H s = H.stage s.castSucc := by
      rw [← Fin.succ_pred s hs]
      rfl
    rw [hstar]
    exact trans (starStage r)
      (stageChain s.val (by omega) r.succ (by simp; omega))

private theorem helper_hATy_286.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega
    ); TreeSequenceInitialSegment A T → TreeSequenceInitialSegment A Ty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H q A Ty hAT
  have hlen : A.length ≤ Ty.length := by
    change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro j
    change T.vertex _ = A.vertex j
    exact hAT.2.1 j
  · intro j
    change T.edge _ = A.edge j
    exact hAT.2.2 j

private theorem helper_maxClosed_317.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (c : Fin k),
    (∃ (r : Fin (H.dividerCount + (1 : ℕ))),
        TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c } : Finset (Fin k))) →
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))),
    TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c } : Finset (Fin k)) ∧
      ∀ (s : Fin (H.dividerCount + (1 : ℕ))),
        (↑r : ℕ) < (↑s : ℕ) →
          ¬TreeColorSetClosed G phi (HierarchyStarredStage H s) ({ c } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H c hex
  let S := Finset.univ.filter fun r : Fin (H.dividerCount + 1) =>
    TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
  have hS : S.Nonempty := by
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, by simp [S, hr]⟩
  refine ⟨S.max' hS, (Finset.mem_filter.mp (Finset.max'_mem S hS)).2, ?_⟩
  intro s hs hcl
  have hmem : s ∈ S := by simp [S, hcl]
  have hle := Finset.le_max' S s hmem
  change s.val ≤ (S.max' hS).val at hle
  omega

private theorem helper_hnStable_349.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (sigma : PartialEdgeColoring E k), (
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n; if ett.series.data.kind n
        = some TashkinovExtensionKind.PE then CombinedStableColoring Tn base.closure Dn phi sigma
        else StableColoring Tn Dn phi sigma) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; StableColoring Tn
        (TashkinovStoredColors ett.series.data n) phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base sigma hbase n Tn
  change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
    CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi sigma
    else StableColoring Tn (TashkinovStoredColors ett.series.data n) phi sigma) at hbase
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · exact (ite_eq_left hp ▸ hbase).1
  · simpa only [hp, ite_false] using hbase

private theorem helper_hqPositive_362.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (t : Fin A.length), base.core.length ≤ (↑t : ℕ) → (0 : ℕ) < H.dividerCount := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H q A t ht
  by_contra hn
  have hz : q = 0 := Fin.ext (by dsimp [q]; omega)
  have he : A = base.core := by dsimp only [A]; rw [hz]; rfl
  have hlt := t.isLt
  have hlen := congrArg TreeSequence.length he
  omega

private theorem helper_augmentationMissing_403.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → TreeSequenceInitialSegment A T →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence phi S T →
    ∀ (t : Fin A.length), S.length ≤ (↑t : ℕ) →
    ∀ (c : Fin k), phi (A.edge t) = some c → c ∈ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H q A trans hAT S hseq t ht c hcol
  let tT := Fin.castLE hAT.1 t
  obtain ⟨hlen, hinit, d, hcolor, hdm⟩ :=
    (TashkinovAugmentationSequencePosition phi S T hseq tT ht).1
  have hdcol : phi (T.edge tT) = some d := by
    convert hcolor using 1
    congr 2
  have hdc : d = c := Option.some.inj
    (hdcol.symm.trans (by rw [hAT.2.2 t]; exact hcol))
  subst d
  obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hdm
  obtain ⟨i, hi⟩ : ∃ i, (TreeSequencePrefix T tT.val
      (le_trans S.positive ht) (Nat.le_of_lt tT.isLt)).vertex i = v := by
    simpa [TreeSequenceVertexSet] using hv
  let iA : Fin (A.length + 1) := ⟨i.val, by
    have hiBound : i.val < t.val + 1 := i.isLt
    have := t.isLt
    omega⟩
  have hvA : A.vertex iA = v := by
    have hh := hAT.2.1 iA
    exact hh.symm.trans hi
  exact Finset.mem_biUnion.mpr ⟨v, by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨iA, hvA⟩, hvm⟩

theorem P2813_T1_DisplayedEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hpreStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by
        have := ett.roundsPositive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)))
    (hprefixElementary :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (alpha beta : Fin k) (z : Sum V E)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hsone : IsOneEdgeUncolored sigma e0)
    (hbase :
      let n := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma)
    (houtside :
      ∀ (r : Fin (H.dividerCount + 1)) (c : Fin k),
        (c = alpha ∨ c = beta) →
        c ∈ TreeMissingColors phi (HierarchyStarredStage H r) →
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} →
        OutsideKempeRecoloring (HierarchyStarredStage H r) phi sigma alpha beta) :
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t) := by
  classical
  have coreFixed := P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base
    sigma hone hsone hbase
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans := @SharedFacts.BaseControl.trans (@V) (@E) (@G) (@e0)
  have stageChain := @helper_stageChain_238 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@trans)
  have starStage (r : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ) := by
    clear * - H r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have starChain := @helper_starChain_264 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@trans) (@stageChain)
      (@starStage)
  have hAT : TreeSequenceInitialSegment A T := by
    have hh := starStage q
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa [hlast, H.terminalStage] using hh
  have hATy := @helper_hATy_286 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@hAT)
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have helemA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv hne'
    exact hprefixElementary
      (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) hne'
  have helemStar (r : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)) := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset
      (starChain r q (Fin.le_last r))
    intro u hu v hv hne'
    exact helemA (hsub hu) (hsub hv) hne'
  have missingSubset {B S : TreeSequence G e0} (hBS : TreeSequenceInitialSegment B S) :
      TreeMissingColors phi B ⊆ TreeMissingColors phi S := by
    intro c hc
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBS hv, hvm⟩
  have maxClosed := @helper_maxClosed_317 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H)
  have missingAtMax (c : Fin k) (hcA : c ∈ TreeMissingColors phi A)
      (r : Fin (H.dividerCount + 1))
      (hmax : ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {c}) :
      c ∈ TreeMissingColors phi (HierarchyStarredStage H r) := by
    exact @P2813_T1_DisplayedEdges_missingAtMax_188 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base H good starChain helemStar missingSubset c hcA
        r hmax
  have coreChain : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (base.parallel hp).2.2.some.leftSegment
    · rw [base.nonparallel hp]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have coreA : TreeSequenceInitialSegment base.core A := starChain 0 q (Fin.zero_le _)
  have TnA := trans coreChain coreA
  have hnStable := @helper_hnStable_349 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@sigma) (@hbase)
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    rw [hsigma]
    simp only [TwoColorComponentSwap]
    split_ifs <;> simp_all
  have hqPositive := @helper_hqPositive_362 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H)
  have missingEdge (t : Fin A.length) (ht : base.core.length ≤ t.val)
      (c : Fin k) (hc : c = alpha ∨ c = beta)
      (hm : c ∈ TreeMissingColors phi A) (hcol : phi (A.edge t) = some c) :
      sigma (A.edge t) = phi (A.edge t) := by
    have hp := hqPositive t ht
    by_cases hex : ∃ r, TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
    · obtain ⟨r, hcl, hmax⟩ := maxClosed c hex
      have hmr := missingAtMax c hm r hmax
      have havoid := (rutcor G k e0 input T phi ett base H good hp
        hprefixElementary hpreStepElementary c hm).1 hex r hcl hmax
      by_cases htr : t.val < (HierarchyStarredStage H r).length
      · let u : Fin (HierarchyStarredStage H r).length := ⟨t.val, htr⟩
        have hseg := starChain r q (Fin.le_last r)
        have he : Fin.castLE hseg.1 u = t := Fin.ext rfl
        rw [← he, hseg.2.2 u]
        have hh := OutsideKempeRecoloringStable G e0 (HierarchyStarredStage H r)
          ∅ phi sigma alpha beta hproper hone (houtside r c hc hmr hcl)
        apply hh.2.2.2.2
        obtain ⟨i, hi⟩ := (HierarchyStarredStage H r).attaches u
        refine ⟨(HierarchyStarredStage H r).vertex u.succ, ?_, ?_⟩
        · simp only [TreeSequenceVertexSet, Finset.mem_image,
            Finset.mem_univ, true_and]
          exact ⟨u.succ, rfl⟩
        · simp [Incident, hi]
      · exact False.elim (havoid (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, t, by omega, hcol⟩))
    · have hnone : ∀ r, ¬ TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} :=
        fun r hr => hex ⟨r, hr⟩
      have havoid := (rutcor G k e0 input T phi ett base H good hp
        hprefixElementary hpreStepElementary c hm).2 hnone
      exact False.elim (havoid.2.2.2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, t, le_trans coreChain.1 ht, hcol⟩))
  have route := P2813_T1_TerminalRoute G k e0 input T phi ett
  have augmentationMissing := @helper_augmentationMissing_403 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@trans)
      (@hAT)
  change ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)
  intro t
  by_cases ht : t.val < base.core.length
  · let u : Fin base.core.length := ⟨t.val, ht⟩
    have he : Fin.castLE coreA.1 u = t := Fin.ext rfl
    rw [← he, coreA.2.2 u]
    exact coreFixed u
  · exact @P2813_T1_DisplayedEdges_branch_320 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base H alpha beta sigma hAT coreChain hnStable
      fixedValue missingEdge route augmentationMissing t ht
end GoldbergSeymour

end
