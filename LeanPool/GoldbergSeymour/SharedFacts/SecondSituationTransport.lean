/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BaseDisplayedEdges
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior

/-!
# Shared facts for HierarchySituationTwoSubcaseThreeTwo

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.SecondSituationTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev apositiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      (0 : ℕ) < H.dividerCount →
      A =
        H.stage
          (⟨H.dividerCount, by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev aTStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      ((0 : ℕ) < H.dividerCount →
          A =
            H.stage
              (⟨H.dividerCount,
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin (H.dividerCount + (2 : ℕ)))) →
      (H.dividerCount = (0 : ℕ) → A = base.core) →
      TreeSequenceInitialSegment A T

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev aBStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let B : TreeSequence G e0 :=
        HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
      (2 : ℕ) ≤ T.length - A.length →
      B.length + (1 : ℕ) = T.length →
      ((0 : ℕ) < H.dividerCount →
          A =
            H.stage
              (⟨H.dividerCount,
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin (H.dividerCount + (2 : ℕ)))) →
      (H.dividerCount = (0 : ℕ) → A = base.core) →
      TreeSequenceInitialSegment A T →
      TreeSequenceInitialSegment A B

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstWitnessStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
        (k : ℕ) (e0 : E) (T : TreeSequence G e0) (rho : PartialEdgeColoring E k)
        (X : TreeSequence G e0),
      TreeSequenceInitialSegment X T →
      ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev missingSubsetStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
        (k : ℕ) (e0 : E) (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
      TreeMissingColors rho X ⊆ TreeMissingColors rho Y

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstPreservedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base),
      let B : TreeSequence G e0 :=
        HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
      TreeSequenceInitialSegment B T →
      (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
          TreeSequenceInitialSegment X T →
            ∀ c ∈ TreeMissingColors rho X,
              c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
                (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
      ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
      (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstUnaffectedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
        (k : ℕ) (e0 : E) (T : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k)
        (a b c : Fin k),
      a ≠ b →
      IsProperEdgeColoring G rho →
      c ≠ a →
      c ≠ b →
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y F : TreeSequence G e0},
      TreeSequenceInitialSegment X F →
      TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length →
      TreeSequenceInitialSegment X Y

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev predecessorIncidentStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E)
        (e0 : E) (T X : TreeSequence G e0),
      TreeSequenceInitialSegment X T →
      ∀ (t : Fin T.length),
      (↑t : ℕ) = X.length →
      TreeIncidentEdge X (T.edge t)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev seedStableStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
        {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho)
        (K : TashkinovHierarchy ett' base'),
      HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
      K.dividerCount = (0 : ℕ) →
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev weakEdgesStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
        {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old)
        (K : TashkinovHierarchy ett' base'),
      HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
      IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
      ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
      new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
        old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstAfterStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      TreeSequenceInitialSegment A T →
      ∀ (rho : PartialEdgeColoring E k),
      ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
      c ∉ TreeMissingColors rho A →
      A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem apositive.{u_1, u_2} : apositiveStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hq
  have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp [q]
    omega
  change HierarchyStarredStage H q = _
  rw [hi]
  simp only [HierarchyStarredStage, Fin.cases_succ]
  congr 1
  apply Fin.ext
  simp
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem aT.{u_1, u_2} : aTStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hApositive hAzero
  by_cases hz : H.dividerCount = 0
  · have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := by apply Fin.ext; simp [hz]
    simpa [hAzero hz, hi, H.terminalStage] using H.coreInsideFirst
  · rw [hApositive (Nat.pos_of_ne_zero hz)]
    have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
        q.castSucc := Fin.ext rfl
    have hj : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    simpa only [hi, hj] using H.nested q

/-- A common proof used by the branches of this transport or construction argument. -/
theorem aB.{u_1, u_2} : aBStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A B htail hBlen hApositive hAzero hAT
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hAT.2.1 i
  · intro i
    exact hAT.2.2 i

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstWitness.{u_1, u_2} : firstWitnessStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 T rho X hXT c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hvc⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G rho (T.vertex j)
    have hi : Fin.castLE (Nat.succ_le_succ hXT.1) i ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hXT.2.1 i]
      exact hvc
    have hn : candidates.Nonempty := ⟨_, hi⟩
    have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hle := Finset.min'_le candidates _ hi
    have hib := i.isLt
    unfold HierarchyFirstMissingPosition
    change (c ∈ MissingColors G rho (T.vertex (if h : candidates.Nonempty then
      candidates.min' h else Fin.last T.length))) ∧ _
    rw [dite_eq_left hn]
    refine ⟨hm, ?_⟩
    change (candidates.min' hn).val ≤ i.val at hle
    omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem missingSubset.{u_1, u_2} : missingSubsetStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 rho X Y hXY
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hm⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstPreserved.{u_1, u_2} : firstPreservedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C B hBT firstWitness rho sigma c helem hmiss hc
  as_aux_lemma =>
    clear_value B
    clear * - G T B rho sigma c helem hmiss hc firstWitness hBT
    have hr := firstWitness rho B hBT c hc
    have hc' : c ∈ TreeMissingColors sigma B := by
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
    have hs := firstWitness sigma B hBT c hc'
    have pref (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
        T.vertex i ∈ TreeSequenceVertexSet B := by
      let j : Fin (B.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
      have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨j, Finset.mem_univ _, (hBT.2.1 j).symm.trans (congrArg T.vertex he)⟩
    by_contra hne
    have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
        T.vertex (HierarchyFirstMissingPosition rho T c) :=
      fun he => hne (T.vertex_injective he)
    have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
    exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstUnaffected.{u_1, u_2} : firstUnaffectedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 T z rho a b c hne hp hca hcb
  let _ := Fintype.ofFinite V
  have hb := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
  have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
      c ∈ MissingColors G (TwoColorComponentSwap G rho a b z) (T.vertex i)) =
      (Finset.univ.filter fun i : Fin (T.length + 1) =>
        c ∈ MissingColors G rho (T.vertex i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2.2.2 _ c hca hcb
  unfold HierarchyFirstMissingPosition
  rw [he]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem comparableInitialSegments.{u_1, u_2} : comparableInitialSegmentsStatement.{u_1, u_2} := by
  classical
  intro V E G e0 X Y F hXF hYF hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro i
    exact (hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXF.2.1 i)
  · intro i
    exact (hYF.2.2 (Fin.castLE hXY i)).symm.trans (hXF.2.2 i)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem predecessorIncident.{u_1, u_2} : predecessorIncidentStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G e0 T X hXT t ht
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨i, hi⟩ := T.attaches t
  let j : Fin (X.length + 1) := ⟨i.val, by have := i.isLt; omega⟩
  have he : Fin.castLE (Nat.succ_le_succ hXT.1) j =
      Fin.castLE (by omega : t.val + 1 ≤ T.length + 1) i := Fin.ext rfl
  refine ⟨X.vertex j, (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  rw [← hXT.2.1 j, he, Incident, hi]
  exact Sym2.mem_mk_right _ _

/-- A common proof used by the branches of this transport or construction argument. -/
theorem seedStable.{u_1, u_2} : seedStableStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 T input' rho sigma ett' base' K hw hq
  have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hq
  rw [hi] at hw
  change (if ett'.series.data.kind (Fin.last ett'.rounds) =
      some TashkinovExtensionKind.PE then _ else _) at hw
  split_ifs at hw with hpe
  · exact hw.1
  · exact hw

/-- A common proof used by the branches of this transport or construction argument. -/
theorem weakEdges.{u_1, u_2} : weakEdgesStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 T input' old new ett' base' K hw ho hno
  by_cases hz : K.dividerCount = 0
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
    rw [hi] at hw ⊢
    exact P2813_T1_BaseDisplayedEdges G k e0 input' T old ett' base' new ho hno hw
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
        (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
      Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
    rw [hi] at hw ⊢
    intro t
    have hinv := hw.2
    by_cases ht : 1 ≤ t.val
    · exact hinv.1 t ht
    · let S := HierarchyStarredStage K
        (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ
      have he : t = ⟨0, S.positive⟩ := Fin.ext (by change t.val = 0; omega)
      rw [he, S.first_edge, hno.1, ho.1]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstAfter.{u_1, u_2} : firstAfterStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hAT rho c hc hn
  by_contra h
  have hi : (HierarchyFirstMissingPosition rho T c).val ≤ A.length := Nat.le_of_not_gt h
  let i : Fin (A.length + 1) := ⟨(HierarchyFirstMissingPosition rho T c).val, by omega⟩
  have he : Fin.castLE (Nat.succ_le_succ hAT.1) i =
      HierarchyFirstMissingPosition rho T c := Fin.ext rfl
  apply hn
  refine Finset.mem_biUnion.mpr ⟨A.vertex i, (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i,
      Finset.mem_univ _, rfl⟩, ?_⟩
  rw [← hAT.2.1 i, he]
  exact hc

end GoldbergSeymour.SharedFacts.SecondSituationTransport

end
