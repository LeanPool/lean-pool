/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ChangeLemmaBothOutsidePreparation1

public import LeanPool.GoldbergSeymour.SharedFacts.MixedChangeTransport.Preparation1
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

/-!
# Shared facts for ChangeLemmaMixedClosedFinal

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.MixedChangeTransport

/-- A common proof used by the branches of this transport or construction argument. -/
alias initialSegmentTransitive :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.initialSegmentTransitive

alias comparableInitialSegments :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.comparableInitialSegments

/-- A common proof used by the branches of this transport or construction argument. -/
theorem stageInitialSegment.{u_1, u_2} : stageInitialSegmentStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H segRefl segTrans a d hbound
  induction d with
  | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
  | succ d ih =>
    exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem stageInitialSegmentOfFinalTree.{u_1, u_2} :
    stageInitialSegmentOfFinalTreeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H stageSegment j
  have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
  have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
      Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
    Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
  simpa [he, H.terminalStage] using hs

/-- A common proof used by the branches of this transport or construction argument. -/
theorem lastStagePositive.{u_1, u_2} : lastStagePositiveStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hz
  obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
    exact (hz hv).elim
  · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simpa [q] using hv.symm

/-- A common proof used by the branches of this transport or construction argument. -/
theorem coreInitialSegmentOfStarredStage.{u_1, u_2} :
    coreInitialSegmentOfStarredStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segRefl segTrans stageSegment lastZero
      lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segRefl _
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

/-- A common proof used by the branches of this transport or construction argument. -/
theorem terminalStageInitialSegmentOfCore.{u_1, u_2} :
    terminalStageInitialSegmentOfCoreStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base n Tn segRefl
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · exact (Classical.choice (base.parallel hp).2.2).leftSegment
  · rw [base.nonparallel hp]
    exact segRefl _

/-- A common proof used by the branches of this transport or construction argument. -/
theorem starredStageInitialSegmentOfFinalTree.{u_1, u_2} :
    starredStageInitialSegmentOfFinalTreeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segTrans stageToT lastZero lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
  · rw [lastPositive hz]
    exact stageToT _

/-- A common proof used by the branches of this transport or construction argument. -/
theorem ordinaryStageInitialSegmentOfStarredStage.{u_1, u_2} :
    ordinaryStageInitialSegmentOfStarredStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn stageSegment lastZero lastPositive
      TnToA j
  by_cases hz : H.dividerCount = 0
  · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
    rw [hj, H.baseStage]
    exact TnToA
  · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
    rw [lastPositive hz]
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
      simp only [Fin.val_castSucc]; omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstMissingPositionWitness.{u_1, u_2} : firstMissingPositionWitnessStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A ell yLength Y YToT c hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨i, hi⟩ := hv
  let it := Fin.castLE (Nat.succ_le_succ YToT.1) i
  have hci : c ∈ MissingColors G phi (T.vertex it) := by
    rw [YToT.2.1 i, hi]
    exact hcv
  let candidates := Finset.univ.filter fun j => c ∈ MissingColors G phi (T.vertex j)
  have hit : it ∈ candidates := by simp [candidates, hci]
  have hnon : candidates.Nonempty := ⟨it, hit⟩
  have hmem := Finset.min'_mem candidates hnon
  have hle := Finset.min'_le candidates it hit
  refine ⟨?_, ?_⟩
  · simpa [HierarchyFirstMissingPosition, candidates, hnon] using
      (Finset.mem_filter.mp hmem).2
  · have hiv : it.val ≤ Y.length := Nat.le_of_lt_succ i.isLt
    have hval : (candidates.min' hnon).val ≤ it.val := hle
    simpa [HierarchyFirstMissingPosition, candidates, hnon] using le_trans hval hiv

/-- A common proof used by the branches of this transport or construction argument. -/
theorem missingPositionOutsidePrefix.{u_1, u_2} : missingPositionOutsidePrefixStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A AToT i hi
  by_contra h
  have hle : i.val ≤ A.length := by omega
  apply hi
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨i.val, by omega⟩, (AToT.2.1 ⟨i.val, by omega⟩).symm⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem colorNotMissingOnStarredStage.{u_1, u_2} :
    colorNotMissingOnStarredStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ell yLength Y hElementaryY
      AToY c i hmi hiy hia
  clear * - hmi hiy hia AToY hElementaryY
  intro hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hne : v ≠ T.vertex i := by intro he; exact hia (he ▸ hv)
  exact (Finset.disjoint_left.mp
    (hElementaryY (TreeSequenceInitialSegmentVertexSetSubset AToY hv) hiy hne)) hcv hmi

/-- A common proof used by the branches of this transport or construction argument. -/
theorem distinctMissingPositionIndices.{u_1, u_2} :
    distinctMissingPositionIndicesStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta ia ib horder
  obtain ⟨i, j, hi, hj, hij⟩ := horder.1
  have hei := T.vertex_injective hi
  have hej := T.vertex_injective hj
  simpa [hei, hej] using hij

/-- A common proof used by the branches of this transport or construction argument. -/
theorem prefixStrictlyShorterThanFinalTree.{u_1, u_2} :
    prefixStrictlyShorterThanFinalTreeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib ell yLength Y AToT hAib B
      ABstrict BToY
  clear * - AToT BToY ABstrict Y
  have hAT := AToT.1
  have hY : Y.length = min (A.length + (T.length - A.length - 1)) T.length := rfl
  have hBY := BToY.1
  have hAB := ABstrict
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem pathMissing.{u_1, u_2} : pathMissingStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k phi hproper v c d hcd hc
  let _ := Fintype.ofFinite V
  refine ⟨hcd, Sum.inl v, rfl, ?_⟩
  intro x hx y hy
  cases x with
  | inr f =>
    cases y with
    | inr g =>
      have hfc : phi f = some d := hx.2.resolve_left (by
        intro he
        exact (Finset.mem_sdiff.mp hc).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hx.1, he⟩))
      have hgc : phi g = some d := hy.2.resolve_left (by
        intro he
        exact (Finset.mem_sdiff.mp hc).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hy.1, he⟩))
      congr 1
      by_contra hfg
      exact hproper hfg ⟨v, hx.1, hy.1⟩ hfc hgc
    | inl w => exact False.elim hy
  | inl w => exact False.elim hx

/-- A common proof used by the branches of this transport or construction argument. -/
theorem otherColorsUnaffected.{u_1, u_2} : otherColorsUnaffectedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ib vb ell yLength Y ha hb
      K sigma f c hca hcb
  clear * - hca hcb K sigma hne
  by_cases hf : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · simp [sigma, TwoColorComponentSwap, K, hf, ha, hca.symm, hcb.symm]
    · by_cases hb : phi f = some beta
      · simp [sigma, TwoColorComponentSwap, K, hf, hb, hne.symm,
          hca.symm, hcb.symm]
      · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb]
  · simp [sigma, TwoColorComponentSwap, K, hf]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem swappedColoringOneUncolored.{u_1, u_2} : swappedColoringOneUncoloredStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta hne H q A ib vb ell yLength Y
      ha hb K sigma unaffected
  clear * - hone sigma K unaffected hne
  refine ⟨?_, ?_⟩
  · simp [sigma, TwoColorComponentSwap, hone.1]
  · intro f hf
    obtain ⟨c, hc⟩ := hone.2 f hf
    by_cases ha : c = alpha
    · subst c
      by_cases hK : Sum.inr f ∈ K
      · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
    · by_cases hb : c = beta
      · subst c
        by_cases hK : Sum.inr f ∈ K
        · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
        · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨c, (unaffected f c ha hb).mpr hc⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem notMissingBeforeFirstPosition.{u_1, u_2} :
    notMissingBeforeFirstPositionStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ia ib va vb ell yLength Y
      hElementaryY ha hb haY hbY hAib B BToY K sigma haK behavior edgeOfVertex v hv hvb
  by_cases hvK : Sum.inl v ∈ K
  · have hva : v ≠ va := by intro he; exact haK (he ▸ hvK)
    have hvY := TreeSequenceInitialSegmentVertexSetSubset BToY hv
    have han : alpha ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY haY hva) hc ha.1
    have hbn : beta ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY hbY hvb) hc hb.1
    have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
      simpa [MissingColors, PresentColors] using han
    have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
      simpa [MissingColors, PresentColors] using hbn
    obtain ⟨fa, hfa, hfca⟩ := hpa
    obtain ⟨fb, hfb, hfcb⟩ := hpb
    have hfaK := edgeOfVertex hvK hfa (Or.inl hfca)
    have hfbK := edgeOfVertex hvK hfb (Or.inr hfcb)
    have hnewa : sigma fb = some alpha := by
      simp [sigma, TwoColorComponentSwap, K, hfbK, hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      simp [sigma, TwoColorComponentSwap, K, hfaK, hfca]
    have hana : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fb, hfb, hnewa⟩
    have hbnb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp [hana, han]
    · by_cases hcb : c = beta
      · subst c; simp [hbnb, hbn]
      · exact behavior.2.2.2 v c hca hcb
  · exact behavior.1 v hvK

/-- A common proof used by the branches of this transport or construction argument. -/
theorem routeTransport.{u_1, u_2} : routeTransportStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb segTrans hAib B BToT
      sigma missingBefore edgesFixed S hs
  unfold TashkinovAugmentationSequence at hs ⊢
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head U W hstep htail ih =>
    have hWB := TashkinovAugmentationSequenceInitialSegment phi W B htail
    obtain ⟨hlen, hUW, c, hcol, hm⟩ := hstep
    have hUB := segTrans hUW hWB
    have hlt : U.length < B.length := by have := hWB.1; omega
    refine Relation.ReflTransGen.head ⟨hlen, hUW, c, ?_, ?_⟩ ih
    · have hf := edgesFixed (Fin.castLE hWB.1 (Fin.cast hlen.symm (Fin.last U.length)))
      rw [hWB.2.2] at hf
      exact hf.trans hcol
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      have hvB := TreeSequenceInitialSegmentVertexSetSubset hUB hv
      have hvb : v ≠ vb := by
        intro he
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
        obtain ⟨i, hi⟩ := hv
        have ht := hUB.2.1 i
        have htT := BToT.2.1 (Fin.castLE (Nat.succ_le_succ hUB.1) i)
        have eqv : T.vertex (Fin.castLE (Nat.succ_le_succ BToT.1)
            (Fin.castLE (Nat.succ_le_succ hUB.1) i)) = T.vertex ib := htT.trans (ht.trans
                (hi.trans he))
        have hh := congrArg Fin.val (T.vertex_injective eqv)
        have := i.isLt
        change i.val = ib.val at hh
        change U.length < ib.val at hlt
        omega
      exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [missingBefore v hvB hvb]; exact hcv⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem storedColorsAtReplacementStage.{u_1, u_2} :
    storedColorsAtReplacementStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB ettB sigma treeMissingEq corr
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
  rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
  cases hr
  have heq : series = newSeries := eq_of_heq hs
  cases heq
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
  have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
  have hm := treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
  unfold Dn TashkinovStoredColors
  simp only [ettB, hstored, ← hgen, ← ett.generatingColoring, htree, hm, n, Tn]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem replacementStageInitialSegmentOfPrefix.{u_1, u_2} :
    replacementStageInitialSegmentOfPrefixStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib segRefl segTrans hAib B rpB
      aboveB strictB belowB genB baseB HB j
  clear * - HB j B segRefl segTrans
  exact Fin.reverseInduction
    (motive := fun j => TreeSequenceInitialSegment (HB.stage j) B)
    (by simpa only [HB.terminalStage] using segRefl B)
    (fun i hi => segTrans (HB.nested i) hi) j

/-- A common proof used by the branches of this transport or construction argument. -/
theorem closureInitialSegmentOfStarredStage.{u_1, u_2} :
    closureInitialSegmentOfStarredStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n ib coreToA hAib B rpB aboveB
      strictB belowB genB baseB hcoreB hp
  clear * - hp baseB coreToA hcoreB
  obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hp
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToA
  rw [← hcoreB, u.vertexSet]
  exact Finset.mem_union_right _ hv

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstMissingPositionEquality.{u_1, u_2} : firstMissingPositionEqualityStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B BToT sigma
      missingBefore firstLe firstStrict eta
  have beforeLast (i : Fin (B.length + 1)) (hi : i.val < B.length) :
      MissingColors G sigma (B.vertex i) = MissingColors G phi (B.vertex i) := by
    apply missingBefore
    · simp [TreeSequenceVertexSet]
    · intro he
      have heT := (BToT.2.1 i).trans he
      have heval := congrArg Fin.val (T.vertex_injective heT)
      have hbLen : B.length = ib.val := rfl
      change i.val = ib.val at heval
      omega
  apply Fin.ext
  apply Nat.le_antisymm
  · by_cases h : (HierarchyFirstMissingPosition phi B eta).val < B.length
    · apply firstLe sigma eta
      rw [beforeLast _ h]
      exact firstStrict phi eta h
    · have := (HierarchyFirstMissingPosition sigma B eta).isLt
      omega
  · by_cases h : (HierarchyFirstMissingPosition sigma B eta).val < B.length
    · apply firstLe phi eta
      rw [← beforeLast _ h]
      exact firstStrict sigma eta h
    · have := (HierarchyFirstMissingPosition phi B eta).isLt
      omega

end GoldbergSeymour.SharedFacts.MixedChangeTransport

end
