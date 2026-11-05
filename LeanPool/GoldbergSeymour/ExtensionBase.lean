/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseBranchLemmas
public import LeanPool.GoldbergSeymour.ExtensionBaseBranchPreparation
public import LeanPool.GoldbergSeymour.ExtensionBaseStoredPairOverlap

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary

/-!
# Extension Base

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open ExtensionBaseProof

theorem ExtensionBase {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ (v : V) (gamma delta : Fin k),
      ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex n = some v →
      ett.series.data.gamma n = some gamma →
      ett.series.data.delta n = some delta →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring Tn
          (TashkinovStoredColors ett.series.data n)
          (ett.series.data.coloring n) sigma →
        ∀ w, w ∈ TreeSequenceVertexSet Tn →
          (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
              (Sum.inl v) ↔ w = v) := by
  classical
  dsimp
  intro v gamma delta hterminalKind hterminalVertex hterminalGamma
    hterminalDelta sigma hsigmaProper hsigmaOne hsigmaStable w hw
  constructor
  · intro hwComponent
    apply of_not_not
    intro hwNe
    let : DecidableEq V := Classical.decEq V
    have hcurrentIII := ExtensionRules G k e0 input T generating ett hMP
      hpositive (fun lower hlowerPositive hlowerRounds hlowerMP =>
        hlower lower hlowerPositive hlowerRounds hlowerMP)
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    have hqTerminal : q.val + 1 = ett.rounds := by
      simp only [q]
      omega
    have hqSucc : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      simpa using hqTerminal
    have hqKind : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by
      rw [hqSucc]
      exact hterminalKind
    have hqVertex : ett.series.data.chosenVertex q.succ = some v := by
      rw [hqSucc]
      exact hterminalVertex
    have hqGamma : ett.series.data.gamma q.succ = some gamma := by
      rw [hqSucc]
      exact hterminalGamma
    have hqDelta : ett.series.data.delta q.succ = some delta := by
      rw [hqSucc]
      exact hterminalDelta
    have hvStage : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      exact ett.pe_chosenVertex_mem_previousTree q v hqKind hqVertex
    have hqTreeIndex : q.succ.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simpa using hqTerminal
    have hvFinal := @helper_hvFinal_2051 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hvStage) (@hqTreeIndex)
    have hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 :=
      ExtensionRulesPEFirstAppearanceBound G k e0 input T generating ett q v
        hqKind hqVertex hvFinal
    have hfirstPositive : 0 < ETTFirstAppearanceIndex ett v hvFinal := by
      unfold ETTFirstAppearanceIndex
      dsimp
      omega
    let jSlot : Fin ett.rounds :=
      ⟨ETTFirstAppearanceIndex ett v hvFinal - 1, by omega⟩
    have hjSlot : jSlot.val + 1 =
        ETTFirstAppearanceIndex ett v hvFinal := by
      simp only [jSlot]
      omega
    have hjle : jSlot.val ≤ q.val := by omega
    have hsigmaTerminal : StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ)
        (ett.series.data.coloring q.succ) sigma := by
      simpa [hqSucc] using hsigmaStable
    have hcurrentTerminal := hcurrentIII.1 q v hqKind hqVertex hvFinal
      jSlot.castSucc (by simpa using hjSlot.symm) sigma hsigmaProper hsigmaOne
      hsigmaTerminal
    have hsigmaBefore := hcurrentTerminal.1
    have segmentRefl (A : TreeSequence G e0) :
        TreeSequenceInitialSegment A A :=
      ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    have segmentTrans := @helper_segmentTrans_2087 (@V) (@E) (@G) (@e0)
    have stepSegment := @helper_stepSegment_2099 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
    have stageToStage := @helper_stageToStage_226 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentRefl) (@segmentTrans)
        (@stepSegment)
    have vertexTransfer := @helper_vertexTransfer_2114 (@V) (@E) (@G) (@e0)
    have orderRestrict := @helper_orderRestrict_1438 (@V) (@E) (@G) (@e0)
    have hLowerElementary := @helper_hLowerElementary_277 (@V) (@E) inferInstance inferInstance
         inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP)
        (@hpositive) (@hlower) (@v) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
    have hLowerPartV := @helper_hLowerPartV_179 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@stepSegment)
        (@stageToStage) (@vertexTransfer) (@orderRestrict)
    have hsupportOrder := ExtensionBaseSupportOrder ett v hvFinal q hqTerminal
      hqKind hqVertex hLowerPartV
    have hdeltaExclusion := ExtensionBaseDeltaExclusion ett v hvFinal q
      hqTerminal hqKind hqVertex jSlot hjSlot hLowerElementary hLowerPartV
    have hpairOverlap := ExtensionBaseStoredPairOverlap G k e0 input T
      generating ett v hvFinal q hqTerminal hqKind hqVertex jSlot hjSlot hMP
      hpositive hLowerElementary hLowerPartV
      (fun lower hlowerPositive hlowerRounds hlowerMP =>
        hlower lower hlowerPositive hlowerRounds hlowerMP)
    exact @helper_caseContinuation_13733 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
        (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma)
        (@hqDelta) (@hvStage) (@hqTreeIndex) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@hjSlot) (@hjle) (@hsigmaTerminal) (@hsigmaBefore) (@segmentTrans) (@stepSegment)
        (@stageToStage) (@vertexTransfer) (@hsupportOrder) (@hdeltaExclusion) (@hpairOverlap)
  · exact @helper_branch_4837 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@w) (@hw)
end GoldbergSeymour

end
