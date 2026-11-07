/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionRulesEarlierIndices
public import LeanPool.GoldbergSeymour.ExtensionRulesTerminalEarlierAppearance
public import LeanPool.GoldbergSeymour.ExtensionRulesTerminalLastAppearance
public import LeanPool.GoldbergSeymour.ExtensionRulesTerminalStoredDisjoint
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# Extension Rules

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionRules {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (open scoped Classical in LowerRoundProperties lower)) :
    (∀ (q : Fin ett.rounds) (v : V),
      ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
            ∀ j : Fin (ett.rounds + 1),
              ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
                ∀ sigma : PartialEdgeColoring E k,
                  IsProperEdgeColoring G sigma →
                    IsOneEdgeUncolored sigma e0 →
                      StableColoring (ett.series.data.tree q.succ.castSucc)
                          (TashkinovStoredColors ett.series.data q.succ)
                          (ett.series.data.coloring q.succ) sigma →
                        StableColoringBeforeVertex T v hvFinal
                            (TashkinovStoredColors ett.series.data j)
                            (ett.series.data.coloring j) sigma ∧
                          (0 < j.val →
                            StableColoring (ett.series.data.tree j.castSucc)
                              (TashkinovStoredColors ett.series.data j)
                              (ett.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin ett.rounds) (vq vr : V),
    q ≠ r →
    vq ≠ vr →
    ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
    ett.series.data.chosenVertex q.succ = some vq →
    ett.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T),
    ETTFirstAppearanceIndex ett vq hvq = ETTFirstAppearanceIndex ett vr hvr →
    Disjoint (ett.series.data.stored q.succ) (ett.series.data.stored r.succ) := by
  classical
  have hLowerOne :
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), 0 < lower.rounds → lower.rounds <
        ett.rounds → MaximumProperty lower → ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T') := by
    intro T' generating' lower hp hlt hmax
    exact (hlower lower hp hlt hmax).1
  have hLowerTwo :
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), 0 < lower.rounds → lower.rounds <
        ett.rounds → MaximumProperty lower → (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + 1))
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tnext (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ alpha beta : Fin k, (alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma
        Tnext) → TreeInterchangeable G Tnext sigma alpha beta) := by
    intro T' generating' lower hp hlt hmax
    exact (hlower lower hp hlt hmax).2.1
  have hLowerThree :
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), 0 < lower.rounds → lower.rounds <
        ett.rounds → MaximumProperty lower → ((
    ∀ (q : Fin lower.rounds) (v : V), lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.chosenVertex q.succ = some v →
    ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
    ∀ j : Fin (lower.rounds + 1), ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring (lower.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        lower.series.data q.succ) (lower.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma ∧ (0 < j.val → StableColoring (lower.series.data.tree
        j.castSucc) (TashkinovStoredColors lower.series.data j) (lower.series.data.coloring j)
        sigma)) ∧
    ∀ (q r : Fin lower.rounds) (vq vr : V), q ≠ r → vq ≠ vr → lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.kind r.succ = some TashkinovExtensionKind.PE
        → lower.series.data.chosenVertex q.succ = some vq → lower.series.data.chosenVertex r.succ
        = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex lower vq hvq = ETTFirstAppearanceIndex lower vr hvr → Disjoint
        (lower.series.data.stored q.succ) (lower.series.data.stored r.succ)) := by
    intro T' generating' lower hp hlt hmax
    exact (hlower lower hp hlt hmax).2.2.1
  have hLowerFive :
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), 0 < lower.rounds → lower.rounds <
        ett.rounds → MaximumProperty lower → (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tn (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ w, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn w v)
        →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin lower.rounds) (vi : V),
        (lower.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨ lower.series.data.kind
        q.succ = some TashkinovExtensionKind.SE) → lower.series.data.chosenVertex q.succ = some vi
        → ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 → v = vi ∨ TreeVertexOrder T' v vi)
  := by
    intro T' generating' lower hp hlt hmax
    exact (hlower lower hp hlt hmax).2.2.2.2.1
  have earlier := ExtensionRulesEarlierIndices G k e0 input T generating ett
    hMP hpositive hLowerThree
  constructor
  · intro q v hkind hvertex hvFinal j hfirst sigma hproper hone hstable
    by_cases hq : q.succ = Fin.last ett.rounds
    · have hbound := ExtensionRulesPEFirstAppearanceBound G k e0
        input T generating ett q v hkind hvertex hvFinal
      have hterminal : q.val + 1 = ett.rounds := by
        have := congrArg Fin.val hq
        simpa using this
      rw [hq] at hkind hvertex hstable
      by_cases hj : j.val + 1 = ett.rounds
      · exact ExtensionRulesTerminalLastAppearance G k e0 input T generating
          ett hMP hpositive v hkind hvertex hvFinal j hfirst hj sigma hproper
          hone hstable
      · apply ExtensionRulesTerminalEarlierAppearance G k e0 input T generating
          ett hMP hpositive hLowerFive v hkind hvertex hvFinal j hfirst
          (by omega) sigma hproper hone hstable
    · exact earlier.1 q v hq hkind hvertex hvFinal j hfirst sigma hproper
        hone hstable
  · intro q r vq vr hqr hvqr hkindq hkindr hvertexq hvertexr hvq hvr hfirst
    by_cases hq : q.succ = Fin.last ett.rounds
    · rw [hq] at hkindq hvertexq ⊢
      exact ExtensionRulesTerminalStoredDisjoint G k e0 input T generating ett
        hMP hpositive hLowerOne hLowerTwo r vq vr (by
          intro hr
          apply hqr
          apply Fin.succ_injective
          exact hq.trans hr.symm) hvqr hkindq hkindr hvertexq hvertexr hvq hvr
        hfirst
    · by_cases hr : r.succ = Fin.last ett.rounds
      · rw [hr] at hkindr hvertexr ⊢
        exact (ExtensionRulesTerminalStoredDisjoint G k e0 input T generating
          ett hMP hpositive hLowerOne hLowerTwo q vr vq hq hvqr.symm hkindr hkindq
          hvertexr hvertexq hvr hvq hfirst.symm).symm
      · exact earlier.2 q r vq vr hq hr hqr hvqr hkindq hkindr hvertexq
          hvertexr hvq hvr hfirst

end GoldbergSeymour

end
