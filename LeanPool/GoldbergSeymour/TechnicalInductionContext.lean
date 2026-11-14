/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorVertex
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex

public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.ModColoring

public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex

public import LeanPool.GoldbergSeymour.TreeInterchangeable

/-!
# Technical Induction Context

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
The lower-round and current-round properties available to the simultaneous technical induction. -/
structure TechnicalInductionContext {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E) (n : Nat) where
  lowerOne :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett →
        ColoredVertexSetElementary G generating (TreeSequenceVertexSet T)
  lowerTwo :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tnext : TreeSequence G e0 := ett.series.data.tree (Fin.last (ett.rounds + 1))
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tnext (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma →
    ∀ alpha beta : Fin k, (alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma
        Tnext) → TreeInterchangeable G Tnext sigma alpha beta
  lowerThree :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett → ((
    ∀ (q : Fin ett.rounds) (v : V), ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v →
    ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
    ∀ j : Fin (ett.rounds + 1), ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧ (0 < j.val → StableColoring (ett.series.data.tree
        j.castSucc) (TashkinovStoredColors ett.series.data j) (ett.series.data.coloring j) sigma))
        ∧
    ∀ (q r : Fin ett.rounds) (vq vr : V), q ≠ r → vq ≠ vr → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some vq → ett.series.data.chosenVertex r.succ = some
        vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett vq hvq = ETTFirstAppearanceIndex ett vr hvr → Disjoint
        (ett.series.data.stored q.succ) (ett.series.data.stored r.succ))
  lowerFour :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ (v : V) (gamma delta : Fin k), ett.series.data.kind terminal = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex terminal = some v →
        ett.series.data.gamma terminal = some gamma → ett.series.data.delta terminal = some delta
        →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma →
    ∀ w, w ∈ TreeSequenceVertexSet Tterminal → (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
        (Sum.inl v) ↔ w = v)
  lowerFive :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma →
    ∀ delta : Fin k, DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta →
    ∀ v : V, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tterminal) delta v → (exists w,
        BoundaryColorVertex G sigma (TreeSequenceVertexSet Tterminal) delta w ∧ TreeVertexOrder
        Tterminal w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V), (ett.series.data.kind
        q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ = some
        TashkinovExtensionKind.SE) → ett.series.data.chosenVertex q.succ = some vi →
        ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 → v = vi ∨ TreeVertexOrder T v vi
  lowerSix :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), 0 < ett.rounds → ett.rounds < n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma → ModColoring ett sigma
  currentThree :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), ett.rounds = n → MaximumProperty ett → ((
    ∀ (q : Fin ett.rounds) (v : V), ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v →
    ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
    ∀ j : Fin (ett.rounds + 1), ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧ (0 < j.val → StableColoring (ett.series.data.tree
        j.castSucc) (TashkinovStoredColors ett.series.data j) (ett.series.data.coloring j) sigma))
        ∧
    ∀ (q r : Fin ett.rounds) (vq vr : V), q ≠ r → vq ≠ vr → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some vq → ett.series.data.chosenVertex r.succ = some
        vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett vq hvq = ETTFirstAppearanceIndex ett vr hvr → Disjoint
        (ett.series.data.stored q.succ) (ett.series.data.stored r.succ))
  currentFour :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), ett.rounds = n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ (v : V) (gamma delta : Fin k), ett.series.data.kind terminal = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex terminal = some v →
        ett.series.data.gamma terminal = some gamma → ett.series.data.delta terminal = some delta
        →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma →
    ∀ w, w ∈ TreeSequenceVertexSet Tterminal → (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
        (Sum.inl v) ↔ w = v)
  currentFive :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), ett.rounds = n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma →
    ∀ delta : Fin k, DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta →
    ∀ v : V, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tterminal) delta v → (exists w,
        BoundaryColorVertex G sigma (TreeSequenceVertexSet Tterminal) delta w ∧ TreeVertexOrder
        Tterminal w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V), (ett.series.data.kind
        q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ = some
        TashkinovExtensionKind.SE) → ett.series.data.chosenVertex q.succ = some vi →
        ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 → v = vi ∨ TreeVertexOrder T v vi
  currentSix :
    ∀ {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
        {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T
        generating), ett.rounds = n → MaximumProperty ett →
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tterminal : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tterminal (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma → ModColoring ett sigma

end GoldbergSeymour

end
