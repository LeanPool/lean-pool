/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePathNumberBounds
public import LeanPool.GoldbergSeymour.HierarchySituationOneImpossible
public import LeanPool.GoldbergSeymour.HierarchySituationTwoImpossible
public import LeanPool.GoldbergSeymour.HierarchySituationThreeImpossible
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# Good Hierarchy Elementary Large

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch670Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (q : ℕ), (
    ∀ m < q,
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi), MaximumProperty ett →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) → H.dividerCount = m →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) →
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi) (H :
        TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) →
    let candidate : ℕ → ℕ → Prop := fun (a b : ℕ) =>
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0) (generating' :
        PartialEdgeColoring E k) (other : ExtendedTashkinovTree G k e0 input' T' generating')
        (base' : HierarchyBase other generating') (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds ∧ C'.hierarchy.dividerCount = q ∧ HierarchyCounterexampleMeasure
        C' = (a, b); (
    ∃ (a : ℕ) (b : ℕ), candidate a b) →
    ∀ (firstExists :
    ∃ (a : ℕ) (b : ℕ), candidate a b),
    let first : ℕ := Nat.find firstExists; (
    ∃ (b : ℕ), candidate first b) →
    ∀ (inputMin : PartialEdgeColoring E k) (TMin : TreeSequence G e0) (generatingMin :
        PartialEdgeColoring E k) (ettMin : ExtendedTashkinovTree G k e0 inputMin TMin
        generatingMin) (baseMin : HierarchyBase ettMin generatingMin) (CMin :
        HierarchyCounterexample baseMin), ettMin.rounds = ett.rounds → CMin.hierarchy.dividerCount
        = q →
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating'), other.rounds = ettMin.rounds → MaximumProperty other →
    ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base') (_ :
        GoodHierarchy K), K.dividerCount < CMin.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')

private abbrev helperCtx623Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (q : ℕ), (
    ∀ m < q,
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi), MaximumProperty ett →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) → H.dividerCount = m →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) →
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi) (H :
        TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) →
    let candidate : ℕ → ℕ → Prop := fun (a b : ℕ) =>
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0) (generating' :
        PartialEdgeColoring E k) (other : ExtendedTashkinovTree G k e0 input' T' generating')
        (base' : HierarchyBase other generating') (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds ∧ C'.hierarchy.dividerCount = q ∧ HierarchyCounterexampleMeasure
        C' = (a, b); (
    ∃ (a : ℕ) (b : ℕ), candidate a b) →
    ∀ (firstExists :
    ∃ (a : ℕ) (b : ℕ), candidate a b),
    let first : ℕ := Nat.find firstExists; (
    ∃ (b : ℕ), candidate first b) →
    ∀ (inputMin : PartialEdgeColoring E k) (TMin : TreeSequence G e0) (generatingMin :
        PartialEdgeColoring E k) (ettMin : ExtendedTashkinovTree G k e0 inputMin TMin
        generatingMin) (baseMin : HierarchyBase ettMin generatingMin) (CMin :
        HierarchyCounterexample baseMin), ettMin.rounds = ett.rounds → CMin.hierarchy.dividerCount
        = q → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T' generating'}
        {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
        other.rounds = ettMin.rounds → C'.hierarchy.dividerCount = CMin.hierarchy.dividerCount →
        ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure CMin)) →
        HierarchyMinimumCounterexampleContext G k e0 inputMin TMin generatingMin ettMin baseMin
        CMin

private abbrev helperBranch281Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (q : ℕ), (
    ∀ m < q,
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi), MaximumProperty ett →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) → H.dividerCount = m →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) →
    ∀ (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi), MaximumProperty ett →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        (open scoped Classical in LowerRoundProperties lower)) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current → ((
    ∀ (q : Fin current.rounds) (v : V), current.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (current.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (current.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        current.series.data q.succ) (current.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (current.series.data.tree j.castSucc) (TashkinovStoredColors current.series.data j)
        (current.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin current.rounds) (vq vr : V), q ≠ r → vq ≠ vr → current.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → current.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → current.series.data.chosenVertex q.succ = some vq →
        current.series.data.chosenVertex r.succ = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex current vq hvq = ETTFirstAppearanceIndex current vr hvr → Disjoint
        (current.series.data.stored q.succ) (current.series.data.stored r.succ)) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (v : V) (gamma delta : Fin k), current.series.data.kind n = some TashkinovExtensionKind.PE →
        current.series.data.chosenVertex n = some v → current.series.data.gamma n = some gamma →
        current.series.data.delta n = some delta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v)
        ↔ w = v) ∧ (
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma →
    ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ (w : V), BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn
        w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin current.rounds) (vi : V),
        current.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        current.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        current.series.data.chosenVertex q.succ = some vi → ETTFirstAppearanceIndex current v
        hvFinal ≤ (↑q : ℕ) + (1 : ℕ) → v = vi ∨ TreeVertexOrder T' v vi) ∧
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn (TashkinovStoredColors current.series.data n)
        (current.series.data.coloring n) sigma → ModColoring current sigma) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base') (_ :
        GoodHierarchy K),
    let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
    let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc; (2 : ℕ) * current.rounds +
        (11 : ℕ) ≤ (TreeMissingColors generating' Tn).card) → H.dividerCount = q →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)

private theorem helper_minMinimal_526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (q : ℕ) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base),
    let candidate : ℕ → ℕ → Prop := fun (a b : ℕ) =>
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0) (generating' :
        PartialEdgeColoring E k) (other : ExtendedTashkinovTree G k e0 input' T' generating')
        (base' : HierarchyBase other generating') (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds ∧ C'.hierarchy.dividerCount = q ∧ HierarchyCounterexampleMeasure
        C' = (a, b); (
    ∃ (a : ℕ) (b : ℕ), candidate a b) →
    ∀ (firstExists :
    ∃ (a : ℕ) (b : ℕ), candidate a b),
    let first : ℕ := Nat.find firstExists;
    ∀ (firstSpec :
    ∃ (b : ℕ), candidate first b),
    let second : ℕ := Nat.find firstSpec;
    ∀ (inputMin : PartialEdgeColoring E k) (TMin : TreeSequence G e0) (generatingMin :
        PartialEdgeColoring E k) (ettMin : ExtendedTashkinovTree G k e0 inputMin TMin
        generatingMin) (baseMin : HierarchyBase ettMin generatingMin) (CMin :
        HierarchyCounterexample baseMin), ettMin.rounds = ett.rounds → CMin.hierarchy.dividerCount
        = q → HierarchyCounterexampleMeasure CMin = (first, second) →
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T' generating'}
        {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
        other.rounds = ettMin.rounds → C'.hierarchy.dividerCount = CMin.hierarchy.dividerCount →
        ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure CMin) := by
  classical
  intro V E _ _ _ _ G k e0 q input T phi ett base H candidate candidateExists firstExists first
      firstSpec second inputMin TMin generatingMin ettMin baseMin CMin roundsMin dividerMin
      measureMin input' T' generating' other base' C' hround hdiv
  unfold HierarchyCounterexampleLess
  rw [measureMin] at ⊢
  have hroundQ : other.rounds = ett.rounds := hround.trans roundsMin
  have hdivQ : C'.hierarchy.dividerCount = q := hdiv.trans dividerMin
  by_cases hfirst : (HierarchyCounterexampleMeasure C').1 < first
  · have firstWitness : ∃ b, candidate
        (HierarchyCounterexampleMeasure C').1 b := by
        exact ⟨(HierarchyCounterexampleMeasure C').2,
          ⟨input', T', generating', other, base', C', hroundQ, hdivQ, rfl⟩⟩
    have := Nat.find_min' firstExists firstWitness
    omega
  · by_cases heq : (HierarchyCounterexampleMeasure C').1 = first
    · by_cases hsecond : (HierarchyCounterexampleMeasure C').2 < second
      · have := Nat.find_min' firstSpec (show candidate first
            (HierarchyCounterexampleMeasure C').2 from by
            exact ⟨input', T', generating', other, base', C', hroundQ, hdivQ,
              Prod.ext heq rfl⟩)
        omega
      · omega
    · omega

private theorem helper_branch_670.{u_1, u_2} :
    helperBranch670Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 q ih input T phi ett base H hgood hlower hcurrent hlarge candidate
      candidateExists firstExists first firstSpec inputMin TMin generatingMin ettMin baseMin CMin
      roundsMin dividerMin input' T' generating' other hround hmax base' K good less
  have lowerOther := fun {input'' : PartialEdgeColoring E k}
      {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input'' T'' generating'')
      (hp : 0 < lower.rounds) (hl : lower.rounds < other.rounds)
      (hm : MaximumProperty lower) =>
    @hlower _ _ _ lower hp (by omega) hm
  have currentOther := fun {input'' : PartialEdgeColoring E k}
      {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input'' T'' generating'')
      (heq : current.rounds = other.rounds) (hm : MaximumProperty current) =>
    hcurrent current (by omega) hm
  have largeOther := fun {input'' : PartialEdgeColoring E k}
      {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input'' T'' generating'')
      (heq : current.rounds = other.rounds) (hm : MaximumProperty current)
      (base'' : HierarchyBase current generating'')
      (K'' : TashkinovHierarchy current base'') (good'' : GoodHierarchy K'') =>
    hlarge current (by omega) hm base'' K'' good''
  unfold ColoredVertexSetElementary
  intro u hu v hv huv
  exact (ih K.dividerCount (by omega) (input := input') (T := T')
    (phi := generating') (ett := other) hmax (base := base') (H := K)
    good lowerOther currentOther largeOther (by rfl)) hu hv huv

private theorem helper_ctx_623.{u_1, u_2} :
    helperCtx623Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 q ih input T phi ett base H hgood hlower hcurrent hlarge
      candidate candidateExists firstExists first firstSpec inputMin TMin generatingMin ettMin
      baseMin CMin roundsMin dividerMin minMinimal
  refine
    { proper := ?_
      oneEdgeUncolored := ?_
      lowerRung := ?_
      fewerDividers := ?_
      lexicographicMinimality := ?_
      largeMissingSet := ?_ }
  · exact ettMin.coloringProperties.1
  · exact ettMin.coloringProperties.2
  · intro input' T' generating' lower positiveLower lowerLess maximumLower
    exact @hlower _ _ _ lower positiveLower (by omega) maximumLower
  · exact @helper_branch_670 V E inferInstance inferInstance inferInstance inferInstance G k e0 q
      ih input T phi ett base H hgood hlower hcurrent hlarge candidateExists firstExists
      firstSpec inputMin TMin generatingMin ettMin baseMin CMin roundsMin dividerMin
  · exact minMinimal
  · exact hlarge ettMin roundsMin CMin.maximum baseMin CMin.hierarchy CMin.good

private theorem helper_branch_281.{u_1, u_2} :
    helperBranch281Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 q ih input T phi ett hMP base H hgood hlower hcurrent hlarge hq
  by_contra hne
  let counter : HierarchyCounterexample base :=
    { positive := ett.roundsPositive
      hierarchy := H
      good := hgood
      maximum := hMP
      notElementary := hne }
  let candidate : ℕ → ℕ → Prop := fun a b =>
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0)
      (generating' : PartialEdgeColoring E k)
      (other : ExtendedTashkinovTree G k e0 input' T' generating')
      (base' : HierarchyBase other generating')
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds ∧
      C'.hierarchy.dividerCount = q ∧
      HierarchyCounterexampleMeasure C' = (a, b)
  have candidateExists : ∃ a b, candidate a b := by
    refine ⟨(HierarchyCounterexampleMeasure counter).1,
      (HierarchyCounterexampleMeasure counter).2, ?_⟩
    exact ⟨input, T, phi, ett, base, counter, rfl, by
      simpa [counter] using hq, rfl⟩
  have firstExists : ∃ a, ∃ b, candidate a b := candidateExists
  let first : ℕ := Nat.find firstExists
  have firstSpec : ∃ b, candidate first b := Nat.find_spec firstExists
  let second : ℕ := Nat.find firstSpec
  have secondSpec : candidate first second := Nat.find_spec firstSpec
  obtain ⟨inputMin, TMin, generatingMin, ettMin, baseMin, CMin,
    roundsMin, dividerMin, measureMin⟩ := secondSpec
  have minCounter : HierarchyCounterexample baseMin := CMin
  have minMinimal :=
    @helper_minMinimal_526 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 q input T phi ett base H candidateExists firstExists firstSpec inputMin TMin
        generatingMin ettMin baseMin CMin roundsMin dividerMin measureMin
  have ctx :=
    @helper_ctx_623 V E inferInstance inferInstance inferInstance inferInstance G k e0 q ih
        input T phi ett base H hgood hlower hcurrent hlarge candidateExists firstExists
        firstSpec inputMin TMin generatingMin ettMin baseMin CMin roundsMin dividerMin minMinimal
  have missing (mu : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G mu)
      (_ : IsOneEdgeUncolored mu e0) (v : V) : (MissingColors G mu v).Nonempty := by
    apply MissingColors.nonempty_of_degree_lt G mu v
    have triple : KTriple G k e0 input := by
      cases ett.series.certified 0 with
      | initial triple => exact triple
    have degreeBound : Degree G v ≤ MaximumDegree G := by
      unfold MaximumDegree
      exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_image.mpr ⟨v, by simp⟩)))
    have paletteBound := triple.2.2.1
    omega
  have lower := HierarchyCounterexampleTailAtLeastTwo G k e0 inputMin TMin generatingMin ettMin
      baseMin CMin
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  dsimp at lower
  have pathBounds := HierarchyCounterexamplePathNumberBounds G k e0 inputMin TMin generatingMin
    ettMin baseMin CMin ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  dsimp at pathBounds
  have pathAtLeast : 1 ≤ HierarchyPathNumber CMin.hierarchy := pathBounds.1
  have pathAtMost : HierarchyPathNumber CMin.hierarchy ≤
      HierarchyFullTailLength CMin := pathBounds.2
  by_cases onePath : HierarchyPathNumber CMin.hierarchy = 1
  · exact HierarchySituationOneImpossible G k e0 inputMin TMin generatingMin
      ettMin baseMin CMin ctx onePath missing
  · by_cases fullPath : HierarchyPathNumber CMin.hierarchy = HierarchyFullTailLength CMin
    · exact HierarchySituationTwoImpossible G k e0 inputMin TMin generatingMin
        ettMin baseMin CMin ctx fullPath
    · have pathLower : 2 ≤ HierarchyPathNumber CMin.hierarchy := by omega
      have pathUpper : HierarchyPathNumber CMin.hierarchy < HierarchyFullTailLength CMin := by omega
      exact HierarchySituationThreeImpossible G k e0 inputMin TMin generatingMin
        ettMin baseMin CMin ctx pathLower pathUpper missing

theorem GoodHierarchyElementaryLarge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hgood : GoodHierarchy H)
    (hlower : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < ett.rounds -> MaximumProperty lower ->
      (open scoped Classical in LowerRoundProperties lower))
    (hcurrent : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      ((forall (q : Fin current.rounds) (v : V),
        current.series.data.kind q.succ =
            some TashkinovExtensionKind.PE ->
        current.series.data.chosenVertex q.succ = some v ->
        forall hvFinal : v ∈ TreeSequenceVertexSet T',
        forall j : Fin (current.rounds + 1),
          ETTFirstAppearanceIndex current v hvFinal = j.val + 1 ->
          forall sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma ->
            IsOneEdgeUncolored sigma e0 ->
            StableColoring
              (current.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors current.series.data q.succ)
              (current.series.data.coloring q.succ) sigma ->
            StableColoringBeforeVertex T' v hvFinal
                (TashkinovStoredColors current.series.data j)
                (current.series.data.coloring j) sigma ∧
              (0 < j.val ->
                StableColoring (current.series.data.tree j.castSucc)
                  (TashkinovStoredColors current.series.data j)
                  (current.series.data.coloring j) sigma)) ∧
        forall (q r : Fin current.rounds) (vq vr : V),
          q ≠ r -> vq ≠ vr ->
          current.series.data.kind q.succ =
              some TashkinovExtensionKind.PE ->
          current.series.data.kind r.succ =
              some TashkinovExtensionKind.PE ->
          current.series.data.chosenVertex q.succ = some vq ->
          current.series.data.chosenVertex r.succ = some vr ->
          forall (hvq : vq ∈ TreeSequenceVertexSet T')
            (hvr : vr ∈ TreeSequenceVertexSet T'),
            ETTFirstAppearanceIndex current vq hvq =
                ETTFirstAppearanceIndex current vr hvr ->
            Disjoint (current.series.data.stored q.succ)
              (current.series.data.stored r.succ)) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall (v : V) (gamma delta : Fin k),
         current.series.data.kind n = some TashkinovExtensionKind.PE ->
         current.series.data.chosenVertex n = some v ->
         current.series.data.gamma n = some gamma ->
         current.series.data.delta n = some delta ->
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma ->
           IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn
             (TashkinovStoredColors current.series.data n)
             (current.series.data.coloring n) sigma ->
           forall w, w ∈ TreeSequenceVertexSet Tn ->
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) ↔ w = v)) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tn
           (TashkinovStoredColors current.series.data n)
           (current.series.data.coloring n) sigma ->
         forall (delta : Fin k),
           DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta ->
           forall (v : V),
             BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                 delta v ->
             (exists w, BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tn) delta w ∧
               TreeVertexOrder Tn w v) ->
             forall (hvFinal : v ∈ TreeSequenceVertexSet T')
               (q : Fin current.rounds) (vi : V),
               (current.series.data.kind q.succ =
                    some TashkinovExtensionKind.PE ∨
                  current.series.data.kind q.succ =
                    some TashkinovExtensionKind.SE) ->
               current.series.data.chosenVertex q.succ = some vi ->
               ETTFirstAppearanceIndex current v hvFinal ≤ q.val + 1 ->
               v = vi ∨ TreeVertexOrder T' v vi) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tn
           (TashkinovStoredColors current.series.data n)
           (current.series.data.coloring n) sigma ->
         ModColoring current sigma))
    (_ : 11 ≤ TashkinovOrder G)
    (hlarge : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'),
        GoodHierarchy K ->
        let n : Fin (current.rounds + 1) := Fin.last current.rounds
        let Tn := current.series.data.tree n.castSucc
        2 * current.rounds + 11 ≤
          (TreeMissingColors generating' Tn).card) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := by
  classical
  induction hq : H.dividerCount using Nat.strong_induction_on
      generalizing input T phi ett base H hgood with
  | h q ih =>
      exact @helper_branch_281 V E inferInstance inferInstance inferInstance inferInstance G k e0
          q ih input T phi ett hMP base H hgood hlower hcurrent hlarge hq
end GoldbergSeymour

end
