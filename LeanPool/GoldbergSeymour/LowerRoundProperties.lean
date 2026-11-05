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
# Lower-round induction properties

The six conclusions of the extension-round induction: elementarity,
interchangeability, stability, separation, defective-colour order and recolouring.
The input colouring and tree are parameters, so the same package can be used
with both fixed-input and unrestricted induction hypotheses.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The complete six-part property proved at an extension-induction stage. -/
def LowerRoundProperties {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input' : PartialEdgeColoring E k}
  {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
  (lower : ExtendedTashkinovTree G k e0 input' T' generating') : Prop :=
 ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T') ∧
  (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
   let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + 1))
   ∀ sigma : PartialEdgeColoring E k,
    IsProperEdgeColoring G sigma →
     IsOneEdgeUncolored sigma e0 →
      StableColoring Tnext (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
       ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext) →
         TreeInterchangeable G Tnext sigma alpha beta) ∧
   ((∀ (q : Fin lower.rounds) (v : V),
      lower.series.data.kind q.succ = some TashkinovExtensionKind.PE →
       lower.series.data.chosenVertex q.succ = some v →
        ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
         ∀ j : Fin (lower.rounds + 1),
          ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
           ∀ sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
              StableColoring (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ) (lower.series.data.coloring q.succ)
                sigma →
               StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors lower.series.data j)
                 (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                 StableColoring (lower.series.data.tree j.castSucc)
                  (TashkinovStoredColors lower.series.data j) (lower.series.data.coloring j)
                  sigma)) ∧
     ∀ (q r : Fin lower.rounds) (vq vr : V),
      q ≠ r →
       vq ≠ vr →
        lower.series.data.kind q.succ = some TashkinovExtensionKind.PE →
         lower.series.data.kind r.succ = some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some vq →
           lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
             ETTFirstAppearanceIndex lower vq hvq = ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ) (lower.series.data.stored r.succ)) ∧
    (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
     let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
     ∀ (v : V) (gamma delta : Fin k),
      lower.series.data.kind n = some TashkinovExtensionKind.PE →
       lower.series.data.chosenVertex n = some v →
        lower.series.data.gamma n = some gamma →
         lower.series.data.delta n = some delta →
          ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma →
            IsOneEdgeUncolored sigma e0 →
             StableColoring Tn (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
              ∀ w,
               w ∈ TreeSequenceVertexSet Tn →
                (Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v)) ∧
     (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
      ∀ sigma : PartialEdgeColoring E k,
       IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 →
         StableColoring Tn (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
          ∀ (delta : Fin k),
           DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
            ∀ (v : V),
             BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
              (∃ w,
                BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin lower.rounds) (vi : V),
                (lower.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
                  lower.series.data.kind q.succ = some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                  ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                   v = vi ∨ TreeVertexOrder T' v vi) ∧
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
      ∀ sigma : PartialEdgeColoring E k,
       IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 →
         StableColoring Tn (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
          ModColoring lower sigma)

end GoldbergSeymour

end
