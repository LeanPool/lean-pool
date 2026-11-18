/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Preparatory lemmas for hierarchy normalization

Extracted from Wesley Pegden’s Trellis formalization of the Goldberg–Seymour
theorem at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish
properties used in the computed hierarchy records of `HierarchyClaimNinePENormalization`.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchyNormalizationLemmas

theorem helper_branch_909.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let F : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let b : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let X : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := X.hierarchy;
    let n : Fin (F.rounds + (1 : ℕ)) := Fin.last F.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let y : V := T.vertex (Fin.last T.length); F.series.data.kind n = some
        TashkinovExtensionKind.PE → A = b.core → alpha ∈ TreeMissingColors mu A →
    let D : Finset (Fin k) := HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)));
    let R : Finset (Fin k) := D.biUnion (X.good.gamma (0 : Fin (X.hierarchy.dividerCount + (1 :
        ℕ))));
    ∀ beta ∉ R, alpha ∉ R → beta ∈ TreeMissingColors mu A →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu beta alpha (Sum.inl y);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 F sigma T) (bs : HierarchyBase
        corr.replacementETT sigma) (K : TashkinovHierarchy corr.replacementETT bs), bs.core = A →
        (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = bs.core) → (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), K.stage j.succ = T) → H.stage (Fin.succ (0 : Fin
        (H.dividerCount + (1 : ℕ)))) = T → (
    ∀ (f : E) (c : Fin k), c ≠ beta → c ≠ alpha → (sigma f = some c ↔ mu f = some c)) → (
    ∀ (eta : Fin k), eta ≠ beta → eta ≠ alpha → HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta) →
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt K j,
    ∀ ⦃c : Fin k⦄, c ∈ X.good.gamma (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ))) eta → eta ∈ D →
        c ∈ HierarchyStageMissingColors X.hierarchy (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ)))
        \ HierarchySegmentColors X.hierarchy (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ))) eta →
        c ∉ HierarchySegmentColors K j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu F b X H n A y hp hA haA D R beta
      hbR haRnot hbA sigma corr bs K coreEq starK termK termH unaffectedValue firstEq j eta heta
      c hcg hetaD hold hseg
  have hn : eta ∉ TreeMissingColors mu A := by
    have hn := (Finset.mem_sdiff.mp hetaD).2
    change eta ∉ TreeMissingColors mu b.core at hn
    rwa [← hA] at hn
  have heb : eta ≠ beta := by intro h; subst eta; exact hn hbA
  have hea : eta ≠ alpha := by intro h; subst eta; exact hn haA
  have hcR : c ∈ R := Finset.mem_biUnion.mpr ⟨eta, hetaD, hcg⟩
  have hcb : c ≠ beta := by intro h; subst c; exact hbR hcR
  have hca : c ≠ alpha := by intro h; subst c; exact haRnot hcR
  have hfirst := firstEq eta heb hea
  change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (K.stage j.succ).length,
    (HierarchyStarredStage K j).length ≤ r.val ∧
      r.val < min (HierarchyFirstMissingPosition sigma T eta).val (K.stage j.succ).length ∧
      sigma ((K.stage j.succ).edge r) = some c) at hseg
  rw [starK j, coreEq, termK j, hfirst] at hseg
  obtain ⟨r, hr, hp, hcol⟩ := (Finset.mem_filter.mp hseg).2
  apply (Finset.mem_sdiff.mp hold).2
  change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (H.stage (0 : Fin (H.dividerCount +
      1)).succ).length,
    b.core.length ≤ r.val ∧
      r.val < min (HierarchyFirstMissingPosition mu T eta).val (H.stage (0 : Fin (H.dividerCount
          + 1)).succ).length ∧
      mu ((H.stage (0 : Fin (H.dividerCount + 1)).succ).edge r) = some c)
  rw [termH, ← hA]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hp, (unaffectedValue _ c hcb hca).1 hcol⟩

end GoldbergSeymour.HierarchyNormalizationLemmas

end
