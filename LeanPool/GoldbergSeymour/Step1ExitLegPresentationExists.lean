/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ElementaryClosedNoninterchangeableExitPair
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.Step1ExitLegPresentation

/-!
# Step1Exit Leg Presentation Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_orderOr_95.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : Fin
        H.dividerCount) (alpha beta : Fin k),
    let r : Fin (H.dividerCount + (1 : ℕ)) := i.succ;
    ∀ (a1 b1 a2 b2 : V) (P1 : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a1) (Sum.inl
        b1)) (P2 : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a2) (Sum.inl b2)),
        TreeExitPath (H.stage r.castSucc) phi alpha beta a1 b1 P1 → TreeExitPath (H.stage
        r.castSucc) phi alpha beta a2 b2 P2 → b1 ≠ b2 → TreeVertexOrder (H.stage r.castSucc) b1 b2
        ∨ TreeVertexOrder (H.stage r.castSucc) b2 b1 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i alpha beta r a1 b1 a2 b2 P1 P2 exit1 exit2
      treeDistinct
  simp only [TreeExitPath] at exit1 exit2
  have hmem1 := exit1.2.2.2.1
  have hmem2 := exit2.2.2.2.1
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hmem1 hmem2
  rcases hmem1 with ⟨x, hxb1⟩
  rcases hmem2 with ⟨y, hyb2⟩
  have hxy : x ≠ y := by
    intro hxy
    apply treeDistinct
    rw [← hxb1, ← hyb2, hxy]
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · left
    exact ⟨x, y, hxb1, hyb2, hlt⟩
  · right
    exact ⟨y, x, hyb2, hxb1, hgt⟩

theorem Step1ExitLegPresentationExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < H.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (i : Fin H.dividerCount) (alpha beta : Fin k)
    (halpha : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc))
    (hne : alpha ≠ beta)
    (hclosed : TreeColorSetClosed G phi
      (H.stage i.succ.castSucc) {alpha})
    (hnot : ¬ TreeInterchangeable G
      (H.stage i.succ.castSucc) phi alpha beta) :
    Nonempty (Step1ExitLegPresentation G k e0 ett.rounds H.dividerCount) := by
  let r : Fin (H.dividerCount + 1) := i.succ
  have hr : 1 ≤ r.val := by
    dsimp [r]
    omega
  obtain ⟨ettPrefix, mpPrefix, roundsPrefix, seriesPrefix, basePrefix,
    corePrefix, closurePrefix, positionPrefix, HP, countPrefix, stagesPrefix,
    dividersPrefix, goodPrefix, gammaPrefix, terminalPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 input T phi phi ett hMP base H good r hr
  have fewer : HP.dividerCount < H.dividerCount := by
    rw [countPrefix]
    omega
  have elementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (H.stage r.castSucc)) := by
    exact hfewer ettPrefix roundsPrefix mpPrefix basePrefix HP goodPrefix fewer
  have pair := ElementaryClosedNoninterchangeableExitPair G
      (H.stage r.castSucc) phi hproper elementary alpha beta hne halpha hclosed hnot
  rcases pair with ⟨a1, b1, a2, b2, P1, P2, f1, f2,
    exit1, exit2, disjoint12, outsideDistinct, treeDistinct,
    boundary1, boundary2, incident1, incident2, support1, support2⟩
  have largePrefix : 2 * ettPrefix.rounds + 11 ≤
      (TreeMissingColors phi
        (ettPrefix.series.data.tree (Fin.last ettPrefix.rounds).castSucc)).card := by
    let oldPackage : Sigma (fun n : ℕ =>
        TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
    let newPackage : Sigma (fun n : ℕ =>
        TashkinovSeries G k n e0 input) :=
      ⟨ettPrefix.rounds, ettPrefix.series⟩
    have packageEq : oldPackage = newPackage := by
      exact Sigma.ext roundsPrefix.symm seriesPrefix.symm
    have transferred :
        2 * newPackage.1 + 11 ≤
          (TreeMissingColors phi
            (newPackage.2.data.tree (Fin.last newPackage.1).castSucc)).card := by
      rw [← packageEq]
      exact hlarge
    simpa [oldPackage, newPackage] using transferred
  have terminalPrefixClosed : TreeColorSetMinusClosed G phi (H.stage r.castSucc)
      ((HierarchyTerminalStoredColors HP).biUnion
        (goodPrefix.gamma (Fin.last HP.dividerCount))) := by
    have rawStoredEq :
        (TashkinovStoredColors ettPrefix.series.data
            (Fin.last ettPrefix.rounds) \
          TreeMissingColors phi (H.stage r.castSucc)) =
        (TashkinovStoredColors ett.series.data
            (Fin.last ett.rounds) \
          TreeMissingColors phi (H.stage r.castSucc)) := by
      let oldPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
      let newPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) :=
        ⟨ettPrefix.rounds, ettPrefix.series⟩
      have hraw := congrArg (fun z =>
          (TashkinovStoredColors z.2.data (Fin.last z.1) \
            TreeMissingColors phi (H.stage r.castSucc)))
        (show oldPackage = newPackage from
          Sigma.ext roundsPrefix.symm seriesPrefix.symm)
      simpa [oldPackage, newPackage] using hraw.symm
    have terminalStoredEq : HierarchyTerminalStoredColors HP =
        HierarchyStoredColorsAt H r := by
      have hstar : HierarchyStarredStage H r = H.stage r.castSucc := by
        dsimp [HierarchyStarredStage, r]
      simpa [HierarchyTerminalStoredColors, HierarchyStoredColorsAt,
        hstar] using rawStoredEq
    have lastGammaEq : goodPrefix.gamma (Fin.last HP.dividerCount) =
        good.gamma ⟨r.val - 1, by omega⟩ := by
      have hcount : HP.dividerCount + 1 = r.val := by omega
      have hidx : Fin.last HP.dividerCount =
          Fin.cast hcount.symm ⟨r.val - 1, by omega⟩ := by
        apply Fin.ext
        simp [countPrefix]
      funext eta
      have hg := (gammaPrefix ⟨r.val - 1, by omega⟩).2 eta
      rw [hidx]
      exact hg
    rw [terminalStoredEq, lastGammaEq]
    exact terminalPrefix
  have orderOr : TreeVertexOrder (H.stage r.castSucc) b1 b2 ∨
      TreeVertexOrder (H.stage r.castSucc) b2 b1 := by
    apply helper_orderOr_95 <;> assumption
  rcases orderOr with orderForward | orderReverse
  · refine ⟨{
    input := input
    T := H.stage r.castSucc
    phi := phi
    ett := ettPrefix
    base := basePrefix
    hierarchy := HP
    good := goodPrefix
    rounds_eq := roundsPrefix
    maximum := mpPrefix
    divider_lt := fewer
    proper := hproper
    oneUncolored := hone
    large := largePrefix
    terminalMinusClosed := terminalPrefixClosed
    a := alpha
    b := beta
    a_ne_b := hne
    aMissing := halpha
    aClosed := hclosed
    a1 := a1
    b1 := b1
    a2 := a2
    b2 := b2
    P1 := P1
    P2 := P2
    exit1 := exit1
    exit2 := exit2
    disjoint12 := disjoint12
    outsideDistinct := outsideDistinct
    treeDistinct := treeDistinct
    treeOrder := orderForward
    f1 := f1
    f2 := f2
    boundary1 := boundary1
    boundary2 := boundary2
    incident1 := incident1
    incident2 := incident2
    support1 := support1
    support2 := support2
  }⟩
  · refine ⟨{
    input := input
    T := H.stage r.castSucc
    phi := phi
    ett := ettPrefix
    base := basePrefix
    hierarchy := HP
    good := goodPrefix
    rounds_eq := roundsPrefix
    maximum := mpPrefix
    divider_lt := fewer
    proper := hproper
    oneUncolored := hone
    large := largePrefix
    terminalMinusClosed := terminalPrefixClosed
    a := alpha
    b := beta
    a_ne_b := hne
    aMissing := halpha
    aClosed := hclosed
    a1 := a2
    b1 := b2
    a2 := a1
    b2 := b1
    P1 := P2
    P2 := P1
    exit1 := exit2
    exit2 := exit1
    disjoint12 := by
      intro x hx hbad
      exact (disjoint12 x hbad) hx
    outsideDistinct := outsideDistinct.symm
    treeDistinct := treeDistinct.symm
    treeOrder := orderReverse
    f1 := f2
    f2 := f1
    boundary1 := boundary2
    boundary2 := boundary1
    incident1 := incident2
    incident2 := incident1
    support1 := support2
    support2 := support1
  }⟩

end GoldbergSeymour

end
