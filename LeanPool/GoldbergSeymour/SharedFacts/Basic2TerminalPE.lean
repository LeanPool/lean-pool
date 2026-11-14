/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Shared facts for Basic2TerminalPE

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.Basic2TerminalPE

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev appearanceInStageStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (generating : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T generating),
      let _ : DecidableEq V := Classical.decEq V;
      ∀
        (_ :
          (∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
            TreeSequenceInitialSegment
              (ett.series.data.tree (⟨a, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
              (ett.series.data.tree (⟨b, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))))
        (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin ett.rounds) (x : V)
        (hxFinal : x ∈ TreeSequenceVertexSet T) (s : ℕ) (_ : (1 : ℕ) ≤ s)
        (_hsRound : s ≤ ett.rounds) (_ : ETTFirstAppearanceIndex ett x hxFinal ≤ s),
      x ∈
        TreeSequenceVertexSet
          (ett.series.data.tree (⟨s, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev earlierInPrefixStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating),
      ∀ v ∈ TreeSequenceVertexSet T,
      ∀ (_ : Fin ett.rounds) {A B : TreeSequence G e0} (x y : V), TreeSequenceInitialSegment A B → y
          ∈ TreeSequenceVertexSet A → TreeVertexOrder B x y → x ∈ TreeSequenceVertexSet A ∧
          TreeVertexOrder A x y

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev boundaryEndpointStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (sigma : PartialEdgeColoring E k) (delta : Fin k),
      let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc),
      ∀ f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree
          terminal.castSucc)) delta, Incident G x f →
      ∃ z ∉ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), G.ends f = s(x, z)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem appearanceInStage.{u_1, u_2} : appearanceInStageStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett this stageToStage v hvFinal q x hxFinal s
      hsPositive hsRound hbound
  unfold ETTFirstAppearanceIndex at hbound
  dsimp at hbound
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hnonempty : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hxFinal
  let m := candidates.min' hnonempty
  have hmBound : m.val + 1 ≤ s := by
    dsimp [m, candidates]
    convert hbound using 1
  have hmRounds : m.val < ett.rounds := by omega
  let mi : Fin ett.rounds := ⟨m.val, hmRounds⟩
  have hmEq : m = mi.castSucc := by
    apply Fin.ext
    rfl
  have hmem := Finset.min'_mem candidates hnonempty
  change m ∈ candidates at hmem
  have hxStart : x ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨m.val + 1, by omega⟩) := by
    rw [hmEq] at hmem
    have hstage : ExtendedTashkinovLadderStage ett mi.castSucc =
        ett.series.data.tree mi.succ.castSucc := by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
        (fun j => ett.series.data.tree j.succ.castSucc) mi
    have hxMi : x ∈ TreeSequenceVertexSet
        (ett.series.data.tree mi.succ.castSucc) := by
      simpa only [candidates, Finset.mem_filter, Finset.mem_univ,
        true_and, hstage] using hmem
    convert hxMi using 1
    apply congrArg TreeSequenceVertexSet
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [mi]
  exact TreeSequenceInitialSegmentVertexSetSubset
    (stageToStage (m.val + 1) s (by omega) hmBound hsRound) hxStart

/-- A common proof used by the branches of this transport or construction argument. -/
theorem earlierInPrefix.{u_1, u_2} : earlierInPrefixStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal q A B x y hAB hyA hxy
  rcases hAB with ⟨hlen, hvertices, _⟩
  rcases Finset.mem_image.mp hyA with ⟨iyA, _, hiyA⟩
  rcases hxy with ⟨ixB, iyB, hixB, hiyB, hlt⟩
  let iyCast := Fin.castLE (Nat.succ_le_succ hlen) iyA
  have hiyEq : iyB = iyCast := by
    apply B.vertex_injective
    exact hiyB.trans ((hvertices iyA).trans hiyA).symm
  have hixBound : ixB.val < A.length + 1 := by
    rw [hiyEq] at hlt
    simp [iyCast] at hlt
    omega
  let ixA : Fin (A.length + 1) := ⟨ixB.val, hixBound⟩
  have hixCast : Fin.castLE (Nat.succ_le_succ hlen) ixA = ixB := by
    apply Fin.ext
    rfl
  have hixA : A.vertex ixA = x := by
    exact (hvertices ixA).symm.trans (by simpa [hixCast] using hixB)
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨ixA, Finset.mem_univ _, hixA⟩
  · refine ⟨ixA, iyA, hixA, hiyA, ?_⟩
    rw [hiyEq] at hlt
    simpa [ixA, iyCast] using hlt

/-- A common proof used by the branches of this transport or construction argument. -/
theorem boundaryEndpoint.{u_1, u_2} : boundaryEndpointStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigma delta terminal x hx f hf hxf
  have hfBoundary := (Finset.mem_filter.mp hf).1
  rcases (by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfBoundary) with ⟨u, hu, z, hz, hends⟩
  have hxEnds : x = u ∨ x = z := by
    change x ∈ G.ends f at hxf
    rw [hends] at hxf
    simpa using hxf
  rcases hxEnds with hxu | hxz
  · exact ⟨z, hz, by simpa [hxu] using hends⟩
  · exact (hz (hxz ▸ hx)).elim

end GoldbergSeymour.SharedFacts.Basic2TerminalPE

end
