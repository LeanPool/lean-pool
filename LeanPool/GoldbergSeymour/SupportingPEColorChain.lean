/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Supporting PEColor Chain

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem SupportingPEColorChain {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V)
    (_ : u ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc))
    (indices : Fin (p + 1) → Fin rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (henumerates : ∀ j : Fin rounds,
      (j.val ≤ q.val ∧
        series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some u) ↔
      ∃ a : Fin (p + 1), indices a = j) :
    ∀ a : Fin p,
    series.data.gamma (indices a.succ).succ = series.data.delta (indices a.castSucc).succ := by
  classical
  intro a
  have leftKind := (henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩
  have rightKind := (henumerates (indices a.succ)).2 ⟨a.succ, rfl⟩
  have a_cast_value : a.castSucc.val = a.val := rfl
  have a_succ_value : a.succ.val = a.val + 1 := rfl
  have index_cast_value : (indices a.succ).castSucc.val =
      (indices a.succ).val := rfl
  have index_succ_value : (indices a.succ).succ.val =
      (indices a.succ).val + 1 := rfl
  have left_succ_value : (indices a.castSucc).succ.val =
      (indices a.castSucc).val + 1 := rfl
  generalize target_eq : (indices a.succ).succ = target
  have cert := series.certified target
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact ((Fin.succ_ne_zero (indices a.succ)) (by omega)).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have target_values := congrArg Fin.val target_eq
    simp at target_values
    have ci_eq : ci = indices a.succ := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at rightKind
    simp at rightKind
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have target_values := congrArg Fin.val target_eq
    simp at target_values
    have ci_eq : ci = indices a.succ := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at rightKind
    simp at rightKind
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have target_values := congrArg Fin.val target_eq
    simp at target_values
    have ci_eq : ci = indices a.succ := by apply Fin.ext; omega
    subst ci
    have vertex_eq : choice.vertex = u := by
      apply Option.some.inj
      exact currentVertex.symm.trans rightKind.2.2
    rcases gammaRule with ⟨_, history⟩
    rcases history with history | history
    · rcases history with ⟨h, hpos, hle, hkind, hvertex, hdelta, hmax⟩
      have hne : h ≠ 0 := by
        intro hzero
        subst h
        simp at hpos
      let predecessor : Fin rounds := h.pred hne
      have predecessor_succ : predecessor.succ = h := Fin.succ_pred h hne
      have predecessor_values := congrArg Fin.val predecessor_succ
      simp at predecessor_values
      have hright_bound : (indices a.succ).val ≤ q.val := rightKind.1
      have hd_bound : predecessor.val ≤ q.val := by omega
      have hd_kind : series.data.kind predecessor.succ =
          some TashkinovExtensionKind.PE := by
        rw [predecessor_succ]
        exact hkind
      have hd_vertex : series.data.chosenVertex predecessor.succ = some u := by
        rw [predecessor_succ]
        simpa [vertex_eq] using hvertex
      have hd_enum := (henumerates predecessor).1
        ⟨hd_bound, hd_kind, hd_vertex⟩
      rcases hd_enum with ⟨t, ht⟩
      have hpredecessor_lt : predecessor.val < (indices a.succ).val := by
        omega
      have hleft_succ_le : (indices a.castSucc).val + 1 ≤ h.val := by
        have consecutive : (indices a.castSucc).val + 1 ≤
            (indices a.succ).val := by
          have increasing := hincreasing a.castSucc a.succ (by omega)
          omega
        have hmax_value := hmax (indices a.castSucc).succ
          (by rw [left_succ_value]; omega)
          (by simpa [index_cast_value] using consecutive)
          leftKind.2.1 (by simpa [vertex_eq] using leftKind.2.2)
        simpa using hmax_value
      have hleft_le : (indices a.castSucc).val ≤ predecessor.val := by
        omega
      have ht_le : t.val ≤ a.val := by
        by_contra not_le
        have t_gt : a.val < t.val := Nat.lt_of_not_ge not_le
        by_cases same : t = a.succ
        · subst t
          rw [ht] at hpredecessor_lt
          omega
        · have order : a.succ.val < t.val := by
            have weak : a.succ.val ≤ t.val := by omega
            have different : a.succ.val ≠ t.val := by
              intro equal
              apply same
              apply Fin.ext
              omega
            exact lt_of_le_of_ne weak different
          have order_indices := hincreasing a.succ t order
          rw [ht] at order_indices
          omega
      have ha_le_t : a.val ≤ t.val := by
        by_contra not_le
        have t_lt : t.val < a.val := Nat.lt_of_not_ge not_le
        have order : t.val < a.castSucc.val := by omega
        have order_indices := hincreasing t a.castSucc order
        rw [ht] at order_indices
        omega
      have t_eq : t = a.castSucc := by
        apply Fin.ext
        omega
      have predecessor_eq : predecessor = indices a.castSucc := by
        rw [← ht, t_eq]
      have h_eq : h = (indices a.castSucc).succ := by
        rw [← predecessor_succ, predecessor_eq]
      rw [h_eq] at hdelta
      rw [currentGamma]
      exact hdelta.symm
    · exfalso
      apply history (indices a.castSucc).succ
      · exact Nat.succ_pos _
      · have increasing := hincreasing a.castSucc a.succ (by omega)
        simpa [index_cast_value] using (show (indices a.castSucc).val + 1 ≤
          (indices a.succ).val by omega)
      · exact leftKind.2.1
      · simpa [vertex_eq] using leftKind.2.2

end GoldbergSeymour

end
