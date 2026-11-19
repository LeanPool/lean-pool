/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Interchangeability at a nonparallel penultimate tree

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A nonparallel final extension makes a missing color interchangeable on the penultimate tree. -/
theorem ExtendedTashkinovTree.nonparallel_interchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k e0 input T phi)
    (maximum : MaximumProperty ett) (proper : IsProperEdgeColoring G phi)
    (one : IsOneEdgeUncolored phi e0)
    (induction : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE)
    (c d : Fin k)
    (missing : c ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∨
      d ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) :
    TreeInterchangeable G (ett.series.data.tree (Fin.last ett.rounds).castSucc) phi c d := by
  classical
  have positive : 0 < ett.rounds := lt_of_lt_of_le Nat.zero_lt_one ett.roundsPositive
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := positive; omega)
  have hprev : StableColoring Tn
      (TashkinovStoredColors ett.series.data j.castSucc)
      (ett.series.data.coloring j.castSucc) phi := by
    have step := ett.series.certified n
    generalize hi : n = i at step
    cases step with
    | initial =>
      have hv := congrArg Fin.val hi
      simp [n] at hv
      have := positive
      omega
    | SE ji _ _ _ _ _ choice _ coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hj, Tn, hc] using choice.selectedStable
    | RE ji _ _ _ _ available coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      refine ⟨?_, ?_⟩
      · intro f _ _
        exact congrFun hc f
      · intro v _
        exact congrArg (fun psi => MissingColors G psi v) hc
    | PE ji _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper
        one stored edges kind vertex outside delta gammaEq closure ordered strict =>
      exact (nonparallel (by simpa [← hi] using kind)).elim
  have hm : c ∈ TreeMissingColors phi Tn ∨ d ∈ TreeMissingColors phi Tn := missing
  by_cases hn : 1 < ett.rounds
  · obtain ⟨lower, hr, hmax, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett maximum
        (ett.rounds - 1) (by omega) (by omega)
    let nl : Fin (lower.rounds + 1) := Fin.last lower.rounds
    have hcidx : Fin.castLE (by omega) nl = j.castSucc :=
      Fin.ext (by simp [nl, j, hr])
    have htidx : Fin.castLE (by omega) (Fin.last (lower.rounds + 1)) =
        n.castSucc := Fin.ext (by simp [n, hr]; omega)
    have ht : lower.series.data.tree (Fin.last (lower.rounds + 1)) = Tn :=
      (htrees _).trans (congrArg ett.series.data.tree htidx)
    obtain ⟨hc, _, _, _, _, _, _, _, hd, _⟩ := hdata nl
    rw [hcidx] at hc hd
    have hs : StableColoring
        (lower.series.data.tree (Fin.last (lower.rounds + 1)))
        (TashkinovStoredColors lower.series.data nl)
        (lower.series.data.coloring nl) phi := by
      rw [ht, hc, hd]
      exact hprev
    have hi := (induction lower (by omega) (by omega) hmax).2.1
      phi proper one hs c d (by rw [ht]; exact hm)
    simpa only [ht] using hi
  · have hn1 : ett.rounds = 1 := by have := positive; omega
    have hj0 : j.castSucc = (0 : Fin (ett.rounds + 1)) :=
      Fin.ext (by simp [j, hn1])
    have ht1 : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn1])
    have hs : StableColoring (ett.series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors ett.series.data 0)
        (ett.series.data.coloring 0) phi := by
      simpa only [Tn, ht1, hj0] using hprev
    have hi := (TechnicalTheoremBase G k ett.rounds e0 input ett.series).2
      phi proper one hs c d
      (by simpa only [Tn, ht1] using hm)
    have hTn1 : Tn = ett.series.data.tree ⟨1, by omega⟩ :=
      congrArg ett.series.data.tree ht1
    change TreeInterchangeable G Tn phi c d
    rw [hTn1]
    exact hi

end GoldbergSeymour

end
