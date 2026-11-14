/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.TashTreeFourUnusedColors
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TreeColorUnusedThrough
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Tash Tree Gamma Epsilon Setup

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeGammaEpsilonSetup {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (beta : Fin k)
    (hbeta : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length))) :
    let q : Fin (T.length + 1) := ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩
    ∃ (gamma epsilon : Fin k) (m : Fin (T.length + 1)),
    gamma ≠ beta ∧
      epsilon ≠ gamma ∧
        gamma ∈ MissingColors G phi (T.vertex q) ∧
          epsilon ∈ MissingColors G phi (T.vertex m) ∧
            TreeColorUnusedThrough phi T gamma q ∧
              TreeColorUnusedThrough phi T epsilon q ∧ m.val + 2 ≤ TashTreePathIndex G T := by
  classical
  dsimp only
  let qn := TashTreePathIndex G T
  let q : Fin (T.length + 1) := ⟨qn, Nat.lt_succ_of_lt hbefore⟩
  have hbad := hmin.1
  have htriple := hbad.1
  have htash := hbad.2.1
  have hdegree : MaximumDegree G + 1 ≤ k := htriple.2.2.1
  obtain ⟨gamma, hgamma⟩ :=
    MissingColorsNonemptyOfMaximumDegree G phi hdegree (T.vertex q)
  have hgammaUnused : TreeColorUnusedThrough phi T gamma q := by
    intro r hr1 hrq hcolor
    obtain ⟨w, c, hc, hw⟩ := htash r hr1
    have hcg : c = gamma := by
      rw [hcolor] at hc
      exact Option.some.inj hc.symm
    subst c
    let P : TreeSequence G e0 :=
      TreeSequencePrefix T qn (by omega) (Nat.le_of_lt hbefore)
    have hPprefix : TreeSequenceInitialSegment P T := by
      refine ⟨Nat.le_of_lt hbefore, ?_, ?_⟩
      · intro i
        rfl
      · intro i
        rfl
    have hPelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) :=
      TashTreeProperPrefixElementary G k e0 phi T P hmin hPprefix (by
        change qn < T.length
        exact hbefore)
    have hwqval : w.val < qn := by
      change r.val < qn at hrq
      omega
    let wp : Fin (P.length + 1) :=
      ⟨w.val, by change w.val < qn + 1; omega⟩
    let qp : Fin (P.length + 1) := Fin.last qn
    have hwp : P.vertex wp = T.vertex
        (Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))) := by
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hqp : P.vertex qp = T.vertex q := by
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hwmem : P.vertex wp ∈ TreeSequenceVertexSet P := by
      simp [TreeSequenceVertexSet]
    have hqmem : P.vertex qp ∈ TreeSequenceVertexSet P := by
      simp [TreeSequenceVertexSet]
    have hwq : P.vertex wp ≠ P.vertex qp := by
      intro heq
      have hi := P.vertex_injective heq
      have hiv := congrArg Fin.val hi
      change w.val = qn at hiv
      omega
    have hdisj := hPelem hwmem hqmem hwq
    exact Finset.disjoint_left.mp hdisj (by simpa [hwp] using hw) (by
      simpa [hqp] using hgamma)
  have hgammaBeta : gamma ≠ beta := by
    intro hgb
    apply hnone
    refine ⟨beta, q, ?_, ?_, ?_, hbeta⟩
    · exact le_rfl
    · exact hbefore
    · simpa [hgb] using hgamma
  let p := qn - 2
  have hp1 : 1 ≤ p := by omega
  have hpT : p < T.length := by omega
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T p hp1 (Nat.le_of_lt hpT)
  have hfreeCard : 4 ≤ (TreeFreeColors phi P).card := by
    simpa [P] using TashTreeFourUnusedColors G k e0 phi T hmin p hp1 hpT
  let r1 : Fin T.length := ⟨qn - 2, by omega⟩
  let r2 : Fin T.length := ⟨qn - 1, by omega⟩
  let c1 : Fin k := (phi (T.edge r1)).getD gamma
  let c2 : Fin k := (phi (T.edge r2)).getD gamma
  let remaining := ((TreeFreeColors phi P).erase gamma).erase c1 |>.erase c2
  have hremaining : remaining.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcard0 : remaining.card = 0 := by simp [hempty]
    have herase1 : (TreeFreeColors phi P).card - 1 ≤
        ((TreeFreeColors phi P).erase gamma).card :=
      Finset.pred_card_le_card_erase
    have herase2 : ((TreeFreeColors phi P).erase gamma).card - 1 ≤
        (((TreeFreeColors phi P).erase gamma).erase c1).card :=
      Finset.pred_card_le_card_erase
    have herase3 :
        (((TreeFreeColors phi P).erase gamma).erase c1).card - 1 ≤
          remaining.card := by
      simpa [remaining] using
        (Finset.pred_card_le_card_erase (s :=
          ((TreeFreeColors phi P).erase gamma).erase c1) (a := c2))
    omega
  obtain ⟨epsilon, hepsilonRemaining⟩ := hremaining
  have hepsilonParts := Finset.mem_erase.mp hepsilonRemaining
  have hepsilonC2 : epsilon ≠ c2 := hepsilonParts.1
  have hepsilonParts' := Finset.mem_erase.mp hepsilonParts.2
  have hepsilonC1 : epsilon ≠ c1 := hepsilonParts'.1
  have hepsilonParts'' := Finset.mem_erase.mp hepsilonParts'.2
  have hepsilonGamma : epsilon ≠ gamma := hepsilonParts''.1
  have hepsilonFree : epsilon ∈ TreeFreeColors phi P := hepsilonParts''.2
  have hepsilonEdge1 : phi (T.edge r1) ≠ some epsilon := by
    intro heq
    apply hepsilonC1
    simp [c1, heq]
  have hepsilonEdge2 : phi (T.edge r2) ≠ some epsilon := by
    intro heq
    apply hepsilonC2
    simp [c2, heq]
  have hepsilonMissingTree : epsilon ∈ TreeMissingColors phi P := by
    exact (Finset.mem_sdiff.mp hepsilonFree).1
  rw [TreeMissingColors] at hepsilonMissingTree
  obtain ⟨v, hvP, hepsilonV⟩ := Finset.mem_biUnion.mp hepsilonMissingTree
  rw [TreeSequenceVertexSet] at hvP
  obtain ⟨mp, -, hv⟩ := Finset.mem_image.mp hvP
  let m : Fin (T.length + 1) :=
    Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt hpT)) mp
  have hPm : P.vertex mp = T.vertex m := by rfl
  have hepsilonM : epsilon ∈ MissingColors G phi (T.vertex m) := by
    rw [← hPm, hv]
    exact hepsilonV
  have hm : m.val + 2 ≤ qn := by
    change mp.val + 2 ≤ qn
    have hmplt : mp.val < P.length + 1 := mp.isLt
    change mp.val < p + 1 at hmplt
    omega
  have hepsilonUnused : TreeColorUnusedThrough phi T epsilon q := by
    intro r hr1 hrq
    by_cases hrold : r.val < p
    · have hepsilonNotUsed : epsilon ∉ TreeUsedColors phi P :=
        (Finset.mem_sdiff.mp hepsilonFree).2
      intro hcolor
      apply hepsilonNotUsed
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      let rp : Fin P.length := ⟨r.val, by change r.val < p; exact hrold⟩
      refine ⟨rp, hr1, ?_⟩
      change phi (T.edge (Fin.castLE (Nat.le_of_lt hpT) rp)) = some epsilon
      have hindex : Fin.castLE (Nat.le_of_lt hpT) rp = r := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hcolor
    · have hrCases : r.val = qn - 2 ∨ r.val = qn - 1 := by
        change r.val < qn at hrq
        change ¬ r.val < qn - 2 at hrold
        omega
      rcases hrCases with hr | hr
      · have hindex : r = r1 := by
          apply Fin.ext
          change r.val = qn - 2
          exact hr
        rw [hindex]
        exact hepsilonEdge1
      · have hindex : r = r2 := by
          apply Fin.ext
          change r.val = qn - 1
          exact hr
        rw [hindex]
        exact hepsilonEdge2
  refine ⟨gamma, epsilon, m, hgammaBeta, hepsilonGamma, ?_,
    hepsilonM, ?_, hepsilonUnused, hm⟩
  · simpa [q] using hgamma
  · simpa [q] using hgammaUnused

end GoldbergSeymour

end
