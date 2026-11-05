/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreeProperInitialSegmentRankLess
public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Tash Tree Suffix Terminal Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hproper_118.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T →
    ∀ (beta : Fin k) (p : Fin T.length), G.ends (T.edge p) = s(T.vertex p.castSucc, T.vertex
        p.succ) → beta ∉ PresentColors G phi (T.vertex p.castSucc) → beta ∉ PresentColors G phi
        (T.vertex p.succ) →
    let phiStar : PartialEdgeColoring E k := fun (e : E) => if e = T.edge p then some beta else
        phi e; IsProperEdgeColoring G phiStar := by
  classical
  intro V E _ _ _ G k e0 phi T hmin beta p hend hbetaPrev hbetaLast phiStar e f c hef hadj hec
  by_cases hep : e = T.edge p
  · subst e
    simp only [phiStar, ite_eq_left rfl] at hec
    have hcbeta : c = beta := Option.some.inj hec.symm
    subst c
    have hcf : f ≠ T.edge p := by
      intro h
      exact hef h.symm
    have hnot : phi f ≠ some beta := by
      rcases hadj with ⟨v, hve, hvf⟩
      unfold Incident at hve hvf
      rw [hend] at hve
      simp only [Sym2.mem_iff] at hve
      rcases hve with hve | hve
      · intro hf
        apply hbetaPrev
        rw [hve] at hvf
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, hvf, hf⟩
      · intro hf
        apply hbetaLast
        rw [hve] at hvf
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, hvf, hf⟩
    simpa [phiStar, hcf] using hnot
  · have hphi : phi e = some c := by simpa [phiStar, hep] using hec
    have hnotold : phi f ≠ some c := hmin.1.1.2.2.2.1 hef hadj hphi
    by_cases hfp : f = T.edge p
    · subst f
      simp only [phiStar, ite_eq_left rfl]
      intro heq
      have hcbeta : c = beta := (Option.some.inj heq).symm
      subst c
      rcases hadj with ⟨v, hve, hvf⟩
      unfold Incident at hve hvf
      rw [hend] at hvf
      simp only [Sym2.mem_iff] at hvf
      rcases hvf with hvf | hvf
      · rw [hvf] at hve
        exact hbetaPrev
            (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, hve, hphi⟩)
      · rw [hvf] at hve
        exact hbetaLast
            (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, hve, hphi⟩)
    · simpa [phiStar, hfp] using hnotold

private theorem helper_hTashS_213.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T →
    ∀ (beta : Fin k) (p : Fin T.length) (hpone : (1 : ℕ) ≤ (↑p : ℕ)) (hple : (↑p : ℕ) ≤ T.length)
        (_ : Fin ((↑p : ℕ) + (1 : ℕ))),
    let phiStar : PartialEdgeColoring E k := fun (e : E) => if e = T.edge p then some beta else
        phi e; (
    ∀ (a : Fin (T.length + (1 : ℕ))), (↑a : ℕ) < (↑p : ℕ) →
    ∀ c ∈ MissingColors G phi (T.vertex a), c ∈ MissingColors G phiStar (T.vertex a)) →
    let S : TreeSequence G e0 := TreeSequencePrefix T (↑p : ℕ) hpone hple; TashkinovTree G e0
        phiStar S := by
  classical
  intro V E _ _ _ G k e0 phi T hmin beta p hpone hple j phiStar missingPreserved S r hr
  have hrlt : r.val < p.val := by
    dsimp [S, TreeSequencePrefix] at r hr ⊢
    omega
  have hT := hmin.1.2.1 (Fin.castLE hple r) (by
    dsimp [S, TreeSequencePrefix] at hr
    exact hr)
  rcases hT with ⟨a, c, hcol, hmiss⟩
  refine ⟨a, c, ?_, ?_⟩
  · dsimp [S, TreeSequencePrefix] at hcol ⊢
    have hedge_ne : T.edge (Fin.castLE hple r) ≠ T.edge p := by
      intro hh
      have hi := T.edge_injective hh
      have hv : (Fin.castLE hple r).val = p.val := congrArg Fin.val hi
      have hrval : (Fin.castLE hple r).val = r.val := rfl
      exact (Nat.ne_of_lt hrlt) (hrval ▸ hv)
    simpa [phiStar, hedge_ne] using hcol
  · have ha_lt : a.val < p.val := by
      have hrval : (Fin.castLE hple r).val = r.val := rfl
      have hrcast : (Fin.castLE hple r).val < p.val := hrval ▸ hrlt
      have har : a.val ≤ (Fin.castLE hple r).val := Nat.le_of_lt_succ a.isLt
      omega
    have hrval : (Fin.castLE hple r).val = r.val := rfl
    have hrcast : (Fin.castLE hple r).val < p.val := hrval ▸ hrlt
    have haP : a.val < p.val + 1 := by
      exact Nat.lt_trans a.isLt (Nat.succ_lt_succ hrcast)
    let q : Fin (p.val + 1) := Fin.castLT a haP
    let b : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hple) q
    have hb_lt : b.val < p.val := by
      have hbval : b.val = a.val := rfl
      rw [hbval]
      omega
    have hmissT : c ∈ MissingColors G phi (T.vertex b) := by
      change c ∈ MissingColors G phi (T.vertex b) at hmiss
      exact hmiss
    have hmiss' := missingPreserved b hb_lt c hmissT
    change c ∈ MissingColors G phiStar (S.vertex q)
    dsimp [S, TreeSequencePrefix]
    exact hmiss'

private theorem helper_hnotElemS_281.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (beta : Fin k) (p : Fin T.length) (hp : (↑p : ℕ) + (1 : ℕ) = T.length) (hpone : (1 :
        ℕ) ≤ (↑p : ℕ)) (hple : (↑p : ℕ) ≤ T.length) (delta : Fin k) (j : Fin ((↑p : ℕ) + (1 : ℕ)))
        (hjlt : (↑j : ℕ) < (↑p : ℕ)),
    let phiStar : PartialEdgeColoring E k := fun (e : E) => if e = T.edge p then some beta else
        phi e;
    let S : TreeSequence G e0 := TreeSequencePrefix T (↑p : ℕ) hpone hple; delta ∈ MissingColors G
        phiStar (T.vertex (j.castLT (Decidable.byContradiction fun (a : ¬(↑j : ℕ) < T.length + (1
        : ℕ)) =>
    by
                omega
    ))) → delta ∈ MissingColors G phiStar (T.vertex p.castSucc) → ¬ColoredVertexSetElementary G
        phiStar (TreeSequenceVertexSet S) := by
  classical
  intro V E _ _ _ G k e0 phi T beta p hp hpone hple delta j hjlt phiStar S hdeltaJ hdeltaP helem
  let _ := Fintype.ofFinite V
  let qj : Fin (p.val + 1) := Fin.castLT j j.isLt
  let qlast : Fin (p.val + 1) := Fin.last p.val
  have hmemj : T.vertex (Fin.castLE (Nat.succ_le_succ hple) qj) ∈
      TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    refine ⟨qj, Finset.mem_univ _, ?_⟩
    dsimp [S, TreeSequencePrefix]
  have hmemlast : T.vertex (Fin.castLE (Nat.succ_le_succ hple) qlast) ∈
      TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    refine ⟨qlast, Finset.mem_univ _, ?_⟩
    dsimp [S, TreeSequencePrefix]
  have hnevertices : T.vertex (Fin.castLE (Nat.succ_le_succ hple) qj) ≠
      T.vertex (Fin.castLE (Nat.succ_le_succ hple) qlast) := by
    intro heq
    have hidx := T.vertex_injective heq
    have hval := congrArg Fin.val hidx
    have hqjlt : qj.val < p.val := by
      change j.val < p.val
      exact hjlt
    have hqlast : qlast.val = p.val := by
      change p.val = p.val
      rfl
    have heqval : qj.val = qlast.val := by simpa using hval
    omega
  have hdis := helem hmemj hmemlast hnevertices
  rw [Finset.disjoint_left] at hdis
  have hdeltaAj : delta ∈ MissingColors G phiStar
      (T.vertex (Fin.castLE (Nat.succ_le_succ hple) qj)) := by
    simpa [Fin.castLE, Fin.castLT, qj] using hdeltaJ
  have hdeltaAlast : delta ∈ MissingColors G phiStar
      (T.vertex (Fin.castLE (Nat.succ_le_succ hple) qlast)) := by
    have hidx : Fin.castLE (Nat.succ_le_succ hple) qlast = p.castSucc := by
      apply Fin.ext
      change p.val = p.val
      rfl
    rw [hidx]
    exact hdeltaP
  exact hdis hdeltaAj hdeltaAlast

theorem TashTreeSuffixTerminalReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (beta : Fin k) (p : Fin T.length)
    (hq : TashTreePathIndex G T ≤ p.val)
    (hp : p.val + 1 = T.length)
    (hprev : beta ∈ MissingColors G phi (T.vertex p.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ (hpos : 1 ≤ p.val) (hle : p.val ≤ T.length) (delta : Fin k) (j : Fin (p.val + 1))
      (phiStar : PartialEdgeColoring E k),
    phi (T.edge p) = some delta ∧
      j.val < p.val ∧
        delta ∈ MissingColors G phi (T.vertex (Fin.castLT j (by omega))) ∧
          phiStar = (fun e => if e = T.edge p then some beta else phi e) ∧
            TashTreeBadPair G k e0 phiStar (TreeSequencePrefix T p.val hpos hle) ∧
              TashTreeRankLess G (TreeSequencePrefix T p.val hpos hle) T := by
  classical
  have hpone : 1 ≤ p.val := by omega
  have hple : p.val ≤ T.length := p.isLt.le
  have hsuffix :
      TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hend : G.ends (T.edge p) = s(T.vertex p.castSucc, T.vertex p.succ) := by
    exact hsuffix.2.2 p hq
  have hedge0 : T.edge p ≠ e0 := by
    intro he
    have hfirst : T.edge ⟨0, T.positive⟩ = e0 := T.first_edge
    have hzero : p = ⟨0, T.positive⟩ :=
      T.edge_injective (he.trans hfirst.symm)
    have hval := congrArg Fin.val hzero
    simp at hval
    omega
  have hdelta : ∃ delta : Fin k, phi (T.edge p) = some delta := by
    rcases hmin.1.1.2.2.2.2 with hone
    exact hone.2 (T.edge p) hedge0
  rcases hdelta with ⟨delta, hdelta⟩
  rcases hmin.1.2.1 p hpone with ⟨j, c, hcolor, hmissing⟩
  have hcdelta : c = delta := by
    exact Option.some.inj (hcolor.symm.trans hdelta)
  subst c
  have hjlt : j.val < p.val := by
    by_contra hj
    have hjle : p.val ≤ j.val := Nat.le_of_not_gt hj
    have hjeq : j.val = p.val := by omega
    have hincident : Incident G (T.vertex (Fin.castLT j
        (Nat.lt_trans j.isLt (Nat.succ_lt_succ p.isLt)))) (T.edge p) := by
      unfold Incident
      rw [show Fin.castLT j
          (Nat.lt_trans j.isLt (Nat.succ_lt_succ p.isLt)) = p.castSucc by
            apply Fin.ext
            simp [hjeq]]
      rw [hend]
      simp
    have hpresent : delta ∈ PresentColors G phi
        (T.vertex (Fin.castLT j
          (Nat.lt_trans j.isLt (Nat.succ_lt_succ p.isLt)))) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨T.edge p, hincident, hdelta⟩
    have hnotpresent : delta ∉ PresentColors G phi
        (T.vertex (Fin.castLT j
          (Nat.lt_trans j.isLt (Nat.succ_lt_succ p.isLt)))) := by
      simpa [MissingColors] using hmissing
    exact hnotpresent hpresent
  have hlastidx : p.succ = Fin.last T.length := by
    apply Fin.ext
    simp [hp]
  have hbetaPrev : beta ∉ PresentColors G phi (T.vertex p.castSucc) := by
    simpa [MissingColors] using hprev
  have hbetaLast : beta ∉ PresentColors G phi (T.vertex p.succ) := by
    rw [hlastidx]
    simpa [MissingColors] using hlast
  let phiStar : PartialEdgeColoring E k :=
    fun e => if e = T.edge p then some beta else phi e
  have hproper := @helper_hproper_118 V E inferInstance inferInstance inferInstance G k e0 phi T
      hmin beta p hend hbetaPrev hbetaLast
  have honeStar : IsOneEdgeUncolored phiStar e0 := by
    have hne : e0 ≠ T.edge p := Ne.symm hedge0
    constructor
    · simp [phiStar, hne, hmin.1.1.2.2.2.2.1]
    · intro e he
      by_cases hep : e = T.edge p
      · subst e
        exact ⟨beta, by simp [phiStar]⟩
      · obtain ⟨c, hc⟩ := hmin.1.1.2.2.2.2.2 e he
        exact ⟨c, by simpa [phiStar, hep] using hc⟩
  have missingPreserved : ∀ (a : Fin (T.length + 1)), a.val < p.val →
      ∀ c, c ∈ MissingColors G phi (T.vertex a) →
        c ∈ MissingColors G phiStar (T.vertex a) := by
    intro a ha c hm
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
    intro hpresent
    rcases (by simpa [PresentColors] using hpresent) with ⟨e, heinc, heval⟩
    by_cases hep : e = T.edge p
    · subst e
      unfold Incident at heinc
      rw [hend] at heinc
      simp only [Sym2.mem_iff] at heinc
      rcases heinc with heinc | heinc
      · have hidx : a = p.castSucc := T.vertex_injective heinc
        have hval : a.val = p.val := congrArg Fin.val hidx
        exact (Nat.lt_irrefl _ (hval ▸ ha))
      · have hidx : a = p.succ := T.vertex_injective heinc
        have hval : a.val = p.val + 1 := by
          simpa using congrArg Fin.val hidx
        omega
    · apply hm
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, heinc, by simpa [phiStar, hep] using heval⟩
  have hdeltaBeta : delta ≠ beta := by
    intro heq
    subst beta
    apply hbetaPrev
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T.edge p, by
      unfold Incident
      rw [hend]
      simp, hdelta⟩
  let S := TreeSequencePrefix T p.val hpone hple
  have hprefix : TreeSequenceInitialSegment S T := by
    unfold TreeSequenceInitialSegment
    refine ⟨hple, ?_, ?_⟩
    · intro a
      dsimp [S, TreeSequencePrefix]
    · intro a
      dsimp [S, TreeSequencePrefix]
  have hTashS := @helper_hTashS_213 V E inferInstance inferInstance inferInstance G k e0 phi T hmin
      beta p hpone hple j missingPreserved
  have hdeltaJ : delta ∈ MissingColors G phiStar
      (T.vertex (Fin.castLT j (by omega))) := by
    have hjm : (Fin.castLT j (by omega)).val < p.val := by
      simpa using hjlt
    exact missingPreserved _ hjm delta (by simpa using hmissing)
  have hdeltaP : delta ∈ MissingColors G phiStar (T.vertex p.castSucc) := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    rcases (by simpa [PresentColors] using hpresent) with ⟨e, heinc, heval⟩
    by_cases hep : e = T.edge p
    · subst e
      have hbadcolor : (some beta : Option (Fin k)) = some delta := by
        simpa [phiStar] using heval
      have : beta = delta := Option.some.inj hbadcolor
      exact hdeltaBeta this.symm
    · have hadj : AdjacentEdges G (T.edge p) e := by
        refine ⟨T.vertex p.castSucc, ?_, heinc⟩
        unfold Incident
        rw [hend]
        simp
      have hold : phi e ≠ some delta :=
        hmin.1.1.2.2.2.1 (Ne.symm hep) hadj hdelta
      apply hold
      simpa [phiStar, hep] using heval
  rcases hmin.1.1 with ⟨hcritical, hchromatic, hdegree, _, _⟩
  have htripleStar : KTriple G k e0 phiStar :=
    ⟨hcritical, hchromatic, hdegree, hproper, honeStar⟩
  have hnotElemS := @helper_hnotElemS_281 V E inferInstance inferInstance inferInstance G k e0 phi T
      beta p hp hpone hple delta j hjlt hdeltaJ hdeltaP
  have hbadS : TashTreeBadPair G k e0 phiStar S :=
    ⟨htripleStar, hTashS, hnotElemS⟩
  have hproperPrefix : S.length < T.length := by
    dsimp [S, TreeSequencePrefix]
    omega
  have hrank : TashTreeRankLess G S T :=
    TashTreeProperInitialSegmentRankLess G S T hprefix hproperPrefix
  refine ⟨hpone, hple, delta, j, phiStar, hdelta, hjlt, hmissing, ?_, hbadS, hrank⟩
  rfl

end GoldbergSeymour

end
