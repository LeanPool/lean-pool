/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.ScheideBalancedCandidate
public import LeanPool.GoldbergSeymour.TashTree
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TashkinovOrderBound
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Scheide Balanced Candidate Maximum Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hPlusTash_173.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (_ :
        ScheideBalancedCandidate N S),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (hnlt : n < T.length + (1 : ℕ)) (hnlarge : (2 : ℕ) ≤ n),
    let q : Fin T.length := (⟨n - (1 : ℕ), Decidable.byContradiction fun (a : ¬n - (1 : ℕ) <
        T.length) =>
    by omega
    ⟩ : Fin T.length);
    ∀ (a : Fin ((↑q : ℕ) + (1 : ℕ))) (gamma : Fin k) (_ : phi (T.edge q) = some gamma) (_ : gamma
        ∈ MissingColors G phi (T.vertex (a.castLT ((
    by first  | omega
    ))))) (s : Fin (S.length + (1 : ℕ))) (_ : S.vertex s = T.vertex (a.castLT (Nat.lt_trans a.isLt
        (Nat.succ_lt_succ q.isLt)))) (Splus : TreeSequence G e0) (hPlusLen : Splus.length =
        S.length + (1 : ℕ)) (hSPlusInit : TreeSequenceInitialSegment S Splus) (_ : Splus.edge
        (Fin.cast ((
    by omega
    )) (Fin.last S.length)) = T.edge q) (_ : (
    ∀ (i : Fin (S.length + (1 : ℕ))), Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) i)
        = S.vertex i)) (_ : (
    ∀ (j : Fin S.length), Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j)), TashkinovTree G e0
        phi Splus := by
  classical
  intro V E _ _ _ _ G k e0 phi T S N hS X omitted n hnlt hnlarge q a gamma hqcolor hagamma s hsa
      Splus hPlusLen hSPlusInit hPlusLast hPlusVertex hPlusEdge j hj
  by_cases hlast : j.val = S.length
  · have hjlast : j = Fin.cast hPlusLen.symm (Fin.last S.length) := by
      apply Fin.ext
      simp [hlast]
    let ss : Fin (j.val + 1) := ⟨s.val, by simpa [hlast] using s.isLt⟩
    refine ⟨ss, gamma, ?_, ?_⟩
    · rw [hjlast, hPlusLast, hqcolor]
    · have hcast : Fin.castLT ss
        (Nat.lt_trans ss.isLt (Nat.succ_lt_succ j.isLt)) =
        Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s := by
        apply Fin.ext
        simp [ss]
      rw [hcast, hPlusVertex, hsa]
      exact hagamma
  · have hjlt : j.val < S.length := by
      rw [hPlusLen] at j
      omega
    let jS : Fin S.length := ⟨j.val, hjlt⟩
    obtain ⟨i, c, hcolor, hmissing⟩ := hS.tashkinov jS (by simpa [jS] using hj)
    let ii : Fin (j.val + 1) := ⟨i.val, by simpa [jS] using i.isLt⟩
    refine ⟨ii, c, ?_, ?_⟩
    · have hindex : j = Fin.castLE hSPlusInit.1 jS := by
        apply Fin.ext
        rfl
      rw [hindex, hPlusEdge]
      exact hcolor
    · have hidx : Fin.castLT ii
          (Nat.lt_trans ii.isLt (Nat.succ_lt_succ j.isLt)) =
          Fin.castLE (Nat.succ_le_succ hSPlusInit.1)
            (Fin.castLT i
              (Nat.lt_trans i.isLt (Nat.succ_lt_succ jS.isLt))) := by
        apply Fin.ext
        rfl
      rw [hidx, hPlusVertex]
      exact hmissing

private theorem helper_hPlusPlusTash_472.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V] (G : LooplessMultigraph
        V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (_ : n < T.length + (1 : ℕ)) (_ : (2 : ℕ) ≤ n) (gamma : Fin k) (s : Fin (S.length + (1 :
        ℕ))) (Splus : TreeSequence G e0) (_ : Splus.length = S.length + (1 : ℕ)) (hSPlusInit :
        TreeSequenceInitialSegment S Splus) (_ : TashkinovTree G e0 phi Splus) (_ :
        (TreeSequenceVertexSet Splus).card = S.length + (2 : ℕ)),
    let U : Finset V := TreeSequenceVertexSet Splus;
    ∀ (_ : U.card = S.length + (2 : ℕ)) (f : E) (_ : phi f = some gamma) (Splusplus : TreeSequence
        G e0) (hPlusPlusLen : Splusplus.length = Splus.length + (1 : ℕ)) (hPlusPlusInit :
        TreeSequenceInitialSegment Splus Splusplus) (_ : Splusplus.edge (Fin.cast ((
    by omega
    )) (Fin.last Splus.length)) = f) (_ : (
    ∀ (i : Fin (Splus.length + (1 : ℕ))), Splusplus.vertex (Fin.castLE (Nat.succ_le_succ
        hPlusPlusInit.1) i) = Splus.vertex i)) (_ : (
    ∀ (j : Fin Splus.length), Splusplus.edge (Fin.castLE hPlusPlusInit.1 j) = Splus.edge j)),
    let zIndex : Fin (Splus.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s;
    ∀ (_ : gamma ∈ MissingColors G phi (Splus.vertex zIndex)), TashkinovTree G e0 phi Splusplus
  := by
  classical
  intro V E _ _ _ G k e0 phi T S X omitted n hnlt hnlarge gamma s Splus hPlusLen hSPlusInit
      hPlusTash hPlusCard U hUCard f hfColor Splusplus hPlusPlusLen hPlusPlusInit hPlusPlusLast
      hPlusPlusVertex hPlusPlusEdge zIndex hzIndexMissing j hj
  let _ := Fintype.ofFinite V
  by_cases hlast : j.val = Splus.length
  · have hjlast : j = Fin.cast hPlusPlusLen.symm (Fin.last Splus.length) := by
      apply Fin.ext
      simp [hlast]
    let zz : Fin (j.val + 1) :=
      ⟨zIndex.val, by simpa [hlast] using zIndex.isLt⟩
    refine ⟨zz, gamma, ?_, ?_⟩
    · rw [hjlast, hPlusPlusLast, hfColor]
    · have hcast : Fin.castLT zz
          (Nat.lt_trans zz.isLt (Nat.succ_lt_succ j.isLt)) =
          Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1) zIndex := by
        apply Fin.ext
        simp [zz]
      rw [hcast, hPlusPlusVertex]
      exact hzIndexMissing
  · have hjlt : j.val < Splus.length := by
      rw [hPlusPlusLen] at j
      omega
    let jPlus : Fin Splus.length := ⟨j.val, hjlt⟩
    obtain ⟨i, c, hcolor, hmissing⟩ :=
      hPlusTash jPlus (by simpa [jPlus] using hj)
    let ii : Fin (j.val + 1) :=
      ⟨i.val, by simpa [jPlus] using i.isLt⟩
    refine ⟨ii, c, ?_, ?_⟩
    · have hindex : j = Fin.castLE hPlusPlusInit.1 jPlus := by
        apply Fin.ext
        rfl
      rw [hindex, hPlusPlusEdge]
      exact hcolor
    · have hidx : Fin.castLT ii
          (Nat.lt_trans ii.isLt (Nat.succ_lt_succ j.isLt)) =
          Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1)
            (Fin.castLT i
              (Nat.lt_trans i.isLt (Nat.succ_lt_succ jPlus.isLt))) := by
        apply Fin.ext
        rfl
      rw [hidx, hPlusPlusVertex]
      exact hmissing

private theorem helper_hUsed_577.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (_ :
        ScheideBalancedCandidate N S),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (_ : n < T.length + (1 : ℕ)) (_ : (2 : ℕ) ≤ n) (gamma : Fin k) (_ : Fin (S.length + (1 :
        ℕ))) (Splus : TreeSequence G e0) (hPlusLen : Splus.length = S.length + (1 : ℕ))
        (hSPlusInit : TreeSequenceInitialSegment S Splus) (_ : (
    ∀ (j : Fin S.length), Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j)) (_ : gamma ∈
        TreeUsedColors phi T) (_ : (TreeSequenceVertexSet Splus).card = S.length + (2 : ℕ)),
    let U : Finset V := TreeSequenceVertexSet Splus;
    ∀ (_ : U.card = S.length + (2 : ℕ)) (Splusplus : TreeSequence G e0) (hPlusPlusLen :
        Splusplus.length = Splus.length + (1 : ℕ)) (hPlusPlusInit : TreeSequenceInitialSegment
        Splus Splusplus) (_ : (
    ∀ (j : Fin Splus.length), Splusplus.edge (Fin.castLE hPlusPlusInit.1 j) = Splus.edge j)),
    let firstNewPlus : Fin Splus.length := Fin.cast (Eq.symm hPlusLen) (Fin.last S.length);
    let firstNew : Fin Splusplus.length := Fin.castLE hPlusPlusInit.1 firstNewPlus;
    let secondNew : Fin Splusplus.length := Fin.cast (Eq.symm hPlusPlusLen) (Fin.last
        Splus.length);
    ∀ (_ : (↑firstNew : ℕ) = S.length) (_ : (↑secondNew : ℕ) = S.length + (1 : ℕ)) (_ : phi
        (Splusplus.edge firstNew) = some gamma) (_ : phi (Splusplus.edge secondNew) = some gamma)
        (_ : (TreeSequenceVertexSet Splusplus).card = S.length + (3 : ℕ)), TreeUsedColors phi
        Splusplus ⊆ TreeUsedColors phi T := by
  classical
  intro V E _ _ _ _ G k e0 phi T S N hS X omitted n hnlt hnlarge gamma s Splus hPlusLen
      hSPlusInit hPlusEdge hgammaUsedT hPlusCard U hUCard Splusplus hPlusPlusLen hPlusPlusInit
      hPlusPlusEdge firstNewPlus firstNew secondNew hFirstNewVal hSecondNewVal hFirstNewColor
      hSecondNewColor hPlusPlusCard c hc
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hc ⊢
  obtain ⟨j, hj, hjcolor⟩ := hc
  by_cases hold : j.val < S.length
  · let jS : Fin S.length := ⟨j.val, hold⟩
    have hjEq : j = Fin.castLE hPlusPlusInit.1
        (Fin.castLE hSPlusInit.1 jS) := by
      apply Fin.ext
      rfl
    have hOldColor : phi (S.edge jS) = some c := by
      rw [hjEq, hPlusPlusEdge, hPlusEdge] at hjcolor
      exact hjcolor
    have hcS : c ∈ TreeUsedColors phi S := by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨jS, by simpa [jS] using hj, hOldColor⟩
    simpa [TreeUsedColors] using hS.usedColors hcS
  · have hjcases : j.val = S.length ∨ j.val = S.length + 1 := by
      rw [hPlusPlusLen, hPlusLen] at j
      omega
    have hcgamma : c = gamma := by
      rcases hjcases with hfirst | hsecond
      · have hjeq : j = firstNew := by
          apply Fin.ext
          simpa [hFirstNewVal] using hfirst
        rw [hjeq, hFirstNewColor] at hjcolor
        exact (Option.some.inj hjcolor).symm
      · have hjeq : j = secondNew := by
          apply Fin.ext
          simpa [hSecondNewVal] using hsecond
        rw [hjeq, hSecondNewColor] at hjcolor
        exact (Option.some.inj hjcolor).symm
    simpa [hcgamma, TreeUsedColors] using hgammaUsedT

private theorem helper_hCandidate_618.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (_ :
        ScheideBalancedCandidate N S),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (_ : n < T.length + (1 : ℕ)) (_ : (2 : ℕ) ≤ n) (gamma : Fin k) (_ : Fin (S.length + (1 :
        ℕ))) (Splus : TreeSequence G e0) (hPlusLen : Splus.length = S.length + (1 : ℕ))
        (hSPlusInit : TreeSequenceInitialSegment S Splus) (_ : (
    ∀ (j : Fin S.length), Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j)) (_ :
        (TreeSequenceVertexSet S).card = S.length + (1 : ℕ)) (_ : (TreeSequenceVertexSet
        Splus).card = S.length + (2 : ℕ)),
    let U : Finset V := TreeSequenceVertexSet Splus;
    ∀ (_ : U.card = S.length + (2 : ℕ)) (Splusplus : TreeSequence G e0) (hPlusPlusLen :
        Splusplus.length = Splus.length + (1 : ℕ)) (hPlusPlusInit : TreeSequenceInitialSegment
        Splus Splusplus) (_ : (
    ∀ (j : Fin Splus.length), Splusplus.edge (Fin.castLE hPlusPlusInit.1 j) = Splus.edge j)) (_ :
        TashkinovTree G e0 phi Splusplus) (_ : TreeSequenceInitialSegment (NormalTripleTrunk N)
        Splusplus),
    let firstNewPlus : Fin Splus.length := Fin.cast (Eq.symm hPlusLen) (Fin.last S.length);
    let firstNew : Fin Splusplus.length := Fin.castLE hPlusPlusInit.1 firstNewPlus;
    let secondNew : Fin Splusplus.length := Fin.cast (Eq.symm hPlusPlusLen) (Fin.last
        Splus.length);
    ∀ (_ : (↑firstNew : ℕ) = S.length) (_ : (↑secondNew : ℕ) = S.length + (1 : ℕ)) (_ : phi
        (Splusplus.edge firstNew) = some gamma) (_ : phi (Splusplus.edge secondNew) = some gamma)
        (_ : (TreeSequenceVertexSet Splusplus).card = S.length + (3 : ℕ)) (_ : TreeUsedColors phi
        Splusplus ⊆ TreeUsedColors phi T) (_ : Odd (TreeSequenceVertexSet Splusplus).card),
        ScheideBalancedCandidate N Splusplus := by
  classical
  intro V E _ _ _ _ G k e0 phi T S N hS X omitted n hnlt hnlarge gamma s Splus hPlusLen
      hSPlusInit hPlusEdge hSCard hPlusCard U hUCard Splusplus hPlusPlusLen hPlusPlusInit
      hPlusPlusEdge hPlusPlusTash hTrunkInit firstNewPlus firstNew secondNew hFirstNewVal
      hSecondNewVal hFirstNewColor hSecondNewColor hPlusPlusCard hUsed hPlusPlusOdd
  refine
    { tashkinov := hPlusPlusTash
      oddOrder := hPlusPlusOdd
      exactTrunk := hTrunkInit
      usedColors := hUsed
      paired := ?_ }
  intro r hlow hupp
  by_cases hold : 2 * r < S.length + 1
  · have hOld := hS.paired r hlow hold
    have hidxOne :
        (⟨2 * r - 2, by omega⟩ : Fin Splusplus.length) =
          Fin.castLE hPlusPlusInit.1
            (Fin.castLE hSPlusInit.1
              (⟨2 * r - 2, by omega⟩ : Fin S.length)) := by
      apply Fin.ext
      rfl
    have hidxTwo :
        (⟨2 * r - 1, by omega⟩ : Fin Splusplus.length) =
          Fin.castLE hPlusPlusInit.1
            (Fin.castLE hSPlusInit.1
              (⟨2 * r - 1, by omega⟩ : Fin S.length)) := by
      apply Fin.ext
      rfl
    rw [hidxOne, hidxTwo, hPlusPlusEdge, hPlusEdge,
      hPlusPlusEdge, hPlusEdge]
    exact hOld
  · have hoddLength : Odd (S.length + 1) := by
      rw [← hSCard]
      exact hS.oddOrder
    have hne : 2 * r ≠ S.length + 1 := by
      intro heq
      rcases hoddLength with ⟨m, hm⟩
      omega
    have heq : 2 * r = S.length + 2 := by
      rw [hPlusPlusLen, hPlusLen] at hupp
      omega
    have hidxOne :
        (⟨2 * r - 2, by omega⟩ : Fin Splusplus.length) = firstNew := by
      apply Fin.ext
      simp [hFirstNewVal, heq]
    have hidxTwo :
        (⟨2 * r - 1, by omega⟩ : Fin Splusplus.length) = secondNew := by
      apply Fin.ext
      simp [hSecondNewVal, heq]
    rw [hidxOne, hidxTwo, hFirstNewColor, hSecondNewColor]

private theorem helper_firstVertices_354.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E)
      (e0 : E) (T S : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (j : Fin (2 : ℕ)),
    T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈ X := by
  classical
  intro V E _ _ G e0 T S X j
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  obtain ⟨it, ht⟩ := T.attaches ⟨0, T.positive⟩
  obtain ⟨is, hs⟩ := S.attaches ⟨0, S.positive⟩
  have itzero : it = 0 := Fin.eq_zero it
  have iszero : is = 0 := Fin.eq_zero is
  subst it
  subst is
  rw [T.first_edge] at ht
  rw [S.first_edge] at hs
  have hm : T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈
      G.ends e0 := by
    have cases : j.val = 0 ∨ j.val = 1 := by omega
    rcases cases with hzero | hone
    · have hj : j = 0 := Fin.ext hzero
      subst j
      rw [ht]
      exact Sym2.mem_iff.mpr (Or.inr rfl)
    · have hj : j = 1 := Fin.ext hone
      subst j
      rw [ht]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
  rw [hs] at hm
  rcases Sym2.mem_iff.mp hm with hm | hm
  · simpa [X, TreeSequenceVertexSet] using
      (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩)
  · simpa [X, TreeSequenceVertexSet] using
      (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩)

private theorem helper_hgoodUnion_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (_ : n < T.length + (1 : ℕ)) (_ : (2 : ℕ) ≤ n) (gamma : Fin k) (Splus : TreeSequence G e0),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let edges : Finset E := {e : E | phi e = some gamma};
    let good : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ U};
    ∀ (_ : (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ))) (_ : (
    ∀ ⦃e : E⦄ (_ : e ∈ good) ⦃f : E⦄ (_ : f ∈ good) (_ : e ≠ f), Disjoint (G.ends e).toFinset
        (G.ends f).toFinset)), (good.biUnion fun (e : E) => (G.ends e).toFinset).card = (2 : ℕ) *
        good.card := by
  classical
  intro V E _ _ _ G k e0 phi T S X omitted n hnlt hnlarge gamma Splus U edges good hendcard
      hgoodDisjoint
  have aux : ∀ A : Finset E, A ⊆ good →
      (A.biUnion fun e => (G.ends e).toFinset).card = 2 * A.card := by
    intro A hA
    induction A using Finset.induction_on with
    | empty => simp
    | @insert e A heA ih =>
      rw [Finset.biUnion_insert]
      have hd : Disjoint (G.ends e).toFinset
          (A.biUnion fun f => (G.ends f).toFinset) := by
        rw [Finset.disjoint_left]
        intro v hev hvA
        obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
        have hh := hgoodDisjoint (hA (Finset.mem_insert_self e A))
          (hA (Finset.mem_insert_of_mem hf)) (by
            intro hef
            exact heA (by simpa [hef] using hf))
        exact (Finset.disjoint_left.mp hh) hev hvf
      rw [Finset.card_union_of_disjoint hd, hendcard]
      rw [ih (fun x hx => hA (Finset.mem_insert_of_mem hx))]
      rw [Finset.card_insert_of_notMem heA]
      omega
  exact aux good (by intro e he; exact he)

private theorem helper_hcover_548.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (S : TreeSequence G e0) (gamma : Fin k) (s : Fin (S.length + (1 : ℕ)))
      (Splus : TreeSequence G e0) (hSPlusInit : TreeSequenceInitialSegment S Splus),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let z : V := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s);
    ∀ (_ : (∀ v ∈ U, v ≠ z → gamma ∈ PresentColors G phi v)),
    let B : Finset E := BoundaryColorEdges G phi U gamma;
    let edges : Finset E := {e : E | phi e = some gamma};
    let good : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ U};
    let Y : Finset V := U.erase z;
    ∀ (_ : (∀ (e : E), e ∈ edges ↔ phi e = some gamma))
      (_ : (∀ (e : E), e ∈ good ↔ e ∈ edges ∧ ∀ (v : V), Incident G v e → v ∈ U)),
    ∀ v ∈ Y,
    (v ∈ good.biUnion fun (e : E) => (G.ends e).toFinset) ∨
      v ∈ B.biUnion fun (e : E) => {v ∈ U | Incident G v e} := by
  classical
  intro V E _ _ _ G k e0 phi S gamma s Splus hSPlusInit U z hpresent B edges good Y hedgeMem
      hgood v hvY
  have hvU : v ∈ U := Finset.mem_of_mem_erase hvY
  have hvz : v ≠ z := (Finset.mem_erase.mp hvY).1
  obtain ⟨e, hve, hecolor⟩ := by
    simpa [PresentColors] using hpresent v hvU hvz
  by_cases hall : ∀ w, Incident G w e → w ∈ U
  · left
    exact Finset.mem_biUnion.mpr
      ⟨e, (hgood e).mpr ⟨(hedgeMem e).mpr hecolor, hall⟩,
        Sym2.mem_toFinset.mpr hve⟩
  · right
    push Not at hall
    obtain ⟨w, hw, hwo⟩ := hall
    obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hw
    have heq : G.ends e = s(w, x) := hx
    have hxU : x ∈ U := by
      have hvends : v = w ∨ v = x := by
        have : v ∈ s(w, x) := by rw [← heq]; exact hve
        simpa using this
      rcases hvends with rfl | rfl
      · exact False.elim (hwo hvU)
      · exact hvU
    have hbound : e ∈ BoundaryEdges G U := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxU, w, hwo, heq.trans Sym2.eq_swap⟩
    exact Finset.mem_biUnion.mpr
      ⟨e, (Finset.mem_filter.mpr ⟨hbound, hecolor⟩),
        Finset.mem_filter.mpr ⟨hvU, hve⟩⟩

private theorem helper_hbUnion_607.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (_ : n < T.length + (1 : ℕ)) (_ : (2 : ℕ) ≤ n) (gamma : Fin k) (Splus : TreeSequence G e0),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let B : Finset E := BoundaryColorEdges G phi U gamma;
    ∀ (_ : (
    ∀ e ∈ B, {v ∈ U | Incident G v e}.card = (1 : ℕ))) (_ : (
    ∀ ⦃e : E⦄ (_ : e ∈ B) ⦃f : E⦄ (_ : f ∈ B) (_ : e ≠ f), Disjoint ({v ∈ U | Incident G v e})
        ({v ∈ U | Incident G v f}))), (B.biUnion fun (e : E) => {v ∈ U | Incident G v e}).card =
        B.card := by
  classical
  intro V E _ _ _ G k e0 phi T S X omitted n hnlt hnlarge gamma Splus U B hbFiber hbDisjoint
  have aux :
    ∀ A : Finset E, A ⊆ B → (A.biUnion fun e => U.filter (fun v => Incident G v e)).card = A.card
  := by
    intro A hA
    induction A using Finset.induction_on with
    | empty => simp
    | @insert e A heA ih =>
      rw [Finset.biUnion_insert]
      have hd : Disjoint (U.filter (fun v => Incident G v e))
          (A.biUnion fun f => U.filter (fun v => Incident G v f)) := by
        rw [Finset.disjoint_left]
        intro v hev hvA
        obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
        exact (Finset.disjoint_left.mp
          (hbDisjoint (hA (Finset.mem_insert_self e A))
            (hA (Finset.mem_insert_of_mem hf)) (by
              intro hef
              exact heA (by simpa [hef] using hf)))) hev hvf
      rw [Finset.card_union_of_disjoint hd,
        hbFiber e (hA (Finset.mem_insert_self e A))]
      rw [ih (fun x hx => hA (Finset.mem_insert_of_mem hx))]
      rw [Finset.card_insert_of_notMem heA]
      omega
  exact aux B (by intro e he; exact he)

private theorem helper_hnlarge_542.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V] (G : LooplessMultigraph
        V E) (e0 : E) (T S : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (_ : (
    ∀ (j : Fin (2 : ℕ)), T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈ X)) (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (hnlt : n < T.length + (1 : ℕ)) (_ : T.vertex (⟨n, hnlt⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
        (2 : ℕ) ≤ n := by
  classical
  intro V E _ _ _ G e0 T S X firstVertices omitted n hnlt hnout
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  by_contra hh
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with hzero | hone
  · apply hnout
    simpa [hzero] using firstVertices ⟨0, by omega⟩
  · apply hnout
    have hv := firstVertices ⟨1, by omega⟩
    have hi : (⟨n, hnlt⟩ : Fin (T.length + 1)) =
        Fin.castLE (Nat.succ_le_succ T.positive) ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [hone]
    rw [hi]
    exact hv

private theorem helper_prior_563.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [ DecidableEq V] (G : LooplessMultigraph
        V E) (e0 : E) (T S : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (hnlt : n < T.length + (1 : ℕ)) (hnlarge : (2 : ℕ) ≤ n),
    let q : Fin T.length := (⟨n - (1 : ℕ), Decidable.byContradiction fun (a : ¬n - (1 : ℕ) <
        T.length) =>
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : (↑q : ℕ) + (1 : ℕ) = n) (i : Fin ((↑q : ℕ) + (1 : ℕ))), T.vertex (i.castLT
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))) ∈ X := by
  classical
  intro V E _ _ _ G e0 T S X omitted n hnlt hnlarge q hqrel i
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  by_contra hout
  have hprop : ∃ hi : i.val < T.length + 1,
      T.vertex ⟨i.val, hi⟩ ∉ X :=
    ⟨by omega, by
      intro hm
      apply hout
      convert hm using 1
      apply congrArg T.vertex
      apply Fin.ext
      rfl⟩
  have hmin : n ≤ i.val := Nat.find_min' omitted hprop
  omega

private theorem helper_hbFiber_675.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (gamma : Fin k) (Splus : TreeSequence G e0),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let B : Finset E := BoundaryColorEdges G phi U gamma;
    ∀ e ∈ B, {v ∈ U | Incident G v e}.card = (1 : ℕ) := by
  classical
  intro V E _ _ G k e0 phi gamma Splus U B e he
  obtain ⟨u, hu, v, hv, huv⟩ := by
    simpa [B, BoundaryColorEdges, BoundaryEdges] using
      (Finset.mem_filter.mp he).1
  have hs : U.filter (fun x => Incident G x e) = {u} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
      huv, Sym2.mem_iff]
    constructor
    · rintro ⟨hxU, rfl | hxe⟩
      · exact rfl
      · exact False.elim (hv (hxe ▸ hxU))
    · intro hxu
      subst hxu
      exact ⟨hu, Or.inl rfl⟩
  rw [hs]
  simp

private theorem helper_hIY_708.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (S : TreeSequence G e0) (gamma : Fin k) (s : Fin (S.length + (1 : ℕ)))
      (Splus : TreeSequence G e0) (hSPlusInit : TreeSequenceInitialSegment S Splus),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let z : V := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s);
    ∀ (_ : gamma ∉ PresentColors G phi z),
    let edges : Finset E := {e : E | phi e = some gamma};
    let good : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ U};
    let Y : Finset V := U.erase z;
    ∀ (_ : (∀ (e : E), e ∈ edges ↔ phi e = some gamma))
      (_ : (∀ (e : E), e ∈ good ↔ e ∈ edges ∧ ∀ (v : V), Incident G v e → v ∈ U)),
    let I : Finset V := good.biUnion fun (e : E) => (G.ends e).toFinset;
    I ⊆ Y := by
  classical
  intro V E _ _ _ G k e0 phi S gamma s Splus hSPlusInit U z hzNotPresent edges good Y hedgeMem
      hgood I v hv
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have hvU : v ∈ U := (hgood e).mp he |>.2 v
    (Sym2.mem_toFinset.mp hve)
  have hvz : v ≠ z := by
    intro hvz
    subst v
    apply hzNotPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, Sym2.mem_toFinset.mp hve,
      hedgeMem e |>.mp (hgood e |>.mp he).1⟩
  exact Finset.mem_erase.mpr ⟨hvz, hvU⟩

private theorem helper_hIW_733.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (gamma : Fin k) (Splus : TreeSequence G e0),
    let U : Finset V := TreeSequenceVertexSet Splus;
    ∀ (_ : IsProperEdgeColoring G phi),
    let B : Finset E := BoundaryColorEdges G phi U gamma;
    let edges : Finset E := {e : E | phi e = some gamma};
    let good : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ U};
    ∀ (_ : (∀ (e : E), e ∈ edges ↔ phi e = some gamma))
      (_ : (∀ (e : E), e ∈ good ↔ e ∈ edges ∧ ∀ (v : V), Incident G v e → v ∈ U)),
    let I : Finset V := good.biUnion fun (e : E) => (G.ends e).toFinset;
    let W : Finset V := B.biUnion fun (e : E) => {v ∈ U | Incident G v e};
    Disjoint I W := by
  classical
  intro V E _ _ _ G k e0 phi gamma Splus U hproper B edges good hedgeMem hgood I W
  rw [Finset.disjoint_left]
  intro v hvI hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvI
  obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
  have hef : e ≠ f := by
    intro hef
    subst f
    obtain ⟨u, hu, w, hw, huw⟩ := by
      simpa [B, BoundaryColorEdges, BoundaryEdges] using
        (Finset.mem_filter.mp hf).1
    have hwU : w ∈ U := (hgood e).mp he |>.2 w
      (by change w ∈ G.ends e; rw [huw]; exact Sym2.mem_mk_right u w)
    exact hw hwU
  exact (hproper hef
    ⟨v, Sym2.mem_toFinset.mp hve, (Finset.mem_filter.mp hvf).2⟩
    (hedgeMem e |>.mp (hgood e |>.mp he).1))
    (Finset.mem_filter.mp hf).2

private theorem helper_continuation_951.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (_ :
        ScheideBalancedCandidate N S) (_ : (
    ∀ (R : TreeSequence G e0) (_ : ScheideBalancedCandidate N R), (TreeSequenceVertexSet R).card ≤
        (TreeSequenceVertexSet S).card)),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (hnlt : n < T.length + (1 : ℕ)) (hnlarge : (2 : ℕ) ≤ n),
    let q : Fin T.length := (⟨n - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (gamma : Fin k) (_ : phi (T.edge q) = some gamma) (s : Fin (S.length + (1 : ℕ))) (Splus :
        TreeSequence G e0) (hPlusLen : Splus.length = S.length + (1 : ℕ)) (hSPlusInit :
        TreeSequenceInitialSegment S Splus) (_ : Splus.edge (Fin.cast (
    by omega
    ) (Fin.last S.length)) = T.edge q) (_ : (
    ∀ (i : Fin (S.length + (1 : ℕ))), Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) i)
        = S.vertex i)) (_ : (
    ∀ (j : Fin S.length), Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j)) (_ : TashkinovTree G
        e0 phi Splus) (_ : gamma ∈ TreeUsedColors phi T) (_ : (TreeSequenceVertexSet S).card =
        S.length + (1 : ℕ)) (_ : (TreeSequenceVertexSet Splus).card = S.length + (2 : ℕ)) (_ :
        gamma ∈ MissingColors G phi (Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1)
        s))),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let z : V := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s);
    ∀ (_ : z ∈ U) (_ : gamma ∈ MissingColors G phi z) (_ : gamma ∉ PresentColors G phi z) (_ : (
    ∀ v ∈ U, v ≠ z → gamma ∈ PresentColors G phi v)),
    let B : Finset E := BoundaryColorEdges G phi U gamma;
    let edges : Finset E := ({e : E | phi e = some gamma} : Finset E);
    let good : Finset E := ({e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ U} : Finset E);
    let Y : Finset V := U.erase z;
    ∀ (_ : (
    ∀ v ∈ Y, (v ∈ good.biUnion fun (e : E) ↦ (G.ends e).toFinset) ∨ v ∈ B.biUnion fun (e : E) ↦
        ({v ∈ U | Incident G v e} : Finset V))),
    let I : Finset V := good.biUnion fun (e : E) ↦ (G.ends e).toFinset;
    let W : Finset V := B.biUnion fun (e : E) ↦ ({v ∈ U | Incident G v e} : Finset V);
    ∀ (_ : I ⊆ Y) (_ : W ⊆ Y) (_ : I ∪ W = Y) (_ : Y.card = (2 : ℕ) * good.card + B.card) (_ :
        U.card = S.length + (2 : ℕ)) (_ : Y.card = S.length + (1 : ℕ)) (_ : Odd Y.card) (_ : (0 :
        ℕ) < B.card), False := by
  classical
  intro V E _ _ _ _ G k e0 phi T S N hS hmax X omitted n hnlt hnlarge q gamma hqcolor s Splus
      hPlusLen hSPlusInit hPlusLast hPlusVertex hPlusEdge hPlusTash hgammaUsedT hSCard hPlusCard
      hsGamma U z hzU hzMissing hzNotPresent hpresent B edges good Y hcover I W hIY hWY hIYunion
      hYCardEq hUCard hYCard hYOdd hBpos
  obtain ⟨f, hfB⟩ := Finset.card_pos.mp hBpos
  have hfBoundary : f ∈ BoundaryEdges G U :=
    (Finset.mem_filter.mp hfB).1
  have hfColor : phi f = some gamma :=
    (Finset.mem_filter.mp hfB).2
  obtain ⟨Splusplus, hAdjoinPlusPlus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists Splus f hfBoundary
  rcases hAdjoinPlusPlus with
    ⟨hPlusPlusLen, hPlusPlusInit, hPlusPlusLast⟩
  have hPlusPlusVertex (i : Fin (Splus.length + 1)) :
      Splusplus.vertex
          (Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1) i) =
        Splus.vertex i := hPlusPlusInit.2.1 i
  have hPlusPlusEdge (j : Fin Splus.length) :
      Splusplus.edge (Fin.castLE hPlusPlusInit.1 j) = Splus.edge j :=
    hPlusPlusInit.2.2 j
  let zIndex : Fin (Splus.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s
  have hzIndexMissing : gamma ∈ MissingColors G phi (Splus.vertex zIndex) := by
    simpa [zIndex] using hsGamma
  have hPlusPlusTash : TashkinovTree G e0 phi Splusplus := by
    exact @helper_hPlusPlusTash_472 V E inferInstance inferInstance inferInstance G
        k e0 phi T S omitted hnlt hnlarge gamma s Splus hPlusLen hSPlusInit hPlusTash hPlusCard
        hUCard f hfColor Splusplus hPlusPlusLen hPlusPlusInit hPlusPlusLast hPlusPlusVertex
        hPlusPlusEdge hzIndexMissing
  have hSPlusPlusInit : TreeSequenceInitialSegment S Splusplus := by
    exact hSPlusInit.trans hPlusPlusInit
  have hTrunkInit :
      TreeSequenceInitialSegment (NormalTripleTrunk N) Splusplus := by
    exact hS.exactTrunk.trans hSPlusPlusInit
  let firstNewPlus : Fin Splus.length :=
    Fin.cast hPlusLen.symm (Fin.last S.length)
  let firstNew : Fin Splusplus.length :=
    Fin.castLE hPlusPlusInit.1 firstNewPlus
  let secondNew : Fin Splusplus.length :=
    Fin.cast hPlusPlusLen.symm (Fin.last Splus.length)
  have hFirstNewVal : firstNew.val = S.length := by
    simp [firstNew, firstNewPlus]
  have hSecondNewVal : secondNew.val = S.length + 1 := by
    simp [secondNew, hPlusLen]
  have hFirstNewColor : phi (Splusplus.edge firstNew) = some gamma := by
    rw [show Splusplus.edge firstNew = Splus.edge firstNewPlus by
      exact hPlusPlusEdge firstNewPlus]
    rw [show Splus.edge firstNewPlus = T.edge q by
      exact hPlusLast]
    exact hqcolor
  have hSecondNewColor : phi (Splusplus.edge secondNew) = some gamma := by
    rw [show Splusplus.edge secondNew = f by exact hPlusPlusLast]
    exact hfColor
  have hPlusPlusCard :
      (TreeSequenceVertexSet Splusplus).card = S.length + 3 := by
    rw [show (TreeSequenceVertexSet Splusplus).card =
        Splusplus.length + 1 by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
        Splusplus.vertex_injective]]
    omega
  have hUsed : TreeUsedColors phi Splusplus ⊆ TreeUsedColors phi T := by
    exact @helper_hUsed_577 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T S N hS omitted hnlt hnlarge gamma s Splus hPlusLen hSPlusInit hPlusEdge hgammaUsedT
        hPlusCard hUCard Splusplus hPlusPlusLen hPlusPlusInit hPlusPlusEdge hFirstNewVal
        hSecondNewVal hFirstNewColor hSecondNewColor hPlusPlusCard
  have hPlusPlusOdd : Odd (TreeSequenceVertexSet Splusplus).card := by
    rcases hS.oddOrder with ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [hPlusPlusCard]
    rw [hSCard] at hm
    omega
  have hCandidate : ScheideBalancedCandidate N Splusplus := by
    exact @helper_hCandidate_618 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T S N hS omitted hnlt hnlarge gamma s Splus hPlusLen hSPlusInit hPlusEdge hSCard
        hPlusCard hUCard Splusplus hPlusPlusLen hPlusPlusInit hPlusPlusEdge hPlusPlusTash
        hTrunkInit hFirstNewVal hSecondNewVal hFirstNewColor hSecondNewColor hPlusPlusCard hUsed
        hPlusPlusOdd
  have hmaxPlusPlus := hmax Splusplus hCandidate
  rw [hPlusPlusCard, hSCard] at hmaxPlusPlus
  omega

private theorem helper_continuation_856.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T S :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (_ :
        ScheideBalancedCandidate N S) (_ : (
    ∀ (R : TreeSequence G e0) (_ : ScheideBalancedCandidate N R), (TreeSequenceVertexSet R).card ≤
        (TreeSequenceVertexSet S).card)),
    let X : Finset V := TreeSequenceVertexSet S;
    ∀ (omitted :
    ∃ (n : ℕ) (hn : n < T.length + (1 : ℕ)), T.vertex (⟨n, hn⟩ : Fin (T.length + (1 : ℕ))) ∉ X),
    let n : ℕ := Nat.find omitted;
    ∀ (hnlt : n < T.length + (1 : ℕ)) (hnlarge : (2 : ℕ) ≤ n),
    let q : Fin T.length := (⟨n - (1 : ℕ), Decidable.byContradiction fun (a : ¬n - (1 : ℕ) <
        T.length) =>
    by omega
    ⟩ : Fin T.length);
    ∀ (gamma : Fin k) (_ : phi (T.edge q) = some gamma) (s : Fin (S.length + (1 : ℕ))) (Splus :
        TreeSequence G e0) (hPlusLen : Splus.length = S.length + (1 : ℕ)) (hSPlusInit :
        TreeSequenceInitialSegment S Splus) (_ : Splus.edge (Fin.cast ((
    by omega
    )) (Fin.last S.length)) = T.edge q) (_ : (
    ∀ (i : Fin (S.length + (1 : ℕ))), Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) i)
        = S.vertex i)) (_ : (
    ∀ (j : Fin S.length), Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j)) (_ : TashkinovTree G
        e0 phi Splus) (_ : gamma ∈ TreeUsedColors phi T) (_ : (TreeSequenceVertexSet S).card =
        S.length + (1 : ℕ)) (_ : (TreeSequenceVertexSet Splus).card = S.length + (2 : ℕ)) (_ :
        gamma ∈ MissingColors G phi (Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1)
        s))),
    let U : Finset V := TreeSequenceVertexSet Splus;
    let z : V := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s);
    ∀ (_ : z ∈ U) (_ : gamma ∈ MissingColors G phi z) (_ : gamma ∉ PresentColors G phi z) (_ :
        IsProperEdgeColoring G phi) (_ : (
    ∀ v ∈ U, v ≠ z → gamma ∈ PresentColors G phi v)), False := by
  classical
  intro V E _ _ _ _ G k e0 phi T S N hS hmax X omitted n hnlt hnlarge q gamma hqcolor s Splus
      hPlusLen hSPlusInit hPlusLast hPlusVertex hPlusEdge hPlusTash hgammaUsedT hSCard hPlusCard
      hsGamma U z hzU hzMissing hzNotPresent hproper hpresent
  let B := BoundaryColorEdges G phi U gamma
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some gamma)
  let good := edges.filter (fun e => ∀ v, Incident G v e → v ∈ U)
  let Y := U.erase z
  have hedgeMem : ∀ e, e ∈ edges ↔ phi e = some gamma := by
    intro e
    simp [edges]
  have hgood : ∀ e, e ∈ good ↔
      e ∈ edges ∧ ∀ v, Incident G v e → v ∈ U := by
    intro e
    simp [good]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have hgoodDisjoint : ∀ ⦃e⦄, e ∈ good → ∀ ⦃f⦄, f ∈ good →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (hedgeMem e |>.mp (hgood e |>.mp he).1))
      (hedgeMem f |>.mp (hgood f |>.mp hf).1)
  have hgoodUnion :
      (good.biUnion fun e => (G.ends e).toFinset).card = 2 * good.card := by
    exact @helper_hgoodUnion_524 V E inferInstance inferInstance inferInstance G k
        e0 phi T S omitted hnlt hnlarge gamma Splus hendcard hgoodDisjoint
  have hcover : ∀ v, v ∈ Y →
      v ∈ good.biUnion (fun e => (G.ends e).toFinset) ∨
        v ∈ B.biUnion (fun e => U.filter (fun v => Incident G v e)) := by
    exact @helper_hcover_548 V E inferInstance inferInstance inferInstance G k e0 phi S gamma s
        Splus hSPlusInit hpresent hedgeMem hgood
  have hbFiber : ∀ e, e ∈ B →
      (U.filter (fun v => Incident G v e)).card = 1 := by
    exact @helper_hbFiber_675 V E inferInstance inferInstance G k e0 phi gamma Splus
  have hbDisjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B → e ≠ f →
      Disjoint (U.filter (fun v => Incident G v e))
        (U.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, (Finset.mem_filter.mp hev).2, (Finset.mem_filter.mp hvf).2⟩
      (Finset.mem_filter.mp he).2) (Finset.mem_filter.mp hf).2
  have hbUnion :
      (B.biUnion fun e => U.filter (fun v => Incident G v e)).card = B.card := by
    exact @helper_hbUnion_607 V E inferInstance inferInstance inferInstance G k e0
        phi T S omitted hnlt hnlarge gamma Splus hbFiber hbDisjoint
  let I := good.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => U.filter (fun v => Incident G v e))
  have hIY : I ⊆ Y := by
    exact @helper_hIY_708 V E inferInstance inferInstance inferInstance G k e0 phi S gamma s
        Splus hSPlusInit hzNotPresent hedgeMem hgood
  have hWY : W ⊆ Y := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have hvU := (Finset.mem_filter.mp hve).1
    have hvz : v ≠ z := by
      intro hvz
      subst v
      apply hzNotPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, (Finset.mem_filter.mp hve).2,
        (Finset.mem_filter.mp he).2⟩
    exact Finset.mem_erase.mpr ⟨hvz, hvU⟩
  have hIW : Disjoint I W := by
    exact @helper_hIW_733 V E inferInstance inferInstance inferInstance G k e0 phi gamma Splus
        hproper hedgeMem hgood
  have hIYunion : I ∪ W = Y := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hIY hWY
    · intro v hv
      rcases hcover v hv with hvI | hvW
      · exact Finset.mem_union.mpr (Or.inl hvI)
      · exact Finset.mem_union.mpr (Or.inr hvW)
  have hYCardEq : Y.card = 2 * good.card + B.card := by
    rw [← hIYunion, Finset.card_union_of_disjoint hIW]
    simpa [I, W] using congrArg₂ (· + ·) hgoodUnion hbUnion
  have hUCard : U.card = S.length + 2 := by
    simpa [U] using hPlusCard
  have hYCard : Y.card = S.length + 1 := by
    have herase := Finset.card_erase_add_one hzU
    change Y.card + 1 = U.card at herase
    omega
  have hYOdd : Odd Y.card := by
    rw [hYCard, ← hSCard]
    exact hS.oddOrder
  have hBOdd : Odd B.card := by
    rcases hYOdd with ⟨m, hm⟩
    have hgoodle : good.card ≤ m := by omega
    refine ⟨m - good.card, ?_⟩
    omega
  have hBpos : 0 < B.card := by
    rcases hBOdd with ⟨m, hm⟩
    omega
  exact @helper_continuation_951 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@S) (@N) (@hS) (@hmax) (@omitted) (@hnlt)
      (@hnlarge) (@gamma) (@hqcolor) (@s) (@Splus) (@hPlusLen) (@hSPlusInit) (@hPlusLast)
      (@hPlusVertex) (@hPlusEdge) (@hPlusTash) (@hgammaUsedT) (@hSCard) (@hPlusCard) (@hsGamma)
      (@hzU) (@hzMissing) (@hzNotPresent) (@hpresent) (@hcover) (@hIY) (@hWY) (@hIYunion)
      (@hYCardEq) (@hUCard) (@hYCard) (@hYOdd) (@hBpos)
theorem ScheideBalancedCandidateMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hS : ScheideBalancedCandidate N S)
    (hmax : ∀ R : TreeSequence G e0, ScheideBalancedCandidate N R →
      (TreeSequenceVertexSet R).card ≤
        (TreeSequenceVertexSet S).card) :
    (TreeSequenceVertexSet S).card = TashkinovOrder G := by
  classical
  have htriple : KTriple G k e0 phi := N.global.1
  have hSle := treeCard_le_tashkinovOrder G k e0 phi S htriple hS.tashkinov
  apply Nat.le_antisymm hSle
  by_contra hnot
  have hltOrder : (TreeSequenceVertexSet S).card < TashkinovOrder G :=
    Nat.lt_of_not_ge hnot
  have hlt : (TreeSequenceVertexSet S).card <
      (TreeSequenceVertexSet T).card := by
    simpa [N.global.2.2] using hltOrder
  let X := TreeSequenceVertexSet S
  have firstVertices : ∀ j : Fin 2,
      T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈ X := by
    exact @helper_firstVertices_354 V E inferInstance inferInstance G
        e0 T S
  have omitted : ∃ n : ℕ, ∃ hn : n < T.length + 1,
      T.vertex ⟨n, hn⟩ ∉ X := by
    by_contra hn
    push Not at hn
    have hsub : TreeSequenceVertexSet T ⊆ X := by
      intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp
        (show v ∈ Finset.image T.vertex Finset.univ from by
          simpa [TreeSequenceVertexSet] using hv)
      exact hn j.val j.isLt
    have hcard := Finset.card_le_card hsub
    exact (Nat.not_le_of_gt hlt) (by simpa [X] using hcard)
  let n : ℕ := Nat.find omitted
  have hnlt : n < T.length + 1 := (Nat.find_spec omitted).1
  have hnout : T.vertex ⟨n, hnlt⟩ ∉ X := (Nat.find_spec omitted).2
  have hnlarge : 2 ≤ n := by
    exact @helper_hnlarge_542 V E inferInstance inferInstance inferInstance G e0 T
        S firstVertices omitted hnlt hnout
  let q : Fin T.length := ⟨n - 1, by omega⟩
  have hqrel : q.val + 1 = n := by
    simp [q, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hqout : T.vertex q.succ ∉ X := by
    have hidx : q.succ = ⟨n, hnlt⟩ := Fin.ext (by simp [hqrel])
    rw [hidx]
    exact hnout
  have prior : ∀ (i : Fin (q.val + 1)),
      T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))) ∈ X := by
    exact @helper_prior_563 V E inferInstance inferInstance inferInstance G e0 T S
        omitted hnlt hnlarge hqrel
  obtain ⟨a, gamma, hqcolor, hagamma⟩ :=
    N.global.2.1 q (by simp [q]; omega)
  have haX := prior a
  obtain ⟨s, -, hsa⟩ := Finset.mem_image.mp
    (show T.vertex (Fin.castLT a
        (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))) ∈
        Finset.image S.vertex Finset.univ from by
      simpa [X, TreeSequenceVertexSet] using haX)
  obtain ⟨b, hqb⟩ := T.attaches q
  have hbX := prior b
  have hboundary : T.edge q ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨T.vertex (Fin.castLT b
        (Nat.lt_trans b.isLt (Nat.succ_lt_succ q.isLt))), hbX,
      T.vertex q.succ, hqout, ?_⟩
    rw [hqb]
    exact Sym2.eq_swap
  obtain ⟨Splus, hAdjoinPlus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists S (T.edge q) hboundary
  rcases hAdjoinPlus with ⟨hPlusLen, hSPlusInit, hPlusLast⟩
  have hPlusVertex (i : Fin (S.length + 1)) :
      Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) i) =
        S.vertex i := hSPlusInit.2.1 i
  have hPlusEdge (j : Fin S.length) :
      Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j :=
    hSPlusInit.2.2 j
  have hPlusTash : TashkinovTree G e0 phi Splus := by
    exact @helper_hPlusTash_173 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T S N hS omitted hnlt hnlarge a gamma hqcolor hagamma s hsa Splus hPlusLen
        hSPlusInit hPlusLast hPlusVertex hPlusEdge
  have hgammaUsedT : gamma ∈ TreeUsedColors phi T := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, by simp [q]; omega, hqcolor⟩
  have hSCard : (TreeSequenceVertexSet S).card = S.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      S.vertex_injective]
  have hPlusCard : (TreeSequenceVertexSet Splus).card = S.length + 2 := by
    rw [show (TreeSequenceVertexSet Splus).card = Splus.length + 1 by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
        Splus.vertex_injective]]
    omega
  have hsGamma : gamma ∈ MissingColors G phi
      (Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s)) := by
    rw [hPlusVertex, hsa]
    exact hagamma
  have hElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet Splus) :=
    TashTree G k e0 phi Splus htriple hPlusTash
  let U := TreeSequenceVertexSet Splus
  let z := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s)
  have hzU : z ∈ U := by
    simp [z, U, TreeSequenceVertexSet]
  have hzMissing : gamma ∈ MissingColors G phi z := by
    simpa [z] using hsGamma
  have hzNotPresent : gamma ∉ PresentColors G phi z := by
    simpa [MissingColors] using hzMissing
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hpresent : ∀ v, v ∈ U → v ≠ z →
      gamma ∈ PresentColors G phi v := by
    intro v hv hvz
    have hnmissing : gamma ∉ MissingColors G phi v := by
      intro hm
      have hd : Disjoint (MissingColors G phi v) (MissingColors G phi z) :=
        hElem (by simpa [U] using hv) (by simpa [U] using hzU) hvz
      exact (Finset.disjoint_left.mp hd) hm hzMissing
    simpa [MissingColors] using hnmissing
  exact @helper_continuation_856 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T S N hS hmax omitted hnlt hnlarge gamma hqcolor s Splus hPlusLen hSPlusInit
      hPlusLast hPlusVertex hPlusEdge hPlusTash hgammaUsedT hSCard hPlusCard hsGamma hzU
      hzMissing hzNotPresent hproper hpresent
end GoldbergSeymour

end
