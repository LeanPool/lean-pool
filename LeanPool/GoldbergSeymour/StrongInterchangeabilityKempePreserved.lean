/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapDisjointPairGraph
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapPreservesDisjointComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.TwoColorPathComponentNotCycle

/-!
# Strong Interchangeability Kempe Preserved

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_finishActive_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (t : Fin ett.rounds) (vs vt : V) (gammaS
        deltaS gammaT deltaT : Fin k) (phi : PartialEdgeColoring E k) (z : V ⊕ E),
        TwoColorNontrivialPathComponent G phi gammaT deltaT z →
    let phiStar : PartialEdgeColoring E k := TwoColorComponentSwap G phi gammaT deltaT z;
    let K : Set (V ⊕ E) := TwoColorComponent G phi gammaT deltaT z;
    ∀ (r : Fin ett.rounds) (v : V), TwoColorComponentCycle G phi gammaS deltaS (Sum.inl v) →
        Sum.inl vs ∉ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) → vs = vt →
    ∀ (rt : Fin ett.rounds), (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc), v ≠ vt →
        TwoColorComponentCycle G phi gammaT deltaT (Sum.inl v) ∧ Sum.inl vt ∉ TwoColorComponent G
        phi gammaT deltaT (Sum.inl v) ∧
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phi gammaT deltaT (Sum.inl v) → w ∈
        TreeSequenceVertexSet (ett.series.data.tree rt.succ.castSucc)) →
    let slotTree : Fin ett.rounds → TreeSequence G e0 := fun (q : Fin ett.rounds) =>
        ett.series.data.tree q.succ.castSucc; TreeSequenceVertexSet (slotTree r) ⊆
        TreeSequenceVertexSet (slotTree t) → (
    ∀ (e : E), Sum.inr e ∈ K → phi e = some gammaT ∨ phi e = some deltaT) → TwoColorComponentCycle
        G phiStar gammaS deltaS (Sum.inl v) ∧ Sum.inl vs ∉ TwoColorComponent G phiStar gammaS
        deltaS (Sum.inl v) ∧
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet (slotTree r) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t vs vt gammaS deltaS gammaT deltaT phi z hpath
      phiStar K r v hcycle havoid hcontained hsupportEq rt htComponents slotTree hvertexSubset
      hactive
  have hvertexDisjoint :
    ∀ y : V, Sum.inl y ∈ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → Sum.inl y ∈ K → False
  := by
    intro y hyC hyK
    have hyR := hcontained y hyC
    have hyT : y ∈ TreeSequenceVertexSet (slotTree t) :=
      hvertexSubset (by simpa [slotTree] using hyR)
    have hyEq : y = vt := by
      by_contra hyne
      obtain ⟨hyCycle, -, -⟩ := htComponents y
        (by simpa [slotTree] using hyT) hyne
      rcases hpath.1 with ⟨hne, leaf, hleafK, hleaf⟩
      have hleafY : leaf ∈
          TwoColorComponent G phi gammaT deltaT (Sum.inl y) := by
        change (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk
            leaf =
          (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk
            (Sum.inl y)
        change (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk
            leaf =
          (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk z at hleafK
        change (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk
            (Sum.inl y) =
          (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk z at hyK
        exact hleafK.trans hyK.symm
      have hpathY : TwoColorPathComponent G phi gammaT deltaT (Sum.inl y) :=
        ⟨hne, leaf, hleafY, hleaf⟩
      exact (TwoColorPathComponentNotCycle G phi gammaT deltaT
        (Sum.inl y) hpathY) hyCycle
    subst y
    exact havoid (by simpa [hsupportEq] using hyC)
  have hdisjoint : Disjoint
      (TwoColorComponent G phi gammaS deltaS (Sum.inl v)) K := by
    apply Set.disjoint_left.mpr
    intro node hnC hnK
    cases node with
    | inl y => exact hvertexDisjoint y hnC hnK
    | inr e =>
        rcases hcycle with ⟨cycle, hfull⟩
        have heSupport : Sum.inr e ∈ cycle.walk.support :=
          (hfull (Sum.inr e)).2 hnC
        obtain ⟨node, -, hnodeEdge⟩ :=
          SimpleGraph.adj_of_mem_walk_support cycle.walk
            cycle.isCycle.not_nil heSupport
        cases node with
        | inl y =>
            have hsAdj : (TwoColorIncidenceGraph G phi gammaS deltaS).Adj
                (Sum.inl y) (Sum.inr e) := hnodeEdge.symm
            have hsData : Incident G y e ∧
                (phi e = some gammaS ∨ phi e = some deltaS) := by
              simpa [TwoColorIncidenceGraph] using hsAdj
            have htAdj : (TwoColorIncidenceGraph G phi gammaT deltaT).Adj
                (Sum.inl y) (Sum.inr e) := by
              simpa [TwoColorIncidenceGraph] using ⟨hsData.1, hactive e hnK⟩
            have hyC : Sum.inl y ∈
                TwoColorComponent G phi gammaS deltaS (Sum.inl v) := by
              change (TwoColorIncidenceGraph G phi gammaS deltaS).connectedComponentMk
                  (Sum.inl y) =
                (TwoColorIncidenceGraph G phi gammaS deltaS).connectedComponentMk
                  (Sum.inl v)
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hsAdj).trans hnC
            have hyK : Sum.inl y ∈ K := by
              change (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk
                  (Sum.inl y) =
                (TwoColorIncidenceGraph G phi gammaT deltaT).connectedComponentMk z
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                htAdj).trans hnK
            exact hvertexDisjoint y hyC hyK
        | inr f => simp [TwoColorIncidenceGraph] at hnodeEdge
  have hcomponent := TwoColorComponentSwapPreservesDisjointComponent G phi
    gammaS deltaS gammaT deltaT z (Sum.inl v) hactive hdisjoint
  refine ⟨?_, ?_, ?_⟩
  · rcases hcycle with ⟨cycle, hfull⟩
    let Hstar := TwoColorIncidenceGraph G phiStar gammaS deltaS
    have hedgeTransfer : ∀ edge, edge ∈ cycle.walk.edges →
        edge ∈ Hstar.edgeSet := by
      intro edge hedge
      induction edge using Sym2.inductionOn with
      | _ a b =>
          have haSupport := cycle.walk.fst_mem_support_of_mem_edges hedge
          have hbSupport := cycle.walk.snd_mem_support_of_mem_edges hedge
          have haC := (hfull a).1 haSupport
          have hbC := (hfull b).1 hbSupport
          have habOld : (TwoColorIncidenceGraph G phi gammaS deltaS).Adj a b := by
            simpa using cycle.walk.edges_subset_edgeSet hedge
          cases a with
          | inl y =>
              cases b with
              | inl w => simp [TwoColorIncidenceGraph] at habOld
              | inr e =>
                  have heNotK : Sum.inr e ∉ K := by
                    intro heK
                    exact Set.disjoint_left.mp hdisjoint hbC heK
                  simpa [Hstar, phiStar, TwoColorIncidenceGraph,
                    TwoColorComponentSwap, K, heNotK] using habOld
          | inr e =>
              cases b with
              | inl y =>
                  have heNotK : Sum.inr e ∉ K := by
                    intro heK
                    exact Set.disjoint_left.mp hdisjoint haC heK
                  simpa [Hstar, phiStar, TwoColorIncidenceGraph,
                    TwoColorComponentSwap, K, heNotK] using habOld
              | inr f => simp [TwoColorIncidenceGraph] at habOld
    let newWalk := cycle.walk.transfer Hstar hedgeTransfer
    refine ⟨⟨cycle.base, newWalk, cycle.isCycle.transfer hedgeTransfer⟩, ?_⟩
    intro node
    rw [SimpleGraph.Walk.support_transfer]
    have hn : node ∈
        TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) ↔
        node ∈ TwoColorComponent G phi gammaS deltaS (Sum.inl v) := by
      simpa [phiStar] using Set.ext_iff.mp hcomponent node
    exact (hfull node).trans hn.symm
  · simpa [phiStar] using (Set.ext_iff.mp hcomponent (Sum.inl vs)).not.mpr havoid
  · intro w hw
    apply hcontained w
    have hn := Set.ext_iff.mp hcomponent (Sum.inl w)
    exact hn.mp (by simpa [phiStar] using hw)

private theorem helper_branch_358.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (vs : V) (gammaS deltaS gammaT deltaT :
        Fin k) (phi : PartialEdgeColoring E k) (z : V ⊕ E),
    let phiStar : PartialEdgeColoring E k := TwoColorComponentSwap G phi gammaT deltaT z;
    let K : Set (V ⊕ E) := TwoColorComponent G phi gammaT deltaT z;
    ∀ (r : Fin ett.rounds) (v : V), TwoColorComponentCycle G phi gammaS deltaS (Sum.inl v) →
        Sum.inl vs ∉ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) →
    let slotTree : Fin ett.rounds → TreeSequence G e0 := fun (q : Fin ett.rounds) =>
        ett.series.data.tree q.succ.castSucc; ((
    ∀ (e : E), Sum.inr e = z → phi e = some gammaT ∨ phi e = some deltaT) →
    ∀ (e : E), Sum.inr e ∈ K → phi e = some gammaT ∨ phi e = some deltaT) → ((
    ∀ (e : E), Sum.inr e ∈ K → phi e = some gammaT ∨ phi e = some deltaT) → TwoColorComponentCycle
        G phiStar gammaS deltaS (Sum.inl v) ∧ Sum.inl vs ∉ TwoColorComponent G phiStar gammaS
        deltaS (Sum.inl v) ∧
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet (slotTree r)) →
    ∀ (f : E), z = Sum.inr f → TwoColorComponentCycle G (TwoColorComponentSwap G phi gammaT deltaT
        (Sum.inr f)) gammaS deltaS (Sum.inl v) ∧ Sum.inl vs ∉ TwoColorComponent G
        (TwoColorComponentSwap G phi gammaT deltaT (Sum.inr f)) gammaS deltaS (Sum.inl v) ∧
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (TwoColorComponentSwap G phi gammaT deltaT (Sum.inr
        f)) gammaS deltaS (Sum.inl v) → w ∈ TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett vs gammaS deltaS gammaT deltaT phi z phiStar K r
      v hcycle havoid hcontained slotTree hrootActive finishActive f hz
  by_cases hfActive : phi f = some gammaT ∨ phi f = some deltaT
  · have hresult := finishActive (hrootActive (by
      intro e he
      have hef : e = f := Sum.inr.inj (he.trans hz)
      simpa [hef] using hfActive))
    simpa [phiStar, slotTree, hz] using hresult
  · have hfGamma : phi f ≠ some gammaT := fun h => hfActive (Or.inl h)
    have hfDelta : phi f ≠ some deltaT := fun h => hfActive (Or.inr h)
    have hrootEmpty :
        (TwoColorIncidenceGraph G phi gammaT deltaT).neighborSet (Sum.inr f) = ∅ := by
      ext node
      cases node <;> simp [TwoColorIncidenceGraph, hfGamma, hfDelta]
    have hphiEq : phiStar = phi := by
      funext e
      by_cases heK : Sum.inr e ∈ K
      · have hreach : (TwoColorIncidenceGraph G phi gammaT deltaT).Reachable
            (Sum.inr e) (Sum.inr f) := by
          simpa [K, hz] using SimpleGraph.ConnectedComponent.exact heK
        have hnodeEq : (Sum.inr e : Sum V E) = Sum.inr f := by
          by_contra hne
          exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
            hne hrootEmpty) hreach
        have hef : e = f := Sum.inr.inj hnodeEq
        subst e
        simp [phiStar, TwoColorComponentSwap, K, heK, hfGamma, hfDelta]
      · simp [phiStar, TwoColorComponentSwap, K, heK]
    have hresult :
        TwoColorComponentCycle G phiStar gammaS deltaS (Sum.inl v) ∧
          Sum.inl vs ∉ TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) ∧
          ∀ w : V,
            Sum.inl w ∈ TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) →
            w ∈ TreeSequenceVertexSet (slotTree r) := by
      rw [hphiEq]
      simpa [slotTree] using ⟨hcycle, havoid, hcontained⟩
    simpa [phiStar, slotTree, hz] using hresult

private theorem helper_branch_124.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (s t : Fin ett.rounds) (vs vt : V)
        (gammaS deltaS gammaT deltaT : Fin k) (phi : PartialEdgeColoring E k) (z : V ⊕ E), vs ≠ vt
        ∨ (↑s : ℕ) < (↑t : ℕ) → TwoColorNontrivialPathComponent G phi gammaT deltaT z →
        ETTStrongInterchangeable ett t vt phi gammaT deltaT →
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G phi gammaT deltaT z;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi gammaT deltaT z;
    ∀ (r : Fin ett.rounds), (
    ∀ (q : Fin ett.rounds), (↑s : ℕ) < (↑q : ℕ) → (↑q : ℕ) < (↑r : ℕ) → ett.series.data.kind
        q.succ = some TashkinovExtensionKind.RE) →
    ∀ (v : V), TwoColorComponentCycle G phi gammaS deltaS (Sum.inl v) → Sum.inl vs ∉
        TwoColorComponent G phi gammaS deltaS (Sum.inl v) → (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G phi gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) → ¬vs ≠ vt →
        TwoColorComponentCycle G (TwoColorComponentSwap G phi gammaT deltaT z) gammaS deltaS
        (Sum.inl v) ∧ Sum.inl vs ∉ TwoColorComponent G (TwoColorComponentSwap G phi gammaT deltaT
        z) gammaS deltaS (Sum.inl v) ∧
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (TwoColorComponentSwap G phi gammaT deltaT z)
        gammaS deltaS (Sum.inl v) → w ∈ TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett s t vs vt gammaS deltaS gammaT deltaT phi z
      hrelative hpath htSI phiStar K r hbetween v hcycle havoid hcontained hsupports
  have hst : s.val < t.val := hrelative.resolve_left hsupports
  have hsupportEq : vs = vt := not_ne_iff.mp hsupports
  rcases htSI with
    ⟨_, hkindT, _, rt, _, _, _, htComponents⟩
  have hrt : r.val ≤ t.val := by
    by_contra hnot
    have htBefore : t.val < r.val := by omega
    have htRE := hbetween t hst htBefore
    rw [hkindT] at htRE
    simp at htRE
  let slotTree (q : Fin ett.rounds) : TreeSequence G e0 :=
    ett.series.data.tree q.succ.castSucc
  have hrtSegment : TreeSequenceInitialSegment (slotTree r) (slotTree t) := by
    exact ett.series.stageInitialSegmentOfLE r.succ.castSucc t.succ.castSucc
      (Nat.zero_lt_succ _) (Nat.succ_le_succ hrt)
  have hvertexSubset : TreeSequenceVertexSet (slotTree r) ⊆
      TreeSequenceVertexSet (slotTree t) :=
    TreeSequenceInitialSegmentVertexSetSubset hrtSegment
  have hrootActive : (∀ e : E, Sum.inr e = z →
      phi e = some gammaT ∨ phi e = some deltaT) →
      ∀ e : E, Sum.inr e ∈ K →
        phi e = some gammaT ∨ phi e = some deltaT := by
    intro hroot e heK
    by_cases hez : Sum.inr e = z
    · exact hroot e hez
    · exact TwoColorComponent.edge_colors_of_ne heK hez
  have finishActive := @helper_finishActive_227 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett t vs vt gammaS deltaS gammaT deltaT phi z hpath r v hcycle havoid
      hcontained hsupportEq rt htComponents hvertexSubset
  cases hz : z with
  | inl u =>
      have hresult := finishActive
        (hrootActive (by intro e he; simp [hz] at he))
      simpa [phiStar, slotTree, hz] using hresult
  | inr f =>
      exact @helper_branch_358 V E inferInstance inferInstance inferInstance G k e0
          input T generating ett vs gammaS deltaS gammaT deltaT phi z r v hcycle havoid
          hcontained hrootActive finishActive f hz
theorem StrongInterchangeabilityKempePreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (s t : Fin ett.rounds) (vs vt : V)
    (gammaS deltaS gammaT deltaT : Fin k)
    (phi : PartialEdgeColoring E k) (z : Sum V E)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (_ : ett.series.data.gamma s.succ = some gammaS)
    (_ : ett.series.data.delta s.succ = some deltaS)
    (_ : ett.series.data.gamma t.succ = some gammaT)
    (_ : ett.series.data.delta t.succ = some deltaT)
    (hrelative : vs ≠ vt ∨ s.val < t.val)
    (hdifferentColors : vs ≠ vt →
      Disjoint ({gammaS, deltaS} : Finset (Fin k)) {gammaT, deltaT})
    (hpath : TwoColorNontrivialPathComponent G phi gammaT deltaT z)
    (htSI : ETTStrongInterchangeable ett t vt phi gammaT deltaT)
    (hsSI : ETTStrongInterchangeable ett s vs phi gammaS deltaS) :
    let phiStar := TwoColorComponentSwap G phi gammaT deltaT z
    IsProperEdgeColoring G phiStar ∧ IsOneEdgeUncolored phiStar e0 ∧
      ETTStrongInterchangeable ett s vs phiStar gammaS deltaS := by
  classical
  dsimp
  let phiStar := TwoColorComponentSwap G phi gammaT deltaT z
  let K := TwoColorComponent G phi gammaT deltaT z
  have hneT : gammaT ≠ deltaT := hpath.1.1
  have hproperStar : IsProperEdgeColoring G phiStar := by
    simpa [phiStar] using
      TwoColorComponentSwapProper G phi gammaT deltaT hneT hproper z
  have honeStar : IsOneEdgeUncolored phiStar e0 := by
    constructor
    · simp [phiStar, TwoColorComponentSwap, hone.1]
    · intro e he0
      obtain ⟨c, hc⟩ := hone.2 e he0
      by_cases heK : Sum.inr e ∈ K
      · by_cases heGamma : phi e = some gammaT
        · exact ⟨deltaT, by
            simp [phiStar, TwoColorComponentSwap, K, heK, heGamma]⟩
        · by_cases heDelta : phi e = some deltaT
          · exact ⟨gammaT, by
              simp [phiStar, TwoColorComponentSwap, K, heK, heDelta]⟩
          · exact ⟨c, by
              simpa [phiStar, TwoColorComponentSwap, K, heK, heGamma, heDelta]
                using hc⟩
      · exact ⟨c, by
          simpa [phiStar, TwoColorComponentSwap, K, heK] using hc⟩
  refine ⟨hproperStar, honeStar, ?_⟩
  rcases hsSI with
    ⟨hneS, hkindS, hvertexS, r, hsr, hrNotRE, hbetween, hsComponents⟩
  refine ⟨hneS, hkindS, hvertexS, r, hsr, hrNotRE, hbetween, ?_⟩
  intro v hvTs hvSupport
  obtain ⟨hcycle, havoid, hcontained⟩ := hsComponents v hvTs hvSupport
  by_cases hsupports : vs ≠ vt
  · have hgraph := TwoColorComponentSwapDisjointPairGraph G phi
        gammaS deltaS gammaT deltaT z (hdifferentColors hsupports)
    have hcomponent : TwoColorComponent G phiStar gammaS deltaS (Sum.inl v) =
        TwoColorComponent G phi gammaS deltaS (Sum.inl v) := by
      unfold TwoColorComponent
      simp only [phiStar]
      rw [hgraph]
    refine ⟨?_, ?_, ?_⟩
    · rcases hcycle with ⟨cycle, hfull⟩
      let Hstar := TwoColorIncidenceGraph G phiStar gammaS deltaS
      have hedgeTransfer : ∀ edge, edge ∈ cycle.walk.edges →
          edge ∈ Hstar.edgeSet := by
        intro edge hedge
        have hold := cycle.walk.edges_subset_edgeSet hedge
        simpa [Hstar, phiStar, hgraph] using hold
      let newWalk := cycle.walk.transfer Hstar hedgeTransfer
      refine ⟨⟨cycle.base, newWalk, cycle.isCycle.transfer hedgeTransfer⟩, ?_⟩
      intro node
      rw [SimpleGraph.Walk.support_transfer]
      have hn := Set.ext_iff.mp hcomponent node
      exact (hfull node).trans hn.symm
    · rw [hcomponent]
      exact havoid
    · intro w hw
      apply hcontained w
      rw [← hcomponent]
      exact hw
  · exact @helper_branch_124 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett s t vs vt gammaS deltaS gammaT deltaT phi z hrelative hpath htSI r
      hbetween v hcycle havoid hcontained hsupports
end GoldbergSeymour

end
