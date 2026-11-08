/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OutsideSwapExitPath

public import LeanPool.GoldbergSeymour.SharedFacts.ExtensionBaseClaim45Singleton

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.OutsideSwapPrefixEffects
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Extension Base Claim45Singleton

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_htreeEdgeFixed_771.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj _ TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (_ gammaN
        deltaN beta : Fin k) (u x : V) (_ : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : Fin (Tj.length + (1 : ℕ))),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → rho3 f = rho1 f)) (a : Fin TjPrime.length), rho3 (TjPrime.edge a)
        = rho1 (TjPrime.edge a) := by
  classical
  intro V E _ _ G k e0 Tj seed TjPrime rho1 gammaFirst gammaN deltaN beta u x exitPath zPosition
      rho0 rho3 hmuRho1PrimeFixed a
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨i, hi⟩ := TjPrime.attaches a
  let earlier : Fin (TjPrime.length + 1) :=
    Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))
  have hlaterSet : TjPrime.vertex a.succ ∈
      TreeSequenceVertexSet TjPrime := by
    simp [TreeSequenceVertexSet]
  have hearlierSet : TjPrime.vertex earlier ∈
      TreeSequenceVertexSet TjPrime := by
    simp [TreeSequenceVertexSet]
  have hlaterInc : Incident G (TjPrime.vertex a.succ)
      (TjPrime.edge a) := by
    change TjPrime.vertex a.succ ∈ G.ends (TjPrime.edge a)
    rw [hi]
    simp
  have hearlierInc : Incident G (TjPrime.vertex earlier)
      (TjPrime.edge a) := by
    change TjPrime.vertex earlier ∈ G.ends (TjPrime.edge a)
    rw [hi]
    simp [earlier]
  have hverticesNe : TjPrime.vertex a.succ ≠ TjPrime.vertex earlier := by
    apply TjPrime.vertex_injective.ne
    intro heq
    have hval := congrArg Fin.val heq
    simp [earlier] at hval
    omega
  by_cases hlu : TjPrime.vertex a.succ = u
  · exact hmuRho1PrimeFixed (TjPrime.vertex earlier) hearlierSet
      (by intro heu; exact hverticesNe (hlu.trans heu.symm))
      (TjPrime.edge a) hearlierInc
  · exact hmuRho1PrimeFixed (TjPrime.vertex a.succ) hlaterSet hlu
      (TjPrime.edge a) hlaterInc

private theorem helper_component_edge_avoids_763.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) (u : V),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ TwoColorComponent
        G rho0 gammaN beta (Sum.inl u) ↔ w = u)),
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
  classical
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN beta u rho0 hcomponentIntersection w hw hwu f
      hwf hf
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  let H := TwoColorIncidenceGraph G rho0 gammaN beta
  have hfSupport : Sum.inr f ∈ H.support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := H) (u := Sum.inr f) (v := Sum.inl u)
    · simp
    · exact SimpleGraph.ConnectedComponent.eq.mp hf
  obtain ⟨y, hy⟩ := H.mem_support.mp hfSupport
  have hfColor : rho0 f = some gammaN ∨ rho0 f = some beta := by
    cases y with
    | inl y => exact hy.2
    | inr y => simp [H, TwoColorIncidenceGraph] at hy
  have hadj : H.Adj (Sum.inl w) (Sum.inr f) := by
    simpa [H, TwoColorIncidenceGraph] using And.intro hwf hfColor
  have hwComponent :
      Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change H.connectedComponentMk (Sum.inl w) =
      H.connectedComponentMk (Sum.inl u)
    change H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl u) at hf
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hf
  exact hwu ((hcomponentIntersection w hw).mp hwComponent)

private theorem helper_before_seed_817.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] {G :
    LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tj seed : TreeSequence G e0) (rho1 :
    PartialEdgeColoring E k) (_ gammaN deltaN : Fin k) (terminalSupport u x : V) (_ :
    (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin
    (Tj.length + (1 : ℕ))), TreeSequenceInitialSegment seed Tj → seed.vertex (Fin.last
    seed.length) = terminalSupport → ∀ (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet
    Tj), ∀ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, w ∈ TreeSequenceVertexSet
    seed := by
  classical
  intro V E _ G k e0 Tj seed rho1 gammaFirst gammaN deltaN terminalSupport u x exitPath zPosition
      hseedJ hseedTerminal hterminalTj w hw
  let _ := Fintype.ofFinite V
  unfold TreeVerticesBefore at hw
  obtain ⟨hwJ, i, j, hiw, hjt, hij⟩ := Finset.mem_filter.mp hw
  obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
  have hjLast : j = Fin.castLE (Nat.succ_le_succ hlen)
      (Fin.last seed.length) := by
    apply Tj.vertex_injective
    rw [hjt, hvertices, hseedTerminal]
  have hiBound : i.val < seed.length + 1 := by
    have hjVal : j.val = seed.length := by
      simpa using congrArg Fin.val hjLast
    rw [hjVal] at hij
    omega
  let iSeed : Fin (seed.length + 1) := ⟨i.val, hiBound⟩
  have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iSeed = i := by
    apply Fin.ext
    rfl
  simp only [TreeSequenceVertexSet, Finset.mem_image]
  refine ⟨iSeed, Finset.mem_univ _, ?_⟩
  rw [← hvertices iSeed, hiCast]
  exact hiw

private theorem helper_continuation_1155.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn Tj seed TjPrime : TreeSequence G e0)
        (phiJ rho1 : PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (gammaFirst gammaN deltaN
        beta : Fin k) (terminalSupport u x z : V) (_ : (TwoColorIncidenceGraph G rho1 gammaN
        deltaN).Walk (Sum.inl x) (Sum.inl u)) (zPosition : Fin (Tj.length + (1 : ℕ))) (_ :
        gammaFirst = gammaN) (_ : TreeSequenceInitialSegment Tj Tn) (_ :
        TreeSequenceInitialSegment seed Tj) (_ : TreeSequenceInitialSegment seed TjPrime) (_ :
        seed.vertex (Fin.last seed.length) = terminalSupport) (hterminalTj : terminalSupport ∈
        TreeSequenceVertexSet Tj) (_ : TashkinovClosure rho1 seed TjPrime) (_ :
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime)) (_ : beta ≠ deltaN) (_
        : beta ∈ MissingColors G rho1 u) (_ : deltaN ∈ MissingColors G rho1 terminalSupport)
        (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet Tn) (_ :
        StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ rho1) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport, MissingColors G rho1 v = MissingColors
        G phiJ v)) (_ : TashkinovAugmentationSequence phiJ seed Tj) (_ : (
    ∀ (a : Fin Tj.length) (_ : seed.length ≤ (↑a : ℕ)), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ :
        deltaN ∉ TreeMissingColors phiJ Tj) (hz : z ∈ TreeSequenceVertexSet Tj) (_ : Tj.vertex
        zPosition = z) (_ : seed.length ≤ (↑zPosition : ℕ)) (_ : (
    ∀ w ∈ TreeVerticesBefore Tj z hz, beta ∉ MissingColors G rho1 w)) (_ : (
    ∀ (a : Fin Tj.length) (_ : seed.length ≤ (↑a : ℕ)) (_ : (↑a : ℕ) < (↑zPosition : ℕ)), rho1
        (Tj.edge a) ≠ some beta)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : terminalSupport ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉
        TreeSequenceVertexSet seed),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f)) (_ : IsProperEdgeColoring G
        rho3) (_ : IsOneEdgeUncolored rho3 e0) (_ : gammaN ∈ MissingColors G rho3 u) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ TwoColorComponent
        G rho0 gammaN beta (Sum.inl u) ↔ w = u)),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
        IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧ StableColoringBeforeVertex Tj
        terminalSupport hterminalTj Dprev phiJ rho3 ∧ ((
    ∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ ({ z } : Finset V) ∪ (TreeVerticesBefore TjPrime u
        huPrime ∪ ({ u } : Finset V))).erase u).erase z, MissingColors G rho3 v = MissingColors G
        rho1 v) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ) ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G rho3 z) ∧ (z ∈
        TreeVerticesBefore TjPrime u huPrime → MissingColors G rho3 z = MissingColors G rho1 z)) ∧
        gammaFirst ∈ MissingColors G rho3 u := by
  classical
  intro V E _ _ _ G k e0 Tn Tj seed TjPrime phiJ rho1 Dprev gammaFirst gammaN deltaN beta
      terminalSupport u x z exitPath zPosition hgammaFirst hTjN hseedJ hseedPrime hseedTerminal
      hterminalTj hclosure hprimeElementary hbetaDelta hbeta hdeltaMissing huPrime huOutside hb1
      hb2Missing haugmentation hb2Edges hdeltaPhiJ hz hzPosition hzAfter hzBefore hzEdges
      initial_subset hterminalPrime huSeed rho0 rho3 hrho0Fixed hrho3Proper hrho3One hgammaRho3
      hcomponentIntersection
  have component_edge_avoids :
    ∀ (w : V), w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → w ≠ u →
    ∀ f : E, Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact @helper_component_edge_avoids_763 V E inferInstance inferInstance inferInstance G k e0
        Tn TjPrime rho1 gammaN deltaN beta u hcomponentIntersection
  have hmuRho0Fixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → rho3 f = rho0 f := by
    intro w hw hwu f hwf
    have hf := component_edge_avoids w hw hwu f hwf
    simp [rho3, TwoColorComponentSwap, hf]
  have hmuRho1PrimeFixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      ∀ f : E, Incident G w f → rho3 f = rho1 f := by
    intro w hw hwu f hwf
    rw [hmuRho0Fixed w (Finset.mem_union.mpr (Or.inr hw)) hwu f hwf]
    exact hrho0Fixed f ⟨w, hw, hwf⟩
  have missing_eq_of_incident_eq : ∀ (w : V),
      (∀ f : E, Incident G w f → rho3 f = rho1 f) →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hfixed
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hnew hold
      obtain ⟨f, hwf, hfc⟩ := hold
      exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
    · intro hold hnew
      obtain ⟨f, hwf, hfc⟩ := hnew
      exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩
  have before_seed : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet seed := by
    exact @helper_before_seed_817 V E inferInstance G k e0 Tj seed rho1 gammaFirst gammaN deltaN
        terminalSupport u x exitPath zPosition hseedJ hseedTerminal hterminalTj
  have before_prime : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet TjPrime := by
    intro w hw
    exact initial_subset hseedPrime (before_seed w hw)
  have hE1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3 := by
    unfold StableColoringBeforeVertex at hb1 ⊢
    have before_ne : ∀ w : V,
        w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj → w ≠ u := by
      intro w hw hwu
      subst w
      exact huSeed (before_seed u hw)
    constructor
    · intro f hf hcolor
      obtain ⟨w, hw, hwf⟩ := hf
      rw [hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw) f hwf]
      exact hb1.1 f ⟨w, hw, hwf⟩ hcolor
    · intro w hw
      exact (missing_eq_of_incident_eq w
        (hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw))).trans
          (hb1.2 w hw)
  have hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hw hwu
    exact missing_eq_of_incident_eq w (hmuRho1PrimeFixed w hw hwu)
  have htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      rho3 (TjPrime.edge a) = rho1 (TjPrime.edge a) := by
    exact @helper_htreeEdgeFixed_771 V E inferInstance inferInstance G k e0 Tj seed
        TjPrime rho1 gammaFirst gammaN deltaN beta u x exitPath zPosition hmuRho1PrimeFixed
  have rho0_unaffected : ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c) := by
    exact @SharedFacts.ExtensionBaseClaim45Singleton.rho0_unaffected V E inferInstance
        inferInstance G k e0 TjPrime rho1 deltaN
        beta
  have hE2 := P2966_T1_OutsideSwapPrefixEffects Tn Tj seed TjPrime
    phiJ rho1 rho0 rho3 deltaN beta terminalSupport u z zPosition
    hTjN hterminalPrime hclosure.2 hprimeElementary hbetaDelta hbeta
    hdeltaMissing hb2Missing haugmentation hb2Edges hdeltaPhiJ hz
    hzPosition hzAfter huPrime huOutside hzBefore hzEdges rfl hrho0Fixed hmuRho0Fixed
    hmissingPrime htreeEdgeFixed rho0_unaffected
  have hgammaFirstRho3 : gammaFirst ∈ MissingColors G rho3 u := by
    rw [hgammaFirst]
    exact hgammaRho3
  exact ⟨hrho3Proper, hrho3One, hE1, hE2, hgammaFirstRho3⟩

theorem ExtensionBaseClaim45Singleton {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 : PartialEdgeColoring E k)
    (Dprev supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN beta : Fin k)
    (terminalSupport u x z : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl x) (Sum.inl u))
    (zPosition : Fin (Tj.length + 1))
    (hgammaFirst : gammaFirst = gammaN)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hgammaDelta : gammaN ≠ deltaN)
    (hbetaGamma : beta ≠ gammaN)
    (hbetaDelta : beta ≠ deltaN)
    (hbeta : beta ∈ MissingColors G rho1 u)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huOutside : u ∉ TreeSequenceVertexSet Tn)
    (hexitPath : exitPath.IsPath)
    (hexitLength : 2 ≤ exitPath.length)
    (hexitSupport : ∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support)
    (hexitIntersection : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      (Sum.inl w ∈ exitPath.support ↔ w = u))
    (hexitBoundary : ∃ g ∈ BoundaryColorEdges G rho1
        (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
      Incident G u g ∧ Sum.inr g ∈ exitPath.support)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hz : z ∈ TreeSequenceVertexSet Tj)
    (hzPosition : Tj.vertex zPosition = z)
    (hzAfter : seed.length ≤ zPosition.val)
    (_ :
      (seed.length < zPosition.val ∧
          beta ∈ MissingColors G rho1 z ∧
          ∀ r : Fin (Tj.length + 1),
            seed.length < r.val → r.val < zPosition.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
        (zPosition = Fin.last Tj.length ∧
          ∀ r : Fin (Tj.length + 1), seed.length < r.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)))
    (hzBefore : ∀ w ∈ TreeVerticesBefore Tj z hz,
      beta ∉ MissingColors G rho1 w)
    (hzEdges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) :
    let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
    let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
    IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧
      StableColoringBeforeVertex Tj terminalSupport hterminalTj
        Dprev phiJ rho3 ∧
      ((∀ v : V,
        v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
            (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v) ∧
        (∀ f : E,
          ((∃ a : Fin Tj.length,
              seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                Tj.edge a = f) ∨
            (∃ (a : Fin TjPrime.length)
              (uPosition : Fin (TjPrime.length + 1)),
              TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                TjPrime.edge a = f)) →
          rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z →
          deltaN ∈ MissingColors G rho3 z) ∧
        (z ∈ TreeVerticesBefore TjPrime u huPrime →
          MissingColors G rho3 z = MissingColors G rho1 z)) ∧
      gammaFirst ∈ MissingColors G rho3 u := by
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    initial_subset hseedPrime hterminalSeed
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hu
    exact huOutside (initial_subset hTjN (initial_subset hseedJ hu))
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  have hbetaTree : beta ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨u, huPrime, hbeta⟩
  have hdeltaTree : deltaN ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨terminalSupport, hterminalPrime,
      hdeltaMissing⟩
  have houtside := OutsideTreeColorSwapStable TjPrime supportColors rho1
    beta deltaN hrhoProper hrhoOne hclosure.2 hbetaTree hdeltaTree
    hbetaDelta
  change IsProperEdgeColoring G rho0 ∧ IsOneEdgeUncolored rho0 e0 ∧
      StableColoring TjPrime supportColors rho1 rho0 ∧
      ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f at houtside
  rcases houtside with ⟨hrho0Proper, hrho0One, hrho0Stable, hrho0Fixed⟩
  have hgammaBeta : gammaN ≠ beta := Ne.symm hbetaGamma
  have hrho3Proper : IsProperEdgeColoring G rho3 :=
    TwoColorComponentSwapProper G rho0 gammaN beta hgammaBeta
      hrho0Proper (Sum.inl u)
  have hrho3One : IsOneEdgeUncolored rho3 e0 := by
    unfold IsOneEdgeUncolored at hrho0One ⊢
    constructor
    · simp [rho3, TwoColorComponentSwap, hrho0One.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hrho0One.2 f hfe
      have hne : rho3 f ≠ none := by
        by_cases hK : Sum.inr f ∈
            TwoColorComponent G rho0 gammaN beta (Sum.inl u)
        · by_cases hcg : c = gammaN
          · simp [rho3, TwoColorComponentSwap, hK, hc, hcg]
          · by_cases hcb : c = beta
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcb,
                hbetaGamma]
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb]
        · simp [rho3, TwoColorComponentSwap, hK, hc]
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
      exact ⟨d, hd.symm⟩
  have hbetaRho0 : beta ∈ MissingColors G rho0 u := by
    rw [hrho0Stable.2 u huPrime]
    exact hbeta
  obtain ⟨g, hgBoundary, hug, hgExit⟩ := hexitBoundary
  have hgRho1 : rho1 g = some gammaN :=
    (Finset.mem_filter.mp hgBoundary).2
  have hgRho0 : rho0 g = some gammaN := by
    rw [hrho0Fixed g ⟨u, huPrime, hug⟩]
    exact hgRho1
  have hgComponent : Sum.inr g ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr g) := ⟨hug, Or.inl hgRho0⟩
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hgRho3 : rho3 g = some beta := by
    simp [rho3, TwoColorComponentSwap, hgComponent, hgRho0]
  have hbetaRho3 : beta ∉ MissingColors G rho3 u := by
    intro hb
    have hbPresent : beta ∉ PresentColors G rho3 u := by
      simpa [MissingColors] using hb
    apply hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hug, hgRho3⟩
  have hgammaRho3 : gammaN ∈ MissingColors G rho3 u := by
    exact (TwoColorComponentSwapMissingBehavior G rho0 gammaN beta hgammaBeta hrho0Proper
      (Sum.inl u)).2.2.1 u rfl hbetaRho0
  have hcomponentExit :
      {y : Sum V E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact outsideSwapExitPathComponent TjPrime rho1 gammaN deltaN beta p exitPath
      hclosure.2 hgammaDelta hbetaDelta hgammaBeta hbeta hpath hcomponent
      (fun hx => hxOutside (Finset.mem_union.mpr (Or.inr hx))) huPrime hexitPath
      (incidenceSubpathFirstEqLast p exitPath hpath hexitSupport (by omega))
      (fun w hw he => (hexitIntersection w (Finset.mem_union.mpr (Or.inr hw))).mp he)
      hrho0Proper hbetaRho0 hug hgExit hgRho1
  have hcomponentIntersection :
    ∀ w : V, w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → (Sum.inl w ∈
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) ↔ w = u) := by
    intro w hw
    rw [← hcomponentExit]
    exact hexitIntersection w hw
  exact @helper_continuation_1155 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@Tn) (@Tj) (@seed) (@TjPrime) (@phiJ) (@rho1) (@Dprev) (@gammaFirst) (@gammaN)
      (@deltaN) (@beta) (@terminalSupport) (@u) (@x) (@z) (@exitPath) (@zPosition) (@hgammaFirst)
      (@hTjN) (@hseedJ) (@hseedPrime) (@hseedTerminal) (@hterminalTj) (@hclosure)
      (@hprimeElementary) (@hbetaDelta) (@hbeta) (@hdeltaMissing) (@huPrime) (@huOutside) (@hb1)
      (@hb2Missing) (@haugmentation) (@hb2Edges) (@hdeltaPhiJ) (@hz) (@hzPosition) (@hzAfter)
      (@hzBefore) (@hzEdges) (@initial_subset) (@hterminalPrime) (@huSeed) (@hrho0Fixed)
      (@hrho3Proper) (@hrho3One) (@hgammaRho3) (@hcomponentIntersection)
end GoldbergSeymour

end
