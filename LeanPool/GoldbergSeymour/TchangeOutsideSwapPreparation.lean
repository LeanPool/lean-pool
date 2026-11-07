/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPathOutsideSwap

public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.TchangeCounterexampleMeasure
public import LeanPool.GoldbergSeymour.TreeVertexOrder

/-!
# Tchange Outside Swap Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hnormalized_63.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0) (i1 : Fin
        (C.T.length + (1 : ℕ))), C.T.vertex i1 = C.b1 →
    ∀ (i2 : Fin (C.T.length + (1 : ℕ))), C.T.vertex i2 = C.b2 →
    ∀ (i3 : Fin (C.T.length + (1 : ℕ))), C.T.vertex i3 = C.b3 → (↑i1 : ℕ) ≠ (↑i2 : ℕ) → (↑i1 : ℕ)
        ≠ (↑i3 : ℕ) → (↑i2 : ℕ) ≠ (↑i3 : ℕ) →
    ∃ (N : TchangeCounterexample G k e0), N.T = C.T ∧ N.phi = C.phi ∧ N.a = C.a ∧ N.b = C.b ∧
        TreeVertexOrder N.T N.b1 N.b3 ∧ TreeVertexOrder N.T N.b2 N.b3 ∧
        TchangeCounterexampleMeasure N = TchangeCounterexampleMeasure C := by
  classical
  intro V E _ _ _ _ G k e0 C i1 hi1 i2 hi2 i3 hi3 hi12 hi13 hi23
  by_cases h13 : i1.val < i3.val
  · by_cases h23 : i2.val < i3.val
    · exact ⟨C, rfl, rfl, rfl, rfl,
        ⟨i1, i3, hi1, hi3, h13⟩,
        ⟨i2, i3, hi2, hi3, h23⟩, rfl⟩
    · have h32 : i3.val < i2.val := by omega
      let N : TchangeCounterexample G k e0 := { C with
        a2 := C.a3
        b2 := C.b3
        a3 := C.a2
        b3 := C.b2
        P2 := C.P3
        P3 := C.P2
        exit2 := C.exit3
        exit3 := C.exit2
        disjoint12 := C.disjoint13
        disjoint13 := C.disjoint12
        disjoint23 := fun x hx h => C.disjoint23 x h hx
        remote12 := C.remote13
        remote13 := C.remote12
        remote23 := C.remote23.symm
        tree12 := C.tree13
        tree13 := C.tree12
        tree23 := C.tree23.symm
        f2 := C.f3
        f3 := C.f2
        boundary2 := C.boundary3
        boundary3 := C.boundary2
        incident2 := C.incident3
        incident3 := C.incident2
        support2 := C.support3
        support3 := C.support2 }
      refine ⟨N, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · exact ⟨i1, i2, hi1, hi2, h13.trans h32⟩
      · exact ⟨i3, i2, hi3, hi2, h32⟩
      · simp [N, TchangeCounterexampleMeasure, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
  · have h31 : i3.val < i1.val := by omega
    by_cases h21 : i2.val < i1.val
    · let N : TchangeCounterexample G k e0 := { C with
        a1 := C.a2
        b1 := C.b2
        a2 := C.a3
        b2 := C.b3
        a3 := C.a1
        b3 := C.b1
        P1 := C.P2
        P2 := C.P3
        P3 := C.P1
        exit1 := C.exit2
        exit2 := C.exit3
        exit3 := C.exit1
        disjoint12 := C.disjoint23
        disjoint13 := fun x hx h => C.disjoint12 x h hx
        disjoint23 := fun x hx h => C.disjoint13 x h hx
        remote12 := C.remote23
        remote13 := C.remote12.symm
        remote23 := C.remote13.symm
        tree12 := C.tree23
        tree13 := C.tree12.symm
        tree23 := C.tree13.symm
        f1 := C.f2
        f2 := C.f3
        f3 := C.f1
        boundary1 := C.boundary2
        boundary2 := C.boundary3
        boundary3 := C.boundary1
        incident1 := C.incident2
        incident2 := C.incident3
        incident3 := C.incident1
        support1 := C.support2
        support2 := C.support3
        support3 := C.support1 }
      refine ⟨N, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · exact ⟨i2, i1, hi2, hi1, h21⟩
      · exact ⟨i3, i1, hi3, hi1, h31⟩
      · simp [N, TchangeCounterexampleMeasure, Nat.add_comm,
          Nat.add_assoc]
    · have h12 : i1.val < i2.val := by omega
      have h32 : i3.val < i2.val := h31.trans h12
      let N : TchangeCounterexample G k e0 := { C with
        a2 := C.a3
        b2 := C.b3
        a3 := C.a2
        b3 := C.b2
        P2 := C.P3
        P3 := C.P2
        exit2 := C.exit3
        exit3 := C.exit2
        disjoint12 := C.disjoint13
        disjoint13 := C.disjoint12
        disjoint23 := fun x hx h => C.disjoint23 x h hx
        remote12 := C.remote13
        remote13 := C.remote12
        remote23 := C.remote23.symm
        tree12 := C.tree13
        tree13 := C.tree12
        tree23 := C.tree23.symm
        f2 := C.f3
        f3 := C.f2
        boundary2 := C.boundary3
        boundary3 := C.boundary2
        incident2 := C.incident3
        incident3 := C.incident2
        support2 := C.support3
        support3 := C.support2 }
      refine ⟨N, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · exact ⟨i1, i2, hi1, hi2, h12⟩
      · exact ⟨i3, i2, hi3, hi2, h32⟩
      · simp [N, TchangeCounterexampleMeasure, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]

private theorem helper_branch_199.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C N : TchangeCounterexample G k e0), N.T =
        C.T → N.phi = C.phi → N.a = C.a → N.b = C.b → TreeVertexOrder N.T N.b1 N.b3 →
        TreeVertexOrder N.T N.b2 N.b3 → TchangeCounterexampleMeasure N =
        TchangeCounterexampleMeasure C →
    ∀ gamma ∈ MissingColors G N.phi N.b3, gamma ∈ TreeMissingColors N.phi N.T → gamma ≠ N.b → ¬N.a
        = gamma →
    ∃ (D : TchangeCounterexample G k e0), D.T = C.T ∧ D.b = C.b ∧ D.phi = OutsideTreeColorSwap C.T
        C.phi C.a D.a ∧ D.a ∈ MissingColors G D.phi D.b3 ∧ TreeVertexOrder D.T D.b1 D.b3 ∧
        TreeVertexOrder D.T D.b2 D.b3 ∧ TchangeCounterexampleMeasure D =
        TchangeCounterexampleMeasure C := by
  classical
  intro V E _ _ _ _ G k e0 C N hNT hNphi hNa hNb horder1 horder2 hmeasure gamma hgamma hgammaTree
      hgammaB hag
  let sigma := OutsideTreeColorSwap N.T N.phi N.a gamma
  have hswap := OutsideTreeColorSwapStable N.T ∅ N.phi N.a gamma
    N.triple.2.2.2.1 N.triple.2.2.2.2 N.closed N.aMissing hgammaTree hag
  change IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring N.T ∅ N.phi sigma ∧
    ∀ f : E, TreeIncidentEdge N.T f → sigma f = N.phi f at hswap
  obtain ⟨hsProper, hsOne, hstable, hfixed⟩ := hswap
  have hsTriple : KTriple G k e0 sigma :=
    ⟨N.triple.1, N.triple.2.1, N.triple.2.2.1, hsProper, hsOne⟩
  have hsTree : TashkinovTree G e0 sigma N.T := by
    intro j hj
    obtain ⟨i, c, hc, hmissing⟩ := N.tree j hj
    have hedgeTree : TreeIncidentEdge N.T (N.T.edge j) := by
      obtain ⟨r, hr⟩ := N.T.attaches j
      refine ⟨N.T.vertex j.succ, ?_, ?_⟩
      · simp [TreeSequenceVertexSet]
      · rw [Incident, hr]
        simp
    refine ⟨i, c, ?_, ?_⟩
    · rw [hfixed _ hedgeTree]
      exact hc
    · have hv : N.T.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) ∈
          TreeSequenceVertexSet N.T := by
        simp [TreeSequenceVertexSet]
      rw [hstable.2 _ hv]
      exact hmissing
  have hsClosed : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet N.T) := by
    intro f c v hf hv hfc hc
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have hftree : TreeIncidentEdge N.T f := by
      refine ⟨x, hx, ?_⟩
      rw [Incident, hends]
      simp
    have hphif : N.phi f = some c := by
      rw [← hfixed f hftree]
      exact hfc
    have hcmissing : c ∈ MissingColors G N.phi v := by
      rw [← hstable.2 v hv]
      exact hc
    exact (N.closed hf hv hphif) hcmissing
  have transfer_exit {u v : V}
      (P : (TwoColorIncidenceGraph G N.phi N.a N.b).Walk (Sum.inl u) (Sum.inl v))
      (exit : TreeExitPath N.T N.phi N.a N.b u v P) :=
    TreeExitPath.outsideSwap N.T N.T N.phi N.a gamma N.b
      (fun _ member => member) N.colorsDistinct hgammaB
      (ColoredVertexSetClosed.treeColorSetClosed N.closed N.aMissing)
      (ColoredVertexSetClosed.treeColorSetClosed N.closed hgammaTree) P exit exit.2.2.2.1
  obtain ⟨Q1, hQ1, hQ1support, hQ1length⟩ := transfer_exit N.P1 N.exit1
  obtain ⟨Q2, hQ2, hQ2support, hQ2length⟩ := transfer_exit N.P2 N.exit2
  obtain ⟨Q3, hQ3, hQ3support, hQ3length⟩ := transfer_exit N.P3 N.exit3
  have boundary_preserved : ∀ {f : E},
      f ∈ BoundaryColorEdges G N.phi (TreeSequenceVertexSet N.T) N.b →
      f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet N.T) N.b := by
    intro f hf
    obtain ⟨hfboundary, hfcolor⟩ := Finset.mem_filter.mp hf
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hfboundary
    have hftree : TreeIncidentEdge N.T f := by
      refine ⟨x, hx, ?_⟩
      rw [Incident, hends]
      simp
    apply Finset.mem_filter.mpr
    exact ⟨hfboundary, (hfixed f hftree).trans hfcolor⟩
  let D : TchangeCounterexample G k e0 := {
    phi := sigma
    T := N.T
    a := gamma
    b := N.b
    colorsDistinct := hgammaB
    triple := hsTriple
    tree := hsTree
    closed := hsClosed
    aMissing := by
      unfold TreeMissingColors
      simp only [Finset.mem_biUnion]
      exact ⟨N.b3, N.exit3.2.2.2.1, by
        rw [hstable.2 N.b3 N.exit3.2.2.2.1]
        exact hgamma⟩
    bNotMissing := by
      intro hb
      have hbNot := N.bNotMissing
      unfold TreeMissingColors at hb hbNot
      simp only [Finset.mem_biUnion] at hb hbNot
      obtain ⟨v, hv, hbmiss⟩ := hb
      apply hbNot
      exact ⟨v, hv, by simpa [hstable.2 v hv] using hbmiss⟩
    a1 := N.a1
    b1 := N.b1
    a2 := N.a2
    b2 := N.b2
    a3 := N.a3
    b3 := N.b3
    P1 := Q1
    P2 := Q2
    P3 := Q3
    exit1 := hQ1
    exit2 := hQ2
    exit3 := hQ3
    disjoint12 := by
      intro x hx1 hx2
      apply N.disjoint12 x
      · simpa [hQ1support] using hx1
      · simpa [hQ2support] using hx2
    disjoint13 := by
      intro x hx1 hx3
      apply N.disjoint13 x
      · simpa [hQ1support] using hx1
      · simpa [hQ3support] using hx3
    disjoint23 := by
      intro x hx2 hx3
      apply N.disjoint23 x
      · simpa [hQ2support] using hx2
      · simpa [hQ3support] using hx3
    remote12 := N.remote12
    remote13 := N.remote13
    remote23 := N.remote23
    tree12 := N.tree12
    tree13 := N.tree13
    tree23 := N.tree23
    f1 := N.f1
    f2 := N.f2
    f3 := N.f3
    boundary1 := boundary_preserved N.boundary1
    boundary2 := boundary_preserved N.boundary2
    boundary3 := boundary_preserved N.boundary3
    incident1 := N.incident1
    incident2 := N.incident2
    incident3 := N.incident3
    support1 := by simpa [hQ1support] using N.support1
    support2 := by simpa [hQ2support] using N.support2
    support3 := by simpa [hQ3support] using N.support3 }
  refine ⟨D, hNT, hNb, ?_, ?_, horder1, horder2, ?_⟩
  · rw [← hNT, ← hNphi, ← hNa]
  · change gamma ∈ MissingColors G sigma N.b3
    rw [hstable.2 N.b3 N.exit3.2.2.2.1]
    exact hgamma
  · change Q1.length + Q2.length + Q3.length =
      C.P1.length + C.P2.length + C.P3.length
    rw [hQ1length, hQ2length, hQ3length]
    simpa [TchangeCounterexampleMeasure] using hmeasure

theorem TchangeOutsideSwapPreparation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) :
    ∃ D : TchangeCounterexample G k e0,
      D.T = C.T ∧ D.b = C.b ∧
      D.phi = OutsideTreeColorSwap C.T C.phi C.a D.a ∧
      D.a ∈ MissingColors G D.phi D.b3 ∧
      TreeVertexOrder D.T D.b1 D.b3 ∧
      TreeVertexOrder D.T D.b2 D.b3 ∧
      TchangeCounterexampleMeasure D = TchangeCounterexampleMeasure C := by
  classical
  have hb1 : C.b1 ∈ TreeSequenceVertexSet C.T := C.exit1.2.2.2.1
  have hb2 : C.b2 ∈ TreeSequenceVertexSet C.T := C.exit2.2.2.2.1
  have hb3 : C.b3 ∈ TreeSequenceVertexSet C.T := C.exit3.2.2.2.1
  obtain ⟨i1, hi1⟩ : ∃ i, C.T.vertex i = C.b1 := by
    simpa [TreeSequenceVertexSet] using hb1
  obtain ⟨i2, hi2⟩ : ∃ i, C.T.vertex i = C.b2 := by
    simpa [TreeSequenceVertexSet] using hb2
  obtain ⟨i3, hi3⟩ : ∃ i, C.T.vertex i = C.b3 := by
    simpa [TreeSequenceVertexSet] using hb3
  have hi12 : i1.val ≠ i2.val := by
    intro h
    apply C.tree12
    rw [← hi1, ← hi2, Fin.ext h]
  have hi13 : i1.val ≠ i3.val := by
    intro h
    apply C.tree13
    rw [← hi1, ← hi3, Fin.ext h]
  have hi23 : i2.val ≠ i3.val := by
    intro h
    apply C.tree23
    rw [← hi2, ← hi3, Fin.ext h]
  have hnormalized := @helper_hnormalized_63 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C i1 hi1 i2 hi2 i3 hi3 hi12 hi13 hi23
  obtain ⟨N, hNT, hNphi, hNa, hNb, horder1, horder2, hmeasure⟩ := hnormalized
  obtain ⟨gamma, hgamma⟩ := MissingColorsNonemptyOfMaximumDegree G N.phi
    N.triple.2.2.1 N.b3
  have hgammaTree : gamma ∈ TreeMissingColors N.phi N.T := by
    unfold TreeMissingColors
    simp only [Finset.mem_biUnion]
    exact ⟨N.b3, N.exit3.2.2.2.1, hgamma⟩
  have hgammaB : gamma ≠ N.b := by
    intro h
    exact N.bNotMissing (h ▸ hgammaTree)
  by_cases hag : N.a = gamma
  · have hswap : OutsideTreeColorSwap N.T N.phi N.a gamma = N.phi := by
      funext f
      by_cases ht : TreeIncidentEdge N.T f
      · simp [OutsideTreeColorSwap, ht]
      · simp only [OutsideTreeColorSwap, ht, ite_false, hag]
        split <;> simp_all
    refine ⟨N, hNT, hNb, ?_, ?_, horder1, horder2, hmeasure⟩
    · rw [← hNT, ← hNphi, ← hNa, hag]
      simpa [hag] using hswap.symm
    · simpa [hag] using hgamma
  · exact @helper_branch_199 V E inferInstance inferInstance inferInstance inferInstance G k e0 C
      N hNT hNphi hNa hNb horder1 horder2 hmeasure gamma hgamma hgammaTree hgammaB hag
end GoldbergSeymour

end
