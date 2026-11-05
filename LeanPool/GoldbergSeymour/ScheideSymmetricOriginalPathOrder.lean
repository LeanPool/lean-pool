/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainBoundaryEdges
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementInternalMissing
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.ScheideSymmetricOriginalFreePath
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Scheide Symmetric Original Path Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_forwardAdjacent_201.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    IsProperEdgeColoring G phi →
    p.IsPath →
    (0 : ℕ) < p.length →
    (∀ (x : V ⊕ E), H.Adj (Sum.inl v) x → x = p.getVert (1 : ℕ)) →
    ∀ (i j : ℕ),
    i ≤ p.length →
    j ≤ p.length →
    i < j →
    H.Adj (p.getVert i) (p.getVert j) →
    i + (1 : ℕ) = j := by
  classical
  intro V E _ _ G k e0 phi T d beta v z p H hproper hpath hlength startNeighborUnique i j hi hj
      hijlt hij
  by_contra hnot
  have hgap : i + 1 < j := by omega
  by_cases hi0 : i = 0
  · subst i
    have heq := startNeighborUnique (p.getVert j) (by simpa using hij)
    have hinj := hpath.getVert_injOn (by omega : 1 ≤ p.length) hj heq.symm
    omega
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hprev := p.adj_getVert_succ (i := i - 1) (by omega)
    have hnext := p.adj_getVert_succ (i := i) (by omega)
    have hprev' : H.Adj (p.getVert i) (p.getVert (i - 1)) := by
      have hieq : i - 1 + 1 = i := by omega
      simpa [H, hieq] using hprev.symm
    have hnext' : H.Adj (p.getVert i) (p.getVert (i + 1)) := by
      simpa [H] using hnext
    have hprevNext : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
      intro heq
      have hindex := hpath.getVert_injOn
        (by omega : i - 1 ≤ p.length) (by omega : i + 1 ≤ p.length) heq
      omega
    have hprevJ : p.getVert (i - 1) ≠ p.getVert j := by
      intro heq
      have hindex := hpath.getVert_injOn (by omega : i - 1 ≤ p.length) hj heq
      omega
    have hnextJ : p.getVert (i + 1) ≠ p.getVert j := by
      intro heq
      have hindex := hpath.getVert_injOn (by omega : i + 1 ≤ p.length) hj heq
      omega
    let S : Finset (Sum V E) :=
      {p.getVert (i - 1), p.getVert (i + 1), p.getVert j}
    have hScard : S.card = 3 := by
      simp [S, hprevNext, hprevJ, hnextJ]
    have hSsub : ∀ x ∈ S, x ∈ H.neighborSet (p.getVert i) := by
      intro x hx
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa only [SimpleGraph.mem_neighborSet] using hprev'
      · simpa only [SimpleGraph.mem_neighborSet] using hnext'
      · simpa only [SimpleGraph.mem_neighborSet] using hij
    let inclusion : {x // x ∈ S} → H.neighborSet (p.getVert i) :=
      fun x => ⟨x.1, hSsub x.1 x.2⟩
    have hinclusion : Function.Injective inclusion := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : H.neighborSet (p.getVert i) => z.1) hxy
    let : Fintype (H.neighborSet (p.getVert i)) := Fintype.ofFinite _
    have hcard := Fintype.card_le_of_injective inclusion hinclusion
    rw [Fintype.card_coe, hScard,
      SimpleGraph.card_neighborSet_eq_degree] at hcard
    have hdegree := TwoColorIncidenceDegreeAtMostTwo G phi d.1 beta hproper
      (p.getVert i)
    have hdegree' : H.degree (p.getVert i) ≤ 2 := by
      simpa only [H] using hdegree
    omega

private theorem helper_branch_436.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let X : Finset V := TreeSequenceVertexSet T;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    ∀ (h : E),
    phi h = some beta →
    G.ends h = s(R.u1, R.u2) →
    p.IsPath →
    ∀ (j0 : ℕ),
    p.getVert j0 = Sum.inr R.f1 →
    j0 ≤ p.length →
    ∀ (j1 : ℕ),
    p.getVert j1 = Sum.inl R.u1 →
    ∀ (j2 : ℕ),
    p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ),
    p.getVert j3 = Sum.inl R.u2 →
    ∀ (j4 : ℕ),
    p.getVert j4 = Sum.inr R.f2 →
    j4 ≤ p.length →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) | ∃ w ∈ X, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ X,
    p.getVert (↑qv : ℕ) = Sum.inl w →
    (∀ (r : Fin (p.length + (1 : ℕ))),
        (↑qv : ℕ) < (↑r : ℕ) → ∀ (a : V), p.getVert (↑r : ℕ) = Sum.inl a → a ∉ X) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qv : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qv : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    ∀ (f : E),
    p.getVert (↑qf : ℕ) = Sum.inr f →
    Incident G w f →
    (↑qf : ℕ) < p.length →
    f = D.f0 d ∨ f = R.f1 ∨ f = R.f2 →
    j1 = j0 + (1 : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 :
      Fin (p.length + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 :
      Fin (p.length + (1 : ℕ))) (qv : Fin (p.length + (1 : ℕ))) (qf :
      Fin (p.length + (1 : ℕ))),
    phi h = some beta ∧
      G.ends h = s(R.u1, R.u2) ∧
        (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧
          (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧
            (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧
              (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧
                (p.getVert (↑i0 : ℕ) = Sum.inr R.f1 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u1 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u2 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f2 ∨
                    p.getVert (↑i0 : ℕ) = Sum.inr R.f2 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u2 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u1 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f1) ∧
                  (↑i4 : ℕ) < (↑qv : ℕ) ∧
                    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧
                      p.getVert (↑qv : ℕ) = Sum.inl (D.v0 d) ∧
                        p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧
                          ∀ (r : Fin (p.length + (1 : ℕ))),
                            (↑qv : ℕ) < (↑r : ℕ) →
                              ∀ (w : V),
                                p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p X H h hhcolor hhends hpath j0 hj0 hj0le j1
      hj1 j2 hj2 j3 hj3 j4 hj4 hj4le insideIndices insideNonempty qv w hwX hqvw hafter hqvlt qf
      hqfval f hqff hwf hqflt hfThree horient
  rcases horient with ⟨hj01, hj12, hj23, hj34⟩
  let i0 : Fin (p.length + 1) := ⟨j0, by omega⟩
  let i1 : Fin (p.length + 1) := ⟨j1, by omega⟩
  let i2 : Fin (p.length + 1) := ⟨j2, by omega⟩
  let i3 : Fin (p.length + 1) := ⟨j3, by omega⟩
  let i4 : Fin (p.length + 1) := ⟨j4, by omega⟩
  have hi4lt : i4.val < p.length := by
    by_contra hn
    have heq : i4.val = p.length := by omega
    have := hj4
    rw [← show i4.val = j4 by rfl, heq, p.getVert_length] at this
    simp at this
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) hi4lt
  have hret : p.getVert ir.val = Sum.inl R.v2 := by
    have hprev : p.getVert (i4.val - 1) = Sum.inl R.u2 := by
      have heq : i4.val - 1 = j3 := by simp [i4]; omega
      simpa [heq] using hj3
    cases hcase : p.getVert ir.val with
    | inr e =>
        rw [show p.getVert i4.val = Sum.inr R.f2 by simpa [i4] using hj4,
          hcase] at hretAdj
        simp [TwoColorIncidenceGraph] at hretAdj
    | inl y =>
        have hinc : Incident G y R.f2 := by
          rw [show p.getVert i4.val = Sum.inr R.f2 by simpa [i4] using hj4,
            hcase] at hretAdj
          have hretAdj' : Incident G y R.f2 ∧
              (phi R.f2 = some d.1 ∨ phi R.f2 = some beta) := by
            simpa [H, ir, TwoColorIncidenceGraph] using hretAdj
          exact hretAdj'.1
        have hy : y = R.v2 ∨ y = R.u2 := by
          simpa [Incident, R.f2_ends] using hinc
        rcases hy with rfl | rfl
        · simp
        · exfalso
          have hinj := hpath.getVert_injOn (by omega : i4.val - 1 ≤ p.length)
            (by omega : ir.val ≤ p.length)
            (hprev.trans hcase.symm)
          have hne : i4.val - 1 ≠ ir.val := by simp [ir]
          exact hne hinj
  have hirMem : ir ∈ insideIndices := by
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v2, (Finset.mem_sdiff.mp R.v2_in_remainder).1, hret⟩
  have hirle := Finset.le_max' insideIndices ir hirMem
  have hi4qv : i4.val < qv.val := by
    change ir.val ≤ qv.val at hirle
    simp [ir] at hirle
    omega
  have hfn1 : f ≠ R.f1 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i0.val := by
      rw [hqff, heq]
      simpa [i0] using hj0.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i0.val ≤ p.length) hverts
    simp [qf, i0, i4] at hind hi4qv
    omega
  have hfn2 : f ≠ R.f2 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i4.val := by
      rw [hqff, heq]
      simpa [i4] using hj4.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i4.val ≤ p.length) hverts
    simp [qf] at hind
    omega
  have hf0 : f = D.f0 d := hfThree.resolve_right (by
    rintro (heq | heq)
    · exact hfn1 heq
    · exact hfn2 heq)
  have hwv0 : w = D.v0 d := by
    have hwinc : Incident G w (D.f0 d) := hf0 ▸ hwf
    have hwcase : w = D.v0 d ∨ w = D.u0 d := by
      simpa [Incident, D.f0_ends] using hwinc
    exact hwcase.resolve_right (fun hwu => D.u0_outside d (hwu ▸ hwX))
  refine ⟨h, i0, i1, i2, i3, i4, qv, qf, hhcolor, hhends,
    by simpa [i0, i1] using hj01,
    by simpa [i1, i2] using hj12,
    by simpa [i2, i3] using hj23,
    by simpa [i3, i4] using hj34, ?_, hi4qv, hqfval, ?_, ?_, ?_⟩
  · left
    exact ⟨by simpa [i0] using hj0, by simpa [i1] using hj1,
      by simpa [i2] using hj2, by simpa [i3] using hj3,
      by simpa [i4] using hj4⟩
  · simpa [hwv0] using hqvw
  · simpa [hf0] using hqff
  · simpa [X] using hafter

private theorem helper_branch_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let X : Finset V := TreeSequenceVertexSet T;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    ∀ (h : E),
    phi h = some beta →
    G.ends h = s(R.u1, R.u2) →
    p.IsPath →
    ∀ (j0 : ℕ),
    p.getVert j0 = Sum.inr R.f1 →
    j0 ≤ p.length →
    ∀ (j1 : ℕ),
    p.getVert j1 = Sum.inl R.u1 →
    ∀ (j2 : ℕ),
    p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ),
    p.getVert j3 = Sum.inl R.u2 →
    ∀ (j4 : ℕ),
    p.getVert j4 = Sum.inr R.f2 →
    j4 ≤ p.length →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) | ∃ w ∈ X, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ X,
    p.getVert (↑qv : ℕ) = Sum.inl w →
    (∀ (r : Fin (p.length + (1 : ℕ))),
        (↑qv : ℕ) < (↑r : ℕ) → ∀ (a : V), p.getVert (↑r : ℕ) = Sum.inl a → a ∉ X) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qv : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qv : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    ∀ (f : E),
    p.getVert (↑qf : ℕ) = Sum.inr f →
    Incident G w f →
    (↑qf : ℕ) < p.length →
    f = D.f0 d ∨ f = R.f1 ∨ f = R.f2 →
    j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 : ℕ) ∧ j0 = j1 + (1 : ℕ) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 :
      Fin (p.length + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 :
      Fin (p.length + (1 : ℕ))) (qv : Fin (p.length + (1 : ℕ))) (qf :
      Fin (p.length + (1 : ℕ))),
    phi h = some beta ∧
      G.ends h = s(R.u1, R.u2) ∧
        (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧
          (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧
            (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧
              (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧
                (p.getVert (↑i0 : ℕ) = Sum.inr R.f1 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u1 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u2 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f2 ∨
                    p.getVert (↑i0 : ℕ) = Sum.inr R.f2 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u2 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u1 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f1) ∧
                  (↑i4 : ℕ) < (↑qv : ℕ) ∧
                    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧
                      p.getVert (↑qv : ℕ) = Sum.inl (D.v0 d) ∧
                        p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧
                          ∀ (r : Fin (p.length + (1 : ℕ))),
                            (↑qv : ℕ) < (↑r : ℕ) →
                              ∀ (w : V),
                                p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p X H h hhcolor hhends hpath j0 hj0 hj0le j1
      hj1 j2 hj2 j3 hj3 j4 hj4 hj4le insideIndices insideNonempty qv w hwX hqvw hafter hqvlt qf
      hqfval f hqff hwf hqflt hfThree horient
  rcases horient with ⟨hj43, hj32, hj21, hj10⟩
  let i0 : Fin (p.length + 1) := ⟨j4, by omega⟩
  let i1 : Fin (p.length + 1) := ⟨j3, by omega⟩
  let i2 : Fin (p.length + 1) := ⟨j2, by omega⟩
  let i3 : Fin (p.length + 1) := ⟨j1, by omega⟩
  let i4 : Fin (p.length + 1) := ⟨j0, by omega⟩
  have hi4lt : i4.val < p.length := by
    by_contra hn
    have heq : i4.val = p.length := by omega
    have := hj0
    rw [← show i4.val = j0 by rfl, heq, p.getVert_length] at this
    simp at this
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) hi4lt
  have hret : p.getVert ir.val = Sum.inl R.v1 := by
    have hprev : p.getVert (i4.val - 1) = Sum.inl R.u1 := by
      have heq : i4.val - 1 = j1 := by simp [i4]; omega
      simpa [heq] using hj1
    cases hcase : p.getVert ir.val with
    | inr e =>
        rw [show p.getVert i4.val = Sum.inr R.f1 by simpa [i4] using hj0,
          hcase] at hretAdj
        simp [TwoColorIncidenceGraph] at hretAdj
    | inl y =>
        have hinc : Incident G y R.f1 := by
          rw [show p.getVert i4.val = Sum.inr R.f1 by simpa [i4] using hj0,
            hcase] at hretAdj
          have hretAdj' : Incident G y R.f1 ∧
              (phi R.f1 = some d.1 ∨ phi R.f1 = some beta) := by
            simpa [H, ir, TwoColorIncidenceGraph] using hretAdj
          exact hretAdj'.1
        have hy : y = R.v1 ∨ y = R.u1 := by
          simpa [Incident, R.f1_ends] using hinc
        rcases hy with rfl | rfl
        · simp
        · exfalso
          have hinj := hpath.getVert_injOn (by omega : i4.val - 1 ≤ p.length)
            (by omega : ir.val ≤ p.length)
            (hprev.trans hcase.symm)
          have hne : i4.val - 1 ≠ ir.val := by simp [ir]
          exact hne hinj
  have hirMem : ir ∈ insideIndices := by
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v1, (Finset.mem_sdiff.mp R.v1_in_remainder).1, hret⟩
  have hirle := Finset.le_max' insideIndices ir hirMem
  have hi4qv : i4.val < qv.val := by
    change ir.val ≤ qv.val at hirle
    simp [ir] at hirle
    omega
  have hfn1 : f ≠ R.f1 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i4.val := by
      rw [hqff, heq]
      simpa [i4] using hj0.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i4.val ≤ p.length) hverts
    simp [qf] at hind
    omega
  have hfn2 : f ≠ R.f2 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i0.val := by
      rw [hqff, heq]
      simpa [i0] using hj4.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i0.val ≤ p.length) hverts
    simp [qf, i0, i4] at hind hi4qv
    omega
  have hf0 : f = D.f0 d := hfThree.resolve_right (by
    rintro (heq | heq)
    · exact hfn1 heq
    · exact hfn2 heq)
  have hwv0 : w = D.v0 d := by
    have hwinc : Incident G w (D.f0 d) := hf0 ▸ hwf
    have hwcase : w = D.v0 d ∨ w = D.u0 d := by
      simpa [Incident, D.f0_ends] using hwinc
    exact hwcase.resolve_right (fun hwu => D.u0_outside d (hwu ▸ hwX))
  refine ⟨h, i0, i1, i2, i3, i4, qv, qf, hhcolor, hhends,
    by simpa [i0, i1] using hj43,
    by simpa [i1, i2] using hj32,
    by simpa [i2, i3] using hj21,
    by simpa [i3, i4] using hj10, ?_, hi4qv, hqfval, ?_, ?_, ?_⟩
  · right
    exact ⟨by simpa [i0] using hj4, by simpa [i1] using hj3,
      by simpa [i2] using hj2, by simpa [i3] using hj1,
      by simpa [i4] using hj0⟩
  · simpa [hwv0] using hqvw
  · simpa [hf0] using hqff
  · simpa [X] using hafter

private theorem helper_startNeighborUnique_582.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    IsProperEdgeColoring G phi →
    (0 : ℕ) < p.length →
    (∀ (e : E), Incident G v e → phi e ≠ some beta) →
    ∀ (x : V ⊕ E),
    H.Adj (Sum.inl v) x →
    x = p.getVert (1 : ℕ) := by
  classical
  intro V E _ _ G k e0 phi T d beta v z p H hproper hlength hbetaAbsent x hx
  have hfirst := p.adj_getVert_succ (i := 0) hlength
  rw [p.getVert_zero] at hfirst
  cases hxcase : x with
  | inl w =>
      rw [hxcase] at hx
      simp [H, TwoColorIncidenceGraph] at hx
  | inr e =>
      rw [hxcase] at hx
      rcases (by simpa [H, TwoColorIncidenceGraph] using hx) with ⟨hve, hec⟩
      have hedelta : phi e = some d.1 :=
        hec.resolve_right (hbetaAbsent e hve)
      cases hnext : p.getVert 1 with
      | inl w =>
          rw [hnext] at hfirst
          simp [TwoColorIncidenceGraph] at hfirst
      | inr f =>
          rw [hnext] at hfirst
          rcases (by simpa [H, TwoColorIncidenceGraph] using hfirst) with
            ⟨hvf, hfc⟩
          have hfdelta : phi f = some d.1 :=
            hfc.resolve_right (hbetaAbsent f hvf)
          have hef : e = f := by
            by_contra hne
            exact (hproper hne ⟨v, hve, hvf⟩ hedelta) hfdelta
          simp [hef]

private theorem helper_continuation_644.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    beta ∈ MissingColors G phi v →
    ScheideDefectiveChainPath T phi (↑d : Fin k) beta v z p →
    let X : Finset V := TreeSequenceVertexSet T;
    let _ : Finset V :=
      X \
        {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
          C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    v ∈ X →
    ColoredVertexSetClosed G phi X →
    ∀ (h : E),
    phi h = some beta →
    G.ends h = s(R.u1, R.u2) →
    p.IsPath →
    ∀ (j0 : ℕ),
    p.getVert j0 = Sum.inr R.f1 →
    j0 ≤ p.length →
    ∀ (j1 : ℕ),
    p.getVert j1 = Sum.inl R.u1 →
    ∀ (j2 : ℕ),
    p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ),
    p.getVert j3 = Sum.inl R.u2 →
    ∀ (j4 : ℕ),
    p.getVert j4 = Sum.inr R.f2 →
    j4 ≤ p.length →
    j1 = j0 + (1 : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) ∨
        j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 : ℕ) ∧ j0 = j1 + (1 : ℕ) →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) | ∃ w ∈ X, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ X,
    p.getVert (↑qv : ℕ) = Sum.inl w →
    (∀ (r : Fin (p.length + (1 : ℕ))),
        (↑qv : ℕ) < (↑r : ℕ) → ∀ (a : V), p.getVert (↑r : ℕ) = Sum.inl a → a ∉ X) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qv : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qv : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    H.Adj (Sum.inl w) (p.getVert (↑qf : ℕ)) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 :
      Fin (p.length + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 :
      Fin (p.length + (1 : ℕ))) (qv : Fin (p.length + (1 : ℕ))) (qf :
      Fin (p.length + (1 : ℕ))),
    phi h = some beta ∧
      G.ends h = s(R.u1, R.u2) ∧
        (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧
          (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧
            (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧
              (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧
                (p.getVert (↑i0 : ℕ) = Sum.inr R.f1 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u1 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u2 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f2 ∨
                    p.getVert (↑i0 : ℕ) = Sum.inr R.f2 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u2 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u1 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f1) ∧
                  (↑i4 : ℕ) < (↑qv : ℕ) ∧
                    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧
                      p.getVert (↑qv : ℕ) = Sum.inl (D.v0 d) ∧
                        p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧
                          ∀ (r : Fin (p.length + (1 : ℕ))),
                            (↑qv : ℕ) < (↑r : ℕ) →
                              ∀ (w : V),
                                p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbeta hp X Z H hvX hclosed h hhcolor hhends
      hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le horientation insideIndices
      insideNonempty qv w hwX hqvw hafter hqvlt qf hqfval hqadj'
  obtain ⟨f, hqff, hwf, hfcolor⟩ : ∃ f : E,
      p.getVert qf.val = Sum.inr f ∧ Incident G w f ∧
        (phi f = some d.1 ∨ phi f = some beta) := by
    cases hnext : p.getVert qf.val with
    | inl a =>
        exfalso
        rw [hnext] at hqadj'
        simp [H, TwoColorIncidenceGraph] at hqadj'
    | inr f =>
        refine ⟨f, rfl, ?_⟩
        rw [hnext] at hqadj'
        simpa [H, TwoColorIncidenceGraph] using hqadj'
  have hqflt : qf.val < p.length := by
    by_contra hn
    have heq : qf.val = p.length := by omega
    have := hqff
    rw [heq, p.getVert_length] at this
    simp at this
  let qx : Fin (p.length + 1) := ⟨qf.val + 1, by omega⟩
  have hfxadj := p.adj_getVert_succ (i := qf.val) hqflt
  rw [hqff] at hfxadj
  have hfxadj' : H.Adj (Sum.inr f) (p.getVert qx.val) := by
    simpa [H, qx] using hfxadj
  obtain ⟨x, hqxx, hxf⟩ : ∃ x : V,
      p.getVert qx.val = Sum.inl x ∧ Incident G x f := by
    cases hnext : p.getVert qx.val with
    | inl a =>
        refine ⟨a, rfl, ?_⟩
        rw [hnext] at hfxadj'
        have hfxadj'' : Incident G a f ∧
            (phi f = some d.1 ∨ phi f = some beta) := by
          simpa [H, TwoColorIncidenceGraph] using hfxadj'
        exact hfxadj''.1
    | inr e =>
        exfalso
        rw [hnext] at hfxadj'
        simp [H, TwoColorIncidenceGraph] at hfxadj'
  have hxX : x ∉ X := hafter qx (by dsimp [qx, qf]; omega) x hqxx
  have hwne : w ≠ x := by
    intro heq
    exact hxX (heq ▸ hwX)
  have hfends : G.ends f = s(w, x) :=
    (Sym2.mem_and_mem_iff hwne).mp ⟨hwf, hxf⟩
  have hfBoundary : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwX, x, hxX, hfends⟩
  have hfdelta : phi f = some d.1 := by
    rcases hfcolor with hfd | hfb
    · exact hfd
    · exact False.elim ((hclosed (f := f) (c := beta) (v := v)
        hfBoundary hvX hfb) hbeta)
  have hwExit : ScheideExitVertex T phi w := by
    exact ⟨v, beta, d.1, hvX, hbeta, d.2, z, p, hp, qv, hqvw, hwX,
      by simpa [X] using hafter⟩
  have hwExits : w ∈ ScheideExitVertices T phi := by
    simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hwExit
  have hwBase := ScheideStructuralExitsInBase G k e0 phi T C hwExits
  obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hwBase
  have baseBlockNe : ∀ j : Fin 2,
      C.y a ≠ C.blockVertex (D.gammaIndex d) j := by
    intro j heq
    have hindices := T.vertex_injective
      ((C.base_vertex_position a).trans
        (heq.trans (C.block_vertex_position (D.gammaIndex d) j).symm))
    have hvals : a.val = C.p + 2 * (D.gammaIndex d).val + j.val := by
      simpa using congrArg Fin.val hindices
    have hap := a.isLt
    omega
  have hwZ : w ∈ Z := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hwX, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hw0 | hw1)
    · exact baseBlockNe 0 (hay.trans hw0)
    · exact baseBlockNe 1 (hay.trans hw1)
  have hfColorBoundaryZ : f ∈ BoundaryColorEdges G phi Z d.1 := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, hfdelta⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwZ, x, fun hxZ => hxX (Finset.mem_sdiff.mp hxZ).1, hfends⟩
  have hfThree : f = D.f0 d ∨ f = R.f1 ∨ f = R.f2 := by
    apply (R.exact_three f).mp
    refine ⟨by simpa [Z, X] using hfColorBoundaryZ, ?_⟩
    exact ⟨x, by simpa [X] using hxX, hxf⟩
  rcases horientation with horient | horient
  · exact @helper_branch_436 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p h hhcolor hhends hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4
      hj4le insideNonempty w hwX hqvw hafter hqvlt hqfval f hqff hwf hqflt hfThree horient
  · exact @helper_branch_524 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p h hhcolor hhends hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4
      hj4le insideNonempty w hwX hqvw hafter hqvlt hqfval f hqff hwf hqflt hfThree horient

private theorem helper_continuation_622.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    beta ∈ MissingColors G phi v →
    ScheideDefectiveChainPath T phi (↑d : Fin k) beta v z p →
    let X : Finset V := TreeSequenceVertexSet T;
    let _ : Finset V :=
      X \
        {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
          C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    v ∈ X →
    IsProperEdgeColoring G phi →
    ColoredVertexSetClosed G phi X →
    (↑d : Fin k) ≠ beta →
    ∀ (h : E),
    phi h = some beta →
    G.ends h = s(R.u1, R.u2) →
    Sum.inr R.f1 ∈ p.support →
    Sum.inr R.f2 ∈ p.support →
    H.Adj (Sum.inr R.f1) (Sum.inl R.u1) →
    H.Adj (Sum.inl R.u1) (Sum.inr h) →
    H.Adj (Sum.inr h) (Sum.inl R.u2) →
    H.Adj (Sum.inl R.u2) (Sum.inr R.f2) →
    Sum.inl R.u1 ∈ p.support →
    Sum.inr h ∈ p.support →
    Sum.inl R.u2 ∈ p.support →
    p.IsPath →
    (0 : ℕ) < p.length →
    (∀ (e : E), Incident G v e → phi e ≠ some beta) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 :
      Fin (p.length + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 :
      Fin (p.length + (1 : ℕ))) (qv : Fin (p.length + (1 : ℕ))) (qf :
      Fin (p.length + (1 : ℕ))),
    phi h = some beta ∧
      G.ends h = s(R.u1, R.u2) ∧
        (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧
          (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧
            (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧
              (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧
                (p.getVert (↑i0 : ℕ) = Sum.inr R.f1 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u1 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u2 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f2 ∨
                    p.getVert (↑i0 : ℕ) = Sum.inr R.f2 ∧
                      p.getVert (↑i1 : ℕ) = Sum.inl R.u2 ∧
                        p.getVert (↑i2 : ℕ) = Sum.inr h ∧
                          p.getVert (↑i3 : ℕ) = Sum.inl R.u1 ∧
                            p.getVert (↑i4 : ℕ) = Sum.inr R.f1) ∧
                  (↑i4 : ℕ) < (↑qv : ℕ) ∧
                    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧
                      p.getVert (↑qv : ℕ) = Sum.inl (D.v0 d) ∧
                        p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧
                          ∀ (r : Fin (p.length + (1 : ℕ))),
                            (↑qv : ℕ) < (↑r : ℕ) →
                              ∀ (w : V),
                                p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbeta hp X Z H hvX hproper hclosed hdeltaBeta
      h hhcolor hhends hf1Support hf2Support hf1u1 hu1h hhu2 hu2f2 hu1Support hhSupport
      hu2Support hpath hlength hbetaAbsent
  have startNeighborUnique := @helper_startNeighborUnique_582 V E inferInstance inferInstance G k e0
      phi T d beta v z p hproper hlength hbetaAbsent
  have forwardAdjacent := @helper_forwardAdjacent_201 V E inferInstance inferInstance G k e0 phi T d
      beta v z p hproper hpath hlength startNeighborUnique
  have adjacentIndices : ∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
      H.Adj (p.getVert i) (p.getVert j) →
        i + 1 = j ∨ j + 1 = i := by
    intro i j hi hj hij
    have hijne : i ≠ j := by
      intro heq
      subst j
      exact H.irrefl hij
    rcases lt_or_gt_of_ne hijne with hijlt | hjilt
    · exact Or.inl (forwardAdjacent i j hi hj hijlt hij)
    · exact Or.inr (forwardAdjacent j i hj hi hjilt hij.symm)
  obtain ⟨j0, hj0, hj0le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf1Support
  obtain ⟨j1, hj1, hj1le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu1Support
  obtain ⟨j2, hj2, hj2le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hhSupport
  obtain ⟨j3, hj3, hj3le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu2Support
  obtain ⟨j4, hj4, hj4le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf2Support
  have ha01 := adjacentIndices j0 j1 hj0le hj1le (by simpa [H, hj0, hj1] using hf1u1)
  have ha12 := adjacentIndices j1 j2 hj1le hj2le (by simpa [H, hj1, hj2] using hu1h)
  have ha23 := adjacentIndices j2 j3 hj2le hj3le (by simpa [H, hj2, hj3] using hhu2)
  have ha34 := adjacentIndices j3 j4 hj3le hj4le (by simpa [H, hj3, hj4] using hu2f2)
  have hf1h : R.f1 ≠ h := by
    intro heq
    have hc := R.f1_color.symm.trans (heq ▸ hhcolor)
    exact hdeltaBeta (Option.some.inj hc)
  have hhf2 : h ≠ R.f2 := by
    intro heq
    have hc := hhcolor.symm.trans (heq ▸ R.f2_color)
    exact hdeltaBeta (Option.some.inj hc).symm
  have hu1u2 : R.u1 ≠ R.u2 := by
    intro heq
    apply G.loopless h R.u1
    simpa [heq] using hhends
  have hj02 : j0 ≠ j2 := by
    intro heq
    apply hf1h
    apply Sum.inr.inj
    exact hj0.symm.trans (by simpa [heq] using hj2)
  have hj13 : j1 ≠ j3 := by
    intro heq
    apply hu1u2
    apply Sum.inl.inj
    exact hj1.symm.trans (by simpa [heq] using hj3)
  have hj24 : j2 ≠ j4 := by
    intro heq
    apply hhf2
    apply Sum.inr.inj
    exact hj2.symm.trans (by simpa [heq] using hj4)
  have horientation :
      (j1 = j0 + 1 ∧ j2 = j1 + 1 ∧ j3 = j2 + 1 ∧ j4 = j3 + 1) ∨
      (j3 = j4 + 1 ∧ j2 = j3 + 1 ∧ j1 = j2 + 1 ∧ j0 = j1 + 1) := by
    rcases ha01 with h01 | h10 <;>
      rcases ha12 with h12 | h21 <;>
      rcases ha23 with h23 | h32 <;>
      rcases ha34 with h34 | h43 <;> omega
  let insideIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun r =>
      ∃ w ∈ X, p.getVert r.val = Sum.inl w
  have insideNonempty : insideIndices.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hvX, p.getVert_zero⟩
  let qv : Fin (p.length + 1) := insideIndices.max' insideNonempty
  have hqvMem : qv ∈ insideIndices := Finset.max'_mem insideIndices insideNonempty
  obtain ⟨w, hwX, hqvw⟩ := by
    simpa only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using hqvMem
  have hafter : ∀ r : Fin (p.length + 1), qv.val < r.val →
      ∀ a : V, p.getVert r.val = Sum.inl a → a ∉ X := by
    intro r hqr a hra haX
    have hrmem : r ∈ insideIndices := by
      simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, haX, hra⟩
    have hrle := Finset.le_max' insideIndices r hrmem
    exact (not_le_of_gt hqr) hrle
  have hqvlt : qv.val < p.length := by
    by_contra hn
    have heq : qv.val = p.length := by omega
    have hwz : w = z := by
      apply Sum.inl.inj
      rw [← hqvw, heq, p.getVert_length]
    exact hp.2.2.1 (hwz ▸ hwX)
  let qf : Fin (p.length + 1) := ⟨qv.val + 1, by omega⟩
  have hqfval : qf.val = qv.val + 1 := rfl
  have hqadj := p.adj_getVert_succ (i := qv.val) hqvlt
  rw [hqvw] at hqadj
  have hqadj' : H.Adj (Sum.inl w) (p.getVert qf.val) := by
    simpa [H, qf] using hqadj
  exact @helper_continuation_644 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R beta v z p hbeta hp hvX hclosed h hhcolor hhends hpath j0 hj0 hj0le j1 hj1
      j2 hj2 j3 hj3 j4 hj4 hj4le horientation insideNonempty w hwX hqvw hafter hqvlt hqfval hqadj'
theorem ScheideSymmetricOriginalPathOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi d.1 beta).Walk (Sum.inl v) (Sum.inl z)),
    v ∈
        TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} →
    beta ∈ MissingColors G phi v →
    beta ∈ TreeFreeColors phi T →
    beta ≠ C.gamma (D.gammaIndex d) →
    ScheideDefectiveChainPath T phi d.1 beta v z p →
    ∃ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + 1)),
    phi h = some beta ∧
      G.ends h = s(R.u1, R.u2) ∧
        i1.val = i0.val + 1 ∧
          i2.val = i1.val + 1 ∧
            i3.val = i2.val + 1 ∧
              i4.val = i3.val + 1 ∧
                ((p.getVert i0.val = Sum.inr R.f1 ∧
                      p.getVert i1.val = Sum.inl R.u1 ∧
                        p.getVert i2.val = Sum.inr h ∧
                          p.getVert i3.val = Sum.inl R.u2 ∧
                            p.getVert i4.val = Sum.inr R.f2) ∨
                    (p.getVert i0.val = Sum.inr R.f2 ∧
                      p.getVert i1.val = Sum.inl R.u2 ∧
                        p.getVert i2.val = Sum.inr h ∧
                          p.getVert i3.val = Sum.inl R.u1 ∧
                            p.getVert i4.val = Sum.inr R.f1)) ∧
                  i4.val < qv.val ∧
                    qf.val = qv.val + 1 ∧
                      p.getVert qv.val = Sum.inl (D.v0 d) ∧
                        p.getVert qf.val = Sum.inr (D.f0 d) ∧
                          ∀ r : Fin (p.length + 1),
                            qv.val < r.val →
                              ∀ w : V,
                                p.getVert r.val = Sum.inl w → w ∉ TreeSequenceVertexSet T := by
  classical
  intro beta v z p hv hbeta hfree hbetaGamma hp
  let X := TreeSequenceVertexSet T
  let Z := X \
    {C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1}
  let H := TwoColorIncidenceGraph G phi d.1 beta
  have hvZ : v ∈ Z := by simpa [Z, X] using hv
  have hvX : v ∈ X := (Finset.mem_sdiff.mp hvZ).1
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    intro f c u hf hu hc
    exact (ScheideGlobalMaximumOrder G k e0 phi T
      C.globally_maximum).2.2.2.2 (f := f) (c := c) (v := u)
        (by simpa only [X] using hf) (by simpa only [X] using hu) hc
  have hf1Boundary : R.f1 ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v1, (Finset.mem_sdiff.mp R.v1_in_remainder).1,
      R.u1, R.u1_outside, R.f1_ends⟩
  have hf2Boundary : R.f2 ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v2, (Finset.mem_sdiff.mp R.v2_in_remainder).1,
      R.u2, R.u2_outside, R.f2_ends⟩
  have hdeltaBeta : d.1 ≠ beta := by
    intro hdb
    have hn := hclosed (f := R.f1) (c := d.1) (v := v)
      hf1Boundary hvX R.f1_color
    exact hn (hdb ▸ hbeta)
  obtain ⟨h, hhcolor, hhends⟩ :=
    ScheideReplacementInternalMissing G k e0 phi T C D d R beta
      hbetaGamma ⟨v, hv, hbeta⟩
  have hf1ColorBoundary :
      R.f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1 := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨by simpa [X] using hf1Boundary, R.f1_color⟩
  have hf2ColorBoundary :
      R.f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1 := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨by simpa [X] using hf2Boundary, R.f2_color⟩
  have hchain := ScheideDefectiveChainBoundaryEdges G k e0 phi T
    C.globally_maximum d.1 beta d.2 hfree v hvX hbeta z p hp
  have hf1Support : Sum.inr R.f1 ∈ p.support :=
    (hchain R.f1).mp hf1ColorBoundary |>.2
  have hf2Support : Sum.inr R.f2 ∈ p.support :=
    (hchain R.f2).mp hf2ColorBoundary |>.2
  have hf1u1 : H.Adj (Sum.inr R.f1) (Sum.inl R.u1) := by
    simp [H, TwoColorIncidenceGraph, Incident, R.f1_ends, R.f1_color]
  have hu1h : H.Adj (Sum.inl R.u1) (Sum.inr h) := by
    simp [H, TwoColorIncidenceGraph, Incident, hhends, hhcolor]
  have hhu2 : H.Adj (Sum.inr h) (Sum.inl R.u2) := by
    simp [H, TwoColorIncidenceGraph, Incident, hhends, hhcolor]
  have hu2f2 : H.Adj (Sum.inl R.u2) (Sum.inr R.f2) := by
    simp [H, TwoColorIncidenceGraph, Incident, R.f2_ends, R.f2_color]
  have hf1Component :
      H.connectedComponentMk (Sum.inr R.f1) =
        H.connectedComponentMk (Sum.inl v) := by
    change Sum.inr R.f1 ∈ TwoColorComponent G phi d.1 beta (Sum.inl v)
    rw [← hp.2.2.2]
    exact hf1Support
  have hu1Component :
      H.connectedComponentMk (Sum.inl R.u1) =
        H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hf1u1).symm.trans
      hf1Component
  have hhComponent :
      H.connectedComponentMk (Sum.inr h) =
        H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hu1h).symm.trans
      hu1Component
  have hu2Component :
      H.connectedComponentMk (Sum.inl R.u2) =
        H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hhu2).symm.trans
      hhComponent
  have componentSupport : ∀ x : Sum V E,
      H.connectedComponentMk x = H.connectedComponentMk (Sum.inl v) →
        x ∈ p.support := by
    intro x hx
    have hx' : x ∈ TwoColorComponent G phi d.1 beta (Sum.inl v) := hx
    rw [← hp.2.2.2] at hx'
    exact hx'
  have hu1Support : Sum.inl R.u1 ∈ p.support :=
    componentSupport _ hu1Component
  have hhSupport : Sum.inr h ∈ p.support :=
    componentSupport _ hhComponent
  have hu2Support : Sum.inl R.u2 ∈ p.support :=
    componentSupport _ hu2Component
  have hpath : p.IsPath := hp.2.1
  have hlength : 0 < p.length := by
    by_contra hn
    have hzero : p.length = 0 := by omega
    have hvz : (Sum.inl v : Sum V E) = Sum.inl z :=
      SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact hp.2.2.1 (Sum.inl.inj hvz ▸ hvX)
  have hbetaAbsent : ∀ e : E, Incident G v e → phi e ≠ some beta := by
    intro e hve heb
    have hnot : beta ∉ PresentColors G phi v := (Finset.mem_sdiff.mp hbeta).2
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hve, heb⟩
  exact @helper_continuation_622 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R beta v z p hbeta hp hvX hproper hclosed hdeltaBeta h hhcolor hhends
      hf1Support hf2Support hf1u1 hu1h hhu2 hu2f2 hu1Support hhSupport hu2Support hpath hlength
      hbetaAbsent
end GoldbergSeymour

end
