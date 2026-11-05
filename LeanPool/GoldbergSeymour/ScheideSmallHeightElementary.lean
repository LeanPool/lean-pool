/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.Critical
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.GlobalMaximumTripleExists
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideBalancedExists
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideGraphHeightOdd
public import LeanPool.GoldbergSeymour.ScheideKempePathHeightBound
public import LeanPool.GoldbergSeymour.ScheideLargeHeightElementary
public import LeanPool.GoldbergSeymour.ScheideMaximalKempePath
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationPreserves
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TrunkRotation
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Small Height Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_300.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (_ e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T),
    BalancedGlobalMaximumTriple N →
    N.height = (3 : ℕ) →
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let v3 : Fin (T.length + (1 : ℕ)) := (⟨(3 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v4 : Fin (T.length + (1 : ℕ)) := (⟨(4 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k),
    phi (T.edge r2) = some gamma →
    gamma ∈
        MissingColors G phi (T.vertex (⟨(↑w : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))) →
    phi (T.edge r3) = some gamma →
    ∀ (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) :=
      a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt));
    (↑a2' : ℕ) < (3 : ℕ) →
    Incident G (T.vertex v3) (T.edge r2) →
    Incident G (T.vertex a2') (T.edge r2) →
    (↑a2' : ℕ) ≠ (↑w : ℕ) →
    (gamma = N.alpha → (↑w : ℕ) = (0 : ℕ)) →
    (gamma = N.beta → (↑w : ℕ) = (1 : ℕ)) →
    gamma ≠ N.alpha →
    gamma ≠ N.beta →
    ∀ (a3 : Fin ((↑r3 : ℕ) + (1 : ℕ))),
    let a3' : Fin (T.length + (1 : ℕ)) :=
      a3.castLT (Nat.lt_trans a3.isLt (Nat.succ_lt_succ r3.isLt));
    (↑a3' : ℕ) < (4 : ℕ) →
    Incident G (T.vertex v4) (T.edge r3) →
    Incident G (T.vertex a3') (T.edge r3) →
    (↑a3' : ℕ) ≠ (3 : ℕ) →
    (↑a3' : ℕ) < (3 : ℕ) →
    (↑a3' : ℕ) ≠ (↑w : ℕ) →
    (↑a2' : ℕ) ≠ (↑a3' : ℕ) →
    (↑w : ℕ) = (0 : ℕ) →
    ∃ (e : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
      NormalGlobalMaximumTriple G k e psi S) (hSlen : (6 : ℕ) ≤ S.length),
    BalancedGlobalMaximumTriple M ∧
      M.height = (3 : ℕ) ∧
        gamma ∈
            MissingColors G psi
              (S.vertex (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) ∧
          psi (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) = some gamma ∧
            psi (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) = some gamma ∧
              Incident G (S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                  (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                Incident G (S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                    (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) ∧
                  (Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                      Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) ∨
                    Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                      Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length))) := by
  classical
  intro V E _ _ _ G k e0 e0 phi T N hbalanced hNheight hlength v3 v4 r2 r3 w gamma he2gamma
      hwgamma' he3gamma a2 a2' ha2val he2inc_new he2inc_attach ha2_ne_w hw_eq_zero_of_alpha
      hw_eq_one_of_beta hgamma_alpha hgamma_beta a3 a3' ha3val he3inc_new he3inc_attach
      ha3_ne_three ha3trunk ha3_ne_w ha23_ne hw0
  have hpairs : (a2'.val = 1 ∧ a3'.val = 2) ∨
      (a2'.val = 2 ∧ a3'.val = 1) := by omega
  refine ⟨e0, phi, T, N, hlength, hbalanced, hNheight, ?_,
    he2gamma, he3gamma, he2inc_new, he3inc_new, ?_⟩
  · have hv : T.vertex ⟨0, by omega⟩ = T.vertex ⟨w.val, by omega⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      simpa using hw0.symm
    rw [hv]
    exact hwgamma'
  · rcases hpairs with h | h
    · left
      constructor
      · have hv : T.vertex ⟨1, by omega⟩ = T.vertex a2' := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa using h.1.symm
        simpa [hv] using he2inc_attach
      · have hv : T.vertex ⟨2, by omega⟩ = T.vertex a3' := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa using h.2.symm
        simpa [hv] using he3inc_attach
    · right
      constructor
      · have hv : T.vertex ⟨2, by omega⟩ = T.vertex a2' := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa using h.1.symm
        simpa [hv] using he2inc_attach
      · have hv : T.vertex ⟨1, by omega⟩ = T.vertex a3' := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa using h.2.symm
        simpa [hv] using he3inc_attach

private theorem helper_hback_432.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
        (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (hw_bound : (↑w : ℕ) < (3 : ℕ)), (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) → phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then
        some N.alpha else some N.beta) →
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))), gamma ≠ N.alpha → gamma ≠ N.beta →
    ∀ (_ : Fin ((↑r3 : ℕ) + (1 : ℕ))) (hwpos : (1 : ℕ) ≤ (↑w : ℕ)),
    let j : Fin N.height := (⟨(↑w : ℕ),
    by omega
    ⟩ : Fin N.height);
    ∀ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1) (M :
        NormalGlobalMaximumTriple G k e1 psi S), (1 : ℕ) ≤ (↑j : ℕ) → e1 = NormalCycleEdge N j →
        psi e1 = none → (
    ∀ (i : Fin (↑j : ℕ)), psi (NormalCycleEdge N (Fin.castLE ((Nat.le_of_lt (j).isLt)) i)) = phi
        (NormalCycleEdge N (⟨(↑i : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin N.height))) → (
    ∀ (f : E), (
    ∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))), f ≠ NormalCycleEdge N (Fin.castLE ((Nat.succ_le_iff.mpr
        (j).isLt)) i)) → psi f = phi f) → (
    ∃ (pred : Fin N.height), (↑pred : ℕ) = ((↑j : ℕ) + N.height - (1 : ℕ)) % N.height ∧
        M.closingEdge = NormalCycleEdge N pred) →
    ∀ (f : E), psi f = some gamma → phi f = some gamma := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength r2 r3 w gamma hw_bound hcycle_colors a2
      hgamma_alpha hgamma_beta a3 hwpos j e1 psi S M _ _ _ hshift hfixed hclosing f hf
  by_cases hfj : f = NormalCycleEdge N j
  · subst f
    simp_all
  by_cases hs : ∃ i : Fin j.val,
      f = NormalCycleEdge N (Fin.castLE (Nat.le_of_lt j.isLt) i)
  · obtain ⟨i, hi⟩ := hs
    have hqpos : 1 ≤ i.val + 1 := by omega
    let q : Fin N.height := ⟨i.val + 1, by
      have hi' := i.isLt
      have hj' := j.isLt
      omega⟩
    have hc := hcycle_colors q hqpos
    have hpsi : psi f = phi (NormalCycleEdge N q) := by
      rw [hi]
      simpa [q] using hshift i
    rw [hpsi] at hf
    by_cases hodd : Odd q.val
    · rw [ite_eq_left hodd] at hc
      exact False.elim (hgamma_alpha
        (Option.some.inj (hc.symm.trans hf)).symm)
    · rw [ite_eq_right hodd] at hc
      exact False.elim (hgamma_beta
        (Option.some.inj (hc.symm.trans hf)).symm)
  · have hfix : psi f = phi f := hfixed f (by
      intro i
      by_cases hilast : i.val = j.val
      · intro heq
        apply hfj
        rw [heq]
        apply congrArg (NormalCycleEdge N)
        apply Fin.ext
        simpa [j] using hilast
      · intro heq
        apply hs
        let t : Fin j.val := ⟨i.val, by omega⟩
        refine ⟨t, ?_⟩
        rw [heq]
        apply congrArg (NormalCycleEdge N)
        apply Fin.ext
        rfl)
    exact hfix ▸ hf

private theorem helper_htailFixed_522.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (_ e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3
        : ℕ)) (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (hw_bound : (↑w : ℕ) < (3 : ℕ)), (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) → phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then
        some N.alpha else some N.beta) →
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))), gamma ≠ N.alpha → gamma ≠ N.beta →
    ∀ (_ : Fin ((↑r3 : ℕ) + (1 : ℕ))) (hwpos : (1 : ℕ) ≤ (↑w : ℕ)),
    let j : Fin N.height := (⟨(↑w : ℕ),
    by omega
    ⟩ : Fin N.height);
    ∀ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1) (M :
        NormalGlobalMaximumTriple G k e1 psi S), (
    ∀ (f : E), (
    ∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))), f ≠ NormalCycleEdge N (Fin.castLE ((Nat.succ_le_iff.mpr
        (j).isLt)) i)) → psi f = phi f) → S.length = T.length → (
    ∃ (pred : Fin N.height), (↑pred : ℕ) = ((↑j : ℕ) + N.height - (1 : ℕ)) % N.height ∧
        M.closingEdge = NormalCycleEdge N pred) →
    ∀ (_ _ _ : Fin N.height) (_ _ : Fin (T.length + (1 : ℕ))) (_ _ : Fin T.length) (f : E), phi f
        = some gamma → psi f = phi f := by
  classical
  intro V E _ _ _ G k e0 e0 phi T N hNheight hlength r2 r3 w gamma hw_bound hcycle_colors a2
      hgamma_alpha hgamma_beta a3 hwpos j e1 psi S M hfixed hSlength hclosing iw0 iw1 iw2 ov3 ov4
      oe2 oe3 f hf
  apply hfixed
  intro i heq
  have hi0 : i.val = 0 ∨ 1 ≤ i.val := by omega
  rcases hi0 with hi0 | hipos
  · have hzero : NormalCycleEdge N
        (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i) = e0 := by
      simp [NormalCycleEdge, hi0]
    have hnone : phi (NormalCycleEdge N
        (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) = none := by
      rw [hzero]
      exact N.global.1.2.2.2.2.1
    rw [heq] at hf
    rw [hnone] at hf
    simp at hf
  · let q : Fin N.height :=
      Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i
    have hc := hcycle_colors q (by simpa [q] using hipos)
    rw [heq] at hf
    change phi (NormalCycleEdge N q) = some gamma at hf
    by_cases hodd : Odd q.val
    · rw [ite_eq_left hodd] at hc
      exact hgamma_alpha (Option.some.inj (hc.symm.trans hf)).symm
    · rw [ite_eq_right hodd] at hc
      exact hgamma_beta (Option.some.inj (hc.symm.trans hf)).symm

private theorem helper_hattach_581.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
      (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (hw_bound : (↑w : ℕ) < (3 : ℕ))
      (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) :=
      a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt));
    Incident G (T.vertex a2') (T.edge r2) →
    ∀ (a3 : Fin ((↑r3 : ℕ) + (1 : ℕ))),
    let a3' : Fin (T.length + (1 : ℕ)) :=
      a3.castLT (Nat.lt_trans a3.isLt (Nat.succ_lt_succ r3.isLt));
    Incident G (T.vertex a3') (T.edge r3) →
    ∀ (hwpos : (1 : ℕ) ≤ (↑w : ℕ)),
    let j : Fin N.height := (⟨(↑w : ℕ), by omega⟩ : Fin N.height);
    ∀ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1)
      (M : NormalGlobalMaximumTriple G k e1 psi S),
    (1 : ℕ) ≤ (↑j : ℕ) →
    e1 = NormalCycleEdge N j →
    psi e1 = none →
    ∀ (hSlength : S.length = T.length)
      (hclosing :
        ∃ (pred : Fin N.height),
          (↑pred : ℕ) = ((↑j : ℕ) + N.height - (1 : ℕ)) % N.height ∧
            M.closingEdge = NormalCycleEdge N pred),
    let s1 : Fin (S.length + (1 : ℕ)) := (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s2 : Fin (S.length + (1 : ℕ)) := (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let t2 : Fin S.length := (⟨(2 : ℕ), by omega⟩ : Fin S.length);
    let t3 : Fin S.length := (⟨(3 : ℕ), by omega⟩ : Fin S.length);
    ∀ (iw1 : Fin N.height),
    S.vertex s1 = T.vertex (Fin.castLE N.height_upper iw1) →
    ∀ (iw2 : Fin N.height),
    S.vertex s2 = T.vertex (Fin.castLE N.height_upper iw2) →
    S.edge t2 = T.edge r2 →
    S.edge t3 = T.edge r3 →
    (↑a2' : ℕ) = (↑iw1 : ℕ) ∧ (↑a3' : ℕ) = (↑iw2 : ℕ) ∨
        (↑a2' : ℕ) = (↑iw2 : ℕ) ∧ (↑a3' : ℕ) = (↑iw1 : ℕ) →
    Incident G (S.vertex s1) (S.edge t2) ∧ Incident G (S.vertex s2) (S.edge t3) ∨
      Incident G (S.vertex s2) (S.edge t2) ∧ Incident G (S.vertex s1) (S.edge t3) := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength r2 r3 w hw_bound a2 a2' he2inc_attach a3 a3'
      he3inc_attach hwpos j e1 psi S M _ _ _ hSlength hclosing s1 s2 t2 t3 iw1 hs1 iw2 hs2 ht2old
      ht3old hpairs
  rcases hpairs with h | h
  · left
    constructor
    · rw [ht2old, hs1]
      have hv : T.vertex (Fin.castLE N.height_upper iw1) = T.vertex a2' := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using h.1.symm
      rw [hv]
      exact he2inc_attach
    · rw [ht3old, hs2]
      have hv : T.vertex (Fin.castLE N.height_upper iw2) = T.vertex a3' := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using h.2.symm
      rw [hv]
      exact he3inc_attach
  · right
    constructor
    · rw [ht2old, hs2]
      have hv : T.vertex (Fin.castLE N.height_upper iw2) = T.vertex a2' := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using h.1.symm
      rw [hv]
      exact he2inc_attach
    · rw [ht3old, hs1]
      have hv : T.vertex (Fin.castLE N.height_upper iw1) = T.vertex a3' := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using h.2.symm
      rw [hv]
      exact he3inc_attach

private theorem helper_hgammaOldPsi_662.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
      (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (hw_bound : (↑w : ℕ) < (3 : ℕ)),
    gamma ∈
        MissingColors G phi (T.vertex (⟨(↑w : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))) →
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))) (_ : Fin ((↑r3 : ℕ) + (1 : ℕ)))
      (hwpos : (1 : ℕ) ≤ (↑w : ℕ)),
    let j : Fin N.height := (⟨(↑w : ℕ), by omega⟩ : Fin N.height);
    ∀ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1)
      (M : NormalGlobalMaximumTriple G k e1 psi S) (hSlength : S.length = T.length)
      (hclosing :
        ∃ (pred : Fin N.height),
          (↑pred : ℕ) = ((↑j : ℕ) + N.height - (1 : ℕ)) % N.height ∧
            M.closingEdge = NormalCycleEdge N pred),
    (∀ (f : E), psi f = some gamma → phi f = some gamma) →
    gamma ∈ MissingColors G psi (T.vertex (⟨(↑w : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength r2 r3 w gamma hw_bound hwgamma' a2 a3 hwpos j
      e1 psi S M hSlength hclosing hback
  have hnot : gamma ∉ PresentColors G psi
      (T.vertex ⟨w.val, by omega⟩) := by
    intro hp
    obtain ⟨f, hinc, hf⟩ := by simpa [PresentColors] using hp
    have hpold : gamma ∈ PresentColors G phi
        (T.vertex ⟨w.val, by omega⟩) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hinc, hback f hf⟩
    have hnold : gamma ∉ PresentColors G phi
        (T.vertex ⟨w.val, by omega⟩) := by
      simpa [MissingColors] using hwgamma'
    exact hnold hpold
  simpa [MissingColors] using hnot

private theorem helper_hpairs_718.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
        (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (hw_bound : (↑w : ℕ) < (3 : ℕ)) (a2 : Fin
        ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) := a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ
        r2.isLt)); (↑a2' : ℕ) < (3 : ℕ) → (↑a2' : ℕ) ≠ (↑w : ℕ) → (gamma = N.alpha → (↑w : ℕ) = (0
        : ℕ)) → (gamma = N.beta → (↑w : ℕ) = (1 : ℕ)) → gamma ≠ N.alpha → gamma ≠ N.beta →
    ∀ (a3 : Fin ((↑r3 : ℕ) + (1 : ℕ))),
    let a3' : Fin (T.length + (1 : ℕ)) := a3.castLT (Nat.lt_trans a3.isLt (Nat.succ_lt_succ
        r3.isLt)); (↑a3' : ℕ) < (4 : ℕ) → (↑a3' : ℕ) ≠ (3 : ℕ) → (↑a3' : ℕ) < (3 : ℕ) → (↑a3' : ℕ)
        ≠ (↑w : ℕ) → (↑a2' : ℕ) ≠ (↑a3' : ℕ) → ¬(↑w : ℕ) = (0 : ℕ) →
    ∀ (hwpos : (1 : ℕ) ≤ (↑w : ℕ)),
    let j : Fin N.height := (⟨(↑w : ℕ),
    by omega
    ⟩ : Fin N.height);
    ∀ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1) (M :
        NormalGlobalMaximumTriple G k e1 psi S) (hSlength : S.length = T.length) (hclosing :
    ∃ (pred : Fin N.height), (↑pred : ℕ) = ((↑j : ℕ) + N.height - (1 : ℕ)) % N.height ∧
        M.closingEdge = NormalCycleEdge N pred),
    let s1 : Fin (S.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let s2 : Fin (S.length + (1 : ℕ)) := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    ∀ (_ iw1 : Fin N.height), (↑iw1 : ℕ) = ((↑j : ℕ) + (↑s1 : ℕ)) % N.height →
    ∀ (iw2 : Fin N.height), (↑iw2 : ℕ) = ((↑j : ℕ) + (↑s2 : ℕ)) % N.height →
    ∀ (_ _ : Fin (T.length + (1 : ℕ))) (_ _ : Fin T.length), (↑w : ℕ) = (1 : ℕ) ∨ (↑w : ℕ) = (2 :
        ℕ) → (↑a2' : ℕ) = (↑iw1 : ℕ) ∧ (↑a3' : ℕ) = (↑iw2 : ℕ) ∨ (↑a2' : ℕ) = (↑iw2 : ℕ) ∧ (↑a3' :
        ℕ) = (↑iw1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength r2 r3 w gamma hw_bound a2 a2' ha2val ha2_ne_w
      hw_eq_zero_of_alpha hw_eq_one_of_beta hgamma_alpha hgamma_beta a3 a3' ha3val ha3_ne_three
      ha3trunk ha3_ne_w ha23_ne hw0 hwpos j e1 psi S M hSlength hclosing s1 s2 iw0 iw1 hiw1 iw2
      hiw2 ov3 ov4 oe2 oe3 hwcases
  rcases hwcases with hw1 | hw2
  · have hi1 : iw1.val = 2 := by
      have hi := hiw1
      simp only [hw1, Nat.reduceAdd, hNheight, Nat.mod_succ, j, s1] at hi
      exact hi
    have hi2 : iw2.val = 0 := by
      have hi := hiw2
      simp only [hw1, Nat.reduceAdd, hNheight, Nat.mod_self, j, s2] at hi
      exact hi
    omega
  · have hi1 : iw1.val = 0 := by
      have hi := hiw1
      simp only [hw2, Nat.reduceAdd, hNheight, Nat.mod_self, j, s1] at hi
      exact hi
    have hi2 : iw2.val = 1 := by
      have hi := hiw2
      simp only [hw2, Nat.reduceAdd, hNheight, Nat.reduceMod, j, s2] at hi
      exact hi
    omega

private theorem helper_branch_335.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (_ e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T),
    BalancedGlobalMaximumTriple N →
    N.height = (3 : ℕ) →
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let v3 : Fin (T.length + (1 : ℕ)) := (⟨(3 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v4 : Fin (T.length + (1 : ℕ)) := (⟨(4 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k),
    phi (T.edge r2) = some gamma →
    (↑w : ℕ) < (3 : ℕ) →
    gamma ∈
        MissingColors G phi (T.vertex (⟨(↑w : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))) →
    phi (T.edge r3) = some gamma →
    (∀ (i : Fin N.height),
        (1 : ℕ) ≤ (↑i : ℕ) →
          phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then some N.alpha else some N.beta) →
    ∀ (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) :=
      a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt));
    (↑a2' : ℕ) < (3 : ℕ) →
    Incident G (T.vertex v3) (T.edge r2) →
    Incident G (T.vertex a2') (T.edge r2) →
    (↑a2' : ℕ) ≠ (↑w : ℕ) →
    (gamma = N.alpha → (↑w : ℕ) = (0 : ℕ)) →
    (gamma = N.beta → (↑w : ℕ) = (1 : ℕ)) →
    gamma ≠ N.alpha →
    gamma ≠ N.beta →
    ∀ (a3 : Fin ((↑r3 : ℕ) + (1 : ℕ))),
    let a3' : Fin (T.length + (1 : ℕ)) :=
      a3.castLT (Nat.lt_trans a3.isLt (Nat.succ_lt_succ r3.isLt));
    (↑a3' : ℕ) < (4 : ℕ) →
    Incident G (T.vertex v4) (T.edge r3) →
    Incident G (T.vertex a3') (T.edge r3) →
    (↑a3' : ℕ) ≠ (3 : ℕ) →
    (↑a3' : ℕ) < (3 : ℕ) →
    (↑a3' : ℕ) ≠ (↑w : ℕ) →
    (↑a2' : ℕ) ≠ (↑a3' : ℕ) →
    ¬(↑w : ℕ) = (0 : ℕ) →
    ∃ (e : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
      NormalGlobalMaximumTriple G k e psi S) (hSlen : (6 : ℕ) ≤ S.length),
    BalancedGlobalMaximumTriple M ∧
      M.height = (3 : ℕ) ∧
        gamma ∈
            MissingColors G psi
              (S.vertex (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) ∧
          psi (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) = some gamma ∧
            psi (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) = some gamma ∧
              Incident G (S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                  (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                Incident G (S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                    (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) ∧
                  (Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                      Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) ∨
                    Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
                      Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
                        (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length))) := by
  classical
  intro V E _ _ _ G k e0 e0 phi T N hbalanced hNheight this hlength v3 v4 r2 r3 w gamma he2gamma
      hw_bound hwgamma' he3gamma hcycle_colors a2 a2' ha2val he2inc_new he2inc_attach ha2_ne_w
      hw_eq_zero_of_alpha hw_eq_one_of_beta hgamma_alpha hgamma_beta a3 a3' ha3val he3inc_new
      he3inc_attach ha3_ne_three ha3trunk ha3_ne_w ha23_ne hw0
  have hwpos : 1 ≤ w.val := by omega
  let j : Fin N.height := ⟨w.val, by omega⟩
  obtain ⟨e1, psi, S, M, hrot, hbalM⟩ :=
    ScheideTrunkRotationPreserves G k e0 phi T N hbalanced j (by
      simpa [j] using hwpos)
  rcases hrot with ⟨_, _, _, hshift, hfixed, hSlength, hMheight0,
    hvertexSet, htrunkVertices, htailVertices, htrunkEdges,
    htailEdges, hclosing⟩
  have hMheight : M.height = 3 := hMheight0.trans hNheight
  have hSlen : 6 ≤ S.length := by omega
  have hback : ∀ f : E, psi f = some gamma → phi f = some gamma := by
    exact @helper_hback_432 V E inferInstance inferInstance inferInstance G k e0 phi T N hNheight
        hlength w gamma hw_bound hcycle_colors a2 hgamma_alpha hgamma_beta a3 hwpos e1 psi S M
        (by assumption) (by assumption) (by assumption) hshift hfixed hclosing
  have hgammaOldPsi := @helper_hgammaOldPsi_662 V E inferInstance inferInstance inferInstance G k e0
      phi T N hNheight hlength w gamma hw_bound hwgamma' a2 a3 hwpos e1 psi S M hSlength hclosing
      hback
  let s0 : Fin (S.length + 1) := ⟨0, by omega⟩
  let s1 : Fin (S.length + 1) := ⟨1, by omega⟩
  let s2 : Fin (S.length + 1) := ⟨2, by omega⟩
  let s3 : Fin (S.length + 1) := ⟨3, by omega⟩
  let s4 : Fin (S.length + 1) := ⟨4, by omega⟩
  let t2 : Fin S.length := ⟨2, by omega⟩
  let t3 : Fin S.length := ⟨3, by omega⟩
  obtain ⟨iw0, hiw0, hs0⟩ := htrunkVertices s0 (by simp [s0, hNheight])
  obtain ⟨iw1, hiw1, hs1⟩ := htrunkVertices s1 (by simp [s1, hNheight])
  obtain ⟨iw2, hiw2, hs2⟩ := htrunkVertices s2 (by simp [s2, hNheight])
  obtain ⟨ov3, hov3, hs3⟩ := htailVertices s3 (by simp [s3, hNheight])
  obtain ⟨ov4, hov4, hs4⟩ := htailVertices s4 (by simp [s4, hNheight])
  obtain ⟨oe2, hoe2, ht2⟩ := htailEdges t2 (by simp [t2, hNheight])
  obtain ⟨oe3, hoe3, ht3⟩ := htailEdges t3 (by simp [t3, hNheight])
  have hs0old : S.vertex s0 = T.vertex ⟨w.val, by omega⟩ := by
    rw [hs0]
    apply congrArg T.vertex
    apply Fin.ext
    have hjval : j.val = w.val := rfl
    have : iw0.val = w.val := by
      have hi := hiw0
      simp only [add_zero, hNheight, Nat.mod_eq_of_lt hw_bound, s0, j] at hi
      exact hi
    exact this
  have hov3eq : ov3 = v3 := by apply Fin.ext; simpa [s3, v3] using hov3
  have hov4eq : ov4 = v4 := by apply Fin.ext; simpa [s4, v4] using hov4
  have hoe2eq : oe2 = r2 := by apply Fin.ext; simpa [t2, r2] using hoe2
  have hoe3eq : oe3 = r3 := by apply Fin.ext; simpa [t3, r3] using hoe3
  have ht2old : S.edge t2 = T.edge r2 := by simpa [hoe2eq] using ht2
  have ht3old : S.edge t3 = T.edge r3 := by simpa [hoe3eq] using ht3
  have hs3old : S.vertex s3 = T.vertex v3 := by simpa [hov3eq] using hs3
  have hs4old : S.vertex s4 = T.vertex v4 := by simpa [hov4eq] using hs4
  have htailFixed := @helper_htailFixed_522 V E inferInstance inferInstance inferInstance G k e0 e0
      phi T N hNheight hlength w gamma hw_bound hcycle_colors a2 hgamma_alpha hgamma_beta a3 hwpos
      e1 psi S M hfixed hSlength hclosing iw0 iw1 iw2 ov3 ov4 oe2 oe3
  have ht2color : psi (S.edge t2) = some gamma := by
    rw [ht2old, htailFixed (T.edge r2) he2gamma]
    exact he2gamma
  have ht3color : psi (S.edge t3) = some gamma := by
    rw [ht3old, htailFixed (T.edge r3) he3gamma]
    exact he3gamma
  have hwcases : w.val = 1 ∨ w.val = 2 := by omega
  have hpairs := @helper_hpairs_718 V E inferInstance inferInstance inferInstance G k e0 phi T N
      hNheight hlength w gamma hw_bound a2 ha2val ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta
      hgamma_alpha hgamma_beta a3 ha3val ha3_ne_three ha3trunk ha3_ne_w ha23_ne hw0 hwpos e1 psi S M
      hSlength hclosing iw0 iw1 hiw1 iw2 hiw2 ov3 ov4 oe2 oe3 hwcases
  have hout2 : Incident G (S.vertex s3) (S.edge t2) := by
    rw [hs3old, ht2old]
    exact he2inc_new
  have hout3 : Incident G (S.vertex s4) (S.edge t3) := by
    rw [hs4old, ht3old]
    exact he3inc_new
  have hattach :
      (Incident G (S.vertex s1) (S.edge t2) ∧
          Incident G (S.vertex s2) (S.edge t3)) ∨
        (Incident G (S.vertex s2) (S.edge t2) ∧
          Incident G (S.vertex s1) (S.edge t3)) := by
    exact @helper_hattach_581 V E inferInstance inferInstance inferInstance G k e0 phi T N
        hNheight hlength w hw_bound a2 he2inc_attach a3 he3inc_attach hwpos e1 psi S M
        (by assumption) (by assumption) (by assumption) hSlength hclosing iw1 hs1 iw2 hs2 ht2old
        ht3old hpairs
  refine ⟨e1, psi, S, M, hSlen, hbalM, hMheight, ?_,
    ht2color, ht3color, hout2, hout3, hattach⟩
  rw [hs0old]
  exact hgammaOldPsi

private theorem helper_hgamma_alpha_773.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
      (hlength : (6 : ℕ) ≤ T.length),
    let v1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v2 : Fin (T.length + (1 : ℕ)) := (⟨(2 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k),
    phi (T.edge r2) = some gamma →
    let c1 : Fin N.height := (⟨(1 : ℕ), by omega⟩ : Fin N.height);
    phi (NormalCycleEdge N c1) = some N.alpha →
    G.ends (NormalCycleEdge N c1) = s(T.vertex v1, T.vertex v2) →
    IsProperEdgeColoring G phi →
    ∀ (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) :=
      a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt));
    (↑a2' : ℕ) < (3 : ℕ) →
    Incident G (T.vertex a2') (T.edge r2) →
    (↑a2' : ℕ) ≠ (↑w : ℕ) →
    (gamma = N.alpha → (↑w : ℕ) = (0 : ℕ)) →
    (gamma = N.beta → (↑w : ℕ) = (1 : ℕ)) →
    T.edge r2 ≠ NormalCycleEdge N c1 →
    gamma ≠ N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength v1 v2 r2 w gamma he2gamma c1 hc1color hc1ends
      hproper a2 a2' ha2val he2inc_attach ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta
      he2_ne_c1 hga
  have hw0 := hw_eq_zero_of_alpha hga
  have ha : a2'.val = 1 ∨ a2'.val = 2 := by omega
  have hinc : Incident G (T.vertex a2') (NormalCycleEdge N c1) := by
    rw [Incident, hc1ends]
    rcases ha with ha | ha
    · have hv : T.vertex a2' = T.vertex v1 := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa [v1] using ha
      rw [hv]
      simp
    · have hv : T.vertex a2' = T.vertex v2 := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa [v2] using ha
      rw [hv]
      simp
  have hadj : AdjacentEdges G (T.edge r2) (NormalCycleEdge N c1) :=
    ⟨T.vertex a2', he2inc_attach, hinc⟩
  exact (hproper he2_ne_c1 hadj he2gamma) (by simpa [hga] using hc1color)

private theorem helper_hgamma_beta_795.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (3 : ℕ))
        (hlength : (6 : ℕ) ≤ T.length),
    let v0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let v2 : Fin (T.length + (1 : ℕ)) := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k), phi (T.edge r2) = some gamma →
    let c2 : Fin N.height := (⟨(2 : ℕ),
    by omega
    ⟩ : Fin N.height); phi (NormalCycleEdge N c2) = some N.beta → G.ends (NormalCycleEdge N c2) =
        s(T.vertex v2, T.vertex v0) → IsProperEdgeColoring G phi →
    ∀ (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) := a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ
        r2.isLt)); (↑a2' : ℕ) < (3 : ℕ) → Incident G (T.vertex a2') (T.edge r2) → (↑a2' : ℕ) ≠ (↑w
        : ℕ) → (gamma = N.alpha → (↑w : ℕ) = (0 : ℕ)) → (gamma = N.beta → (↑w : ℕ) = (1 : ℕ)) →
        T.edge r2 ≠ NormalCycleEdge N c2 → gamma ≠ N.alpha → gamma ≠ N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hlength v0 v2 r2 w gamma he2gamma c2 hc2color hc2ends
      hproper a2 a2' ha2val he2inc_attach ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta
      he2_ne_c2 hgamma_alpha hgb
  have hw1 := hw_eq_one_of_beta hgb
  have ha : a2'.val = 0 ∨ a2'.val = 2 := by omega
  have hinc : Incident G (T.vertex a2') (NormalCycleEdge N c2) := by
    rw [Incident, hc2ends]
    rcases ha with ha | ha
    · have hv : T.vertex a2' = T.vertex v0 := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa [v0] using ha
      rw [hv]
      simp
    · have hv : T.vertex a2' = T.vertex v2 := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa [v2] using ha
      rw [hv]
      simp
  have hadj : AdjacentEdges G (T.edge r2) (NormalCycleEdge N c2) :=
    ⟨T.vertex a2', he2inc_attach, hinc⟩
  exact (hproper he2_ne_c2 hadj he2gamma) (by simpa [hgb] using hc2color)

private theorem helper_hZsub_1237.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (_ : NormalGlobalMaximumTriple G k e0 phi T),
    let this : DecidableEq V := Classical.decEq V;
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (_ : Fin ((↑r2 : ℕ) + (1 : ℕ)))
      (_ : Fin ((↑r3 : ℕ) + (1 : ℕ))) (e : E) (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
      (hSlen : (6 : ℕ) ≤ S.length) (hMheight : M.height = (3 : ℕ)),
    let s0 : Fin (S.length + (1 : ℕ)) := (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s1 : Fin (S.length + (1 : ℕ)) := (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s2 : Fin (S.length + (1 : ℕ)) := (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s3 : Fin (S.length + (1 : ℕ)) := (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s4 : Fin (S.length + (1 : ℕ)) := (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let t2 : Fin S.length := (⟨(2 : ℕ), by omega⟩ : Fin S.length);
    let t3 : Fin S.length := (⟨(3 : ℕ), by omega⟩ : Fin S.length);
    let d2 : Fin M.height := (⟨(2 : ℕ), by omega⟩ : Fin M.height);
    let q : E := NormalCycleEdge M d2;
    ∀
      (p :
        (TwoColorIncidenceGraph G psi gamma M.beta).Walk
          (Sum.inl
            (S.vertex (⟨(0 : ℕ), Nat.zero_lt_succ S.length⟩ : Fin (S.length + (1 : ℕ)))))
          (Sum.inl
            (S.vertex
              (⟨(1 : ℕ), Nat.succ_lt_succ S.positive⟩ : Fin (S.length + (1 : ℕ)))))),
    Sum.inl (S.vertex s0) ∈ p.support →
    Sum.inl (S.vertex s1) ∈ p.support →
    Sum.inl (S.vertex s2) ∈ p.support →
    Sum.inl (S.vertex s3) ∈ p.support →
    Sum.inl (S.vertex s4) ∈ p.support →
    Sum.inr q ∈ p.support →
    Sum.inr (S.edge t2) ∈ p.support →
    Sum.inr (S.edge t3) ∈ p.support →
    let Z : Finset (V ⊕ E) :=
      {Sum.inl (S.vertex s0), Sum.inl (S.vertex s1), Sum.inl (S.vertex s2),
        Sum.inl (S.vertex s3), Sum.inl (S.vertex s4), Sum.inr q, Sum.inr (S.edge t2),
        Sum.inr (S.edge t3)};
    Z ⊆ p.support.toFinset := by
  classical
  intro V E _ _ _ G k e0 phi T N this hlength r2 r3 w gamma a2 a3 e psi S M hSlen hMheight s0 s1
      s2 s3 s4 t2 t3 d2 q p hs0support hs1support hs2support hs3support hs4support hqsupport
      he2support he3support Z z hz
  simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [List.mem_toFinset]
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs0support
  · exact hs1support
  · exact hs2support
  · exact hs3support
  · exact hs4support
  · exact hqsupport
  · exact he2support
  · exact he3support

private theorem helper_continuation_1212.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (_ : E),
    ScheideGraphHeight G = (3 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (_ : NormalGlobalMaximumTriple G k e0 phi T),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (_ : Fin ((↑r2 : ℕ) + (1 : ℕ)))
      (_ : Fin ((↑r3 : ℕ) + (1 : ℕ))) (e : E) (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
      (hSlen : (6 : ℕ) ≤ S.length) (hMheight : M.height = (3 : ℕ)),
    let s0 : Fin (S.length + (1 : ℕ)) := (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s1 : Fin (S.length + (1 : ℕ)) := (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s2 : Fin (S.length + (1 : ℕ)) := (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s3 : Fin (S.length + (1 : ℕ)) := (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let s4 : Fin (S.length + (1 : ℕ)) := (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
    let t2 : Fin S.length := (⟨(2 : ℕ), by omega⟩ : Fin S.length);
    let t3 : Fin S.length := (⟨(3 : ℕ), by omega⟩ : Fin S.length);
    gamma ≠ M.beta →
    let d2 : Fin M.height := (⟨(2 : ℕ), by omega⟩ : Fin M.height);
    let q : E := NormalCycleEdge M d2;
    psi q = some M.beta →
    psi (S.edge t2) = some gamma →
    psi (S.edge t3) = some gamma →
    Incident G (S.vertex s3) (S.edge t2) →
    Incident G (S.vertex s4) (S.edge t3) →
    Incident G (S.vertex s1) (S.edge t2) ∧ Incident G (S.vertex s2) (S.edge t3) ∨
        Incident G (S.vertex s2) (S.edge t2) ∧ Incident G (S.vertex s1) (S.edge t3) →
    ∀
      (p :
        (TwoColorIncidenceGraph G psi gamma M.beta).Walk
          (Sum.inl
            (S.vertex (⟨(0 : ℕ), Nat.zero_lt_succ S.length⟩ : Fin (S.length + (1 : ℕ)))))
          (Sum.inl
            (S.vertex
              (⟨(1 : ℕ), Nat.succ_lt_succ S.positive⟩ : Fin (S.length + (1 : ℕ)))))),
    p.IsPath →
    {x : V ⊕ E | x ∈ p.support} =
        TwoColorComponent G psi gamma M.beta
          (Sum.inl
            (S.vertex (⟨(0 : ℕ), Nat.zero_lt_succ S.length⟩ : Fin (S.length + (1 : ℕ))))) →
    (4 : ℕ) ∣ p.length →
    p.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi gamma M.beta;
    let C : Set (V ⊕ E) := TwoColorComponent G psi gamma M.beta (Sum.inl (S.vertex s0));
    Sum.inl (S.vertex s0) ∈ C →
    (∀ {x y : V ⊕ E}, x ∈ C → H.Adj x y → y ∈ C) →
    Sum.inr q ∈ C →
    Sum.inl (S.vertex s2) ∈ C →
    Sum.inl (S.vertex s1) ∈ C →
    (∀ (i : Fin (S.length + (1 : ℕ))),
        Sum.inl (S.vertex i) ∈ C →
          Incident G (S.vertex i) (S.edge t2) → Sum.inr (S.edge t2) ∈ C) →
    False := by
  classical
  intro V E _ _ _ G k e0 hheight e0 phi T N this hlength r2 r3 w gamma a2 a3 e psi S M hSlen
      hMheight s0 s1 s2 s3 s4 t2 t3 hgamma_betaM d2 q hqcolor htail2' htail3' hout2' hout3'
      hattach' p hp hsupport hdiv hbound H C hrootC hcomp_step hqC hs2C hs1C hedge2_from
  have hedge3_from (i : Fin (S.length + 1))
      (hi : Sum.inl (S.vertex i) ∈ C)
      (hinc : Incident G (S.vertex i) (S.edge t3)) :
      Sum.inr (S.edge t3) ∈ C := by
    apply hcomp_step hi
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex i) (S.edge t3) ∧
          (psi (S.edge t3) = some gamma ∨ psi (S.edge t3) = some M.beta) from
        ⟨hinc, Or.inl htail3'⟩)
  have he2C : Sum.inr (S.edge t2) ∈ C := by
    rcases hattach' with h | h
    · exact hedge2_from s1 hs1C h.1
    · exact hedge2_from s2 hs2C h.1
  have he3C : Sum.inr (S.edge t3) ∈ C := by
    rcases hattach' with h | h
    · exact hedge3_from s2 hs2C h.2
    · exact hedge3_from s1 hs1C h.2
  have hadje23 : H.Adj (Sum.inr (S.edge t2)) (Sum.inl (S.vertex s3)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s3) (S.edge t2) ∧
          (psi (S.edge t2) = some gamma ∨ psi (S.edge t2) = some M.beta) from
        ⟨hout2', Or.inl htail2'⟩)
  have hadje34 : H.Adj (Sum.inr (S.edge t3)) (Sum.inl (S.vertex s4)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s4) (S.edge t3) ∧
          (psi (S.edge t3) = some gamma ∨ psi (S.edge t3) = some M.beta) from
        ⟨hout3', Or.inl htail3'⟩)
  have hs3C : Sum.inl (S.vertex s3) ∈ C := hcomp_step he2C hadje23
  have hs4C : Sum.inl (S.vertex s4) ∈ C := hcomp_step he3C hadje34
  have hC_support {z : Sum V E} (hz : z ∈ C) : z ∈ p.support := by
    have hc : z ∈ TwoColorComponent G psi gamma M.beta
        (Sum.inl (S.vertex ⟨0, by omega⟩)) := by
      simpa [C, s0] using hz
    exact (Set.ext_iff.mp hsupport z).mpr hc
  have hs0support : Sum.inl (S.vertex s0) ∈ p.support := hC_support hrootC
  have hs1support : Sum.inl (S.vertex s1) ∈ p.support := hC_support hs1C
  have hs2support : Sum.inl (S.vertex s2) ∈ p.support := hC_support hs2C
  have hs3support : Sum.inl (S.vertex s3) ∈ p.support := hC_support hs3C
  have hs4support : Sum.inl (S.vertex s4) ∈ p.support := hC_support hs4C
  have hqsupport : Sum.inr q ∈ p.support := hC_support hqC
  have he2support : Sum.inr (S.edge t2) ∈ p.support := hC_support he2C
  have he3support : Sum.inr (S.edge t3) ∈ p.support := hC_support he3C
  have hq_ne_e2 : q ≠ S.edge t2 := by
    intro heq
    rw [heq, htail2'] at hqcolor
    exact hgamma_betaM (Option.some.inj hqcolor)
  have hq_ne_e3 : q ≠ S.edge t3 := by
    intro heq
    rw [heq, htail3'] at hqcolor
    exact hgamma_betaM (Option.some.inj hqcolor)
  have he23 : S.edge t2 ≠ S.edge t3 := by
    intro heq
    have hi := S.edge_injective heq
    have := congrArg Fin.val hi
    simp [t2, t3] at this
  let Z : Finset (Sum V E) :=
    {Sum.inl (S.vertex s0), Sum.inl (S.vertex s1),
      Sum.inl (S.vertex s2), Sum.inl (S.vertex s3),
      Sum.inl (S.vertex s4), Sum.inr q,
      Sum.inr (S.edge t2), Sum.inr (S.edge t3)}
  have hZcard : Z.card = 8 := by
    simp [Z, S.vertex_injective.eq_iff, hq_ne_e2, hq_ne_e3, he23,
      s0, s1, s2, s3, s4, t2, t3]
  have hZsub := @helper_hZsub_1237 V E inferInstance inferInstance inferInstance G k e0 phi T N
      hlength w gamma a2 a3 e psi S M hSlen hMheight p hs0support hs1support hs2support hs3support
      hs4support hqsupport he2support he3support
  have hseven : 7 ≤ p.length := by
    have hc := Finset.card_le_card hZsub
    rw [hZcard, List.toFinset_card_of_nodup hp.support_nodup,
      p.length_support] at hc
    omega
  have height : 8 ≤ p.length := by
    rcases hdiv with ⟨d, hd⟩
    omega
  have hfive : 5 ≤ p.length / 2 + 1 := by omega
  omega

private theorem helper_continuation_1208.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (_ : E),
    ScheideGraphHeight G = (3 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (_ : NormalGlobalMaximumTriple G k e0 phi T),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (_ : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k) (_ : Fin ((↑r2 : ℕ) + (1 : ℕ)))
      (_ : Fin ((↑r3 : ℕ) + (1 : ℕ))) (e : E) (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
      (hSlen : (6 : ℕ) ≤ S.length),
    BalancedGlobalMaximumTriple M →
    M.height = (3 : ℕ) →
    gamma ∈
        MissingColors G psi (S.vertex (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) →
    psi (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) = some gamma →
    psi (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) = some gamma →
    Incident G (S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
        (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) →
    Incident G (S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
        (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) →
    Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
            (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
          Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
            (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) ∨
        Incident G (S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
            (S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length)) ∧
          Incident G (S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))
            (S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length)) →
    False := by
  classical
  intro V E _ _ _ G k e0 hheight e0 phi T N this hlength r2 r3 w gamma a2 a3 e psi S M hSlen
      hbalM hMheight hgamma0 htail2 htail3 hout2 hout3 hattach
  let s0 : Fin (S.length + 1) := ⟨0, by omega⟩
  let s1 : Fin (S.length + 1) := ⟨1, by omega⟩
  let s2 : Fin (S.length + 1) := ⟨2, by omega⟩
  let s3 : Fin (S.length + 1) := ⟨3, by omega⟩
  let s4 : Fin (S.length + 1) := ⟨4, by omega⟩
  let t2 : Fin S.length := ⟨2, by omega⟩
  let t3 : Fin S.length := ⟨3, by omega⟩
  have hgamma0' : gamma ∈ MissingColors G psi (S.vertex s0) := by
    simpa [s0] using hgamma0
  have hbeta1 : M.beta ∈ MissingColors G psi (S.vertex s1) := by
    simpa [s1] using M.beta_missing
  have helemS : ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) :=
    (ScheideGlobalMaximumOrder G k e psi S M.global).2.2.2.1
  have hmemS (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp [TreeSequenceVertexSet]
  have hgamma_betaM : gamma ≠ M.beta := by
    intro heq
    have hne : S.vertex s0 ≠ S.vertex s1 := by
      intro hv
      have hi := S.vertex_injective hv
      have := congrArg Fin.val hi
      simp [s0, s1] at this
    have hd := helemS (hmemS s0) (hmemS s1) hne
    exact (Finset.disjoint_left.mp hd) hgamma0' (by simpa [heq] using hbeta1)
  have hcycleM := ScheideTrunkRotationCycle G k e psi S M hbalM
  have hcycleMends := hcycleM.2.2.2.1
  have hcycleMcolors := hcycleM.2.2.2.2
  let d2 : Fin M.height := ⟨2, by omega⟩
  let q : E := NormalCycleEdge M d2
  have hqcolor : psi q = some M.beta := by
    have hnotodd : ¬ Odd (2 : ℕ) := by
      rintro ⟨x, hx⟩
      omega
    simpa [q, d2, hnotodd] using hcycleMcolors d2 (by simp [d2])
  have hqends : G.ends q = s(S.vertex s2, S.vertex s0) := by
    simpa [q, d2, s2, s0, hMheight] using hcycleMends d2
  have hqinc0 : Incident G (S.vertex s0) q := by
    rw [Incident, hqends]
    simp
  have hqinc2 : Incident G (S.vertex s2) q := by
    rw [Incident, hqends]
    simp
  have htail2' : psi (S.edge t2) = some gamma := by simpa [t2] using htail2
  have htail3' : psi (S.edge t3) = some gamma := by simpa [t3] using htail3
  have hout2' : Incident G (S.vertex s3) (S.edge t2) := by
    simpa [s3, t2] using hout2
  have hout3' : Incident G (S.vertex s4) (S.edge t3) := by
    simpa [s4, t3] using hout3
  have hattach' :
      (Incident G (S.vertex s1) (S.edge t2) ∧
          Incident G (S.vertex s2) (S.edge t3)) ∨
        (Incident G (S.vertex s2) (S.edge t2) ∧
          Incident G (S.vertex s1) (S.edge t3)) := by
    simpa [s1, s2, t2, t3] using hattach
  obtain ⟨p, hp, hsupport, hdiv, hvertices, hbound⟩ :=
    ScheideKempePathHeightBound G k e psi S M.global gamma M.beta
      hgamma0' hbeta1
  let H := TwoColorIncidenceGraph G psi gamma M.beta
  let C := TwoColorComponent G psi gamma M.beta (Sum.inl (S.vertex s0))
  have hrootC : Sum.inl (S.vertex s0) ∈ C := by
    change H.connectedComponentMk (Sum.inl (S.vertex s0)) =
      H.connectedComponentMk (Sum.inl (S.vertex s0))
    rfl
  have hcomp_step {x y : Sum V E} (hx : x ∈ C) (hxy : H.Adj x y) : y ∈ C := by
    change H.connectedComponentMk x = H.connectedComponentMk (Sum.inl (S.vertex s0)) at hx
    change H.connectedComponentMk y = H.connectedComponentMk (Sum.inl (S.vertex s0))
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans hx
  have hadj0q : H.Adj (Sum.inl (S.vertex s0)) (Sum.inr q) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s0) q ∧
          (psi q = some gamma ∨ psi q = some M.beta) from
        ⟨hqinc0, Or.inr hqcolor⟩)
  have hqC : Sum.inr q ∈ C := hcomp_step hrootC hadj0q
  have hadjq2 : H.Adj (Sum.inr q) (Sum.inl (S.vertex s2)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s2) q ∧
          (psi q = some gamma ∨ psi q = some M.beta) from
        ⟨hqinc2, Or.inr hqcolor⟩)
  have hs2C : Sum.inl (S.vertex s2) ∈ C := hcomp_step hqC hadjq2
  have hs1C : Sum.inl (S.vertex s1) ∈ C := by
    have hsupp : Sum.inl (S.vertex s1) ∈ p.support := by
      have hm := p.getVert_mem_support p.length
      rw [p.getVert_length] at hm
      simpa [s1] using hm
    have hc : Sum.inl (S.vertex s1) ∈
        TwoColorComponent G psi gamma M.beta
          (Sum.inl (S.vertex ⟨0, by omega⟩)) := by
      rw [← hsupport]
      exact hsupp
    simpa [C, s0] using hc
  have hedge2_from (i : Fin (S.length + 1))
      (hi : Sum.inl (S.vertex i) ∈ C)
      (hinc : Incident G (S.vertex i) (S.edge t2)) :
      Sum.inr (S.edge t2) ∈ C := by
    apply hcomp_step hi
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex i) (S.edge t2) ∧
          (psi (S.edge t2) = some gamma ∨ psi (S.edge t2) = some M.beta) from
        ⟨hinc, Or.inl htail2'⟩)
  exact @helper_continuation_1212 V E inferInstance inferInstance inferInstance G k e0 hheight e0
      phi T N hlength w gamma a2 a3 e psi S M hSlen hMheight hgamma_betaM hqcolor htail2' htail3'
      hout2' hout3' hattach' p hp hsupport hdiv hbound hrootC hcomp_step hqC hs2C hs1C hedge2_from
private theorem helper_continuation_1136.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (_ : E),
    ScheideGraphHeight G = (3 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T),
    BalancedGlobalMaximumTriple N →
    ∀ (hNheight : N.height = (3 : ℕ)),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hlength : (6 : ℕ) ≤ T.length),
    let v0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v2 : Fin (T.length + (1 : ℕ)) := (⟨(2 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let v3 : Fin (T.length + (1 : ℕ)) := (⟨(3 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let _ : Fin (T.length + (1 : ℕ)) := (⟨(4 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ), by omega⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ), by omega⟩ : Fin T.length);
    ∀ (w : Fin ((↑r2 : ℕ) + (1 : ℕ))) (gamma : Fin k),
    phi (T.edge r2) = some gamma →
    (↑w : ℕ) < (3 : ℕ) →
    gamma ∈
        MissingColors G phi (T.vertex (⟨(↑w : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))) →
    phi (T.edge r3) = some gamma →
    (∀ (i : Fin N.height),
        (1 : ℕ) ≤ (↑i : ℕ) →
          phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then some N.alpha else some N.beta) →
    let c1 : Fin N.height := (⟨(1 : ℕ), by omega⟩ : Fin N.height);
    let c2 : Fin N.height := (⟨(2 : ℕ), by omega⟩ : Fin N.height);
    phi (NormalCycleEdge N c1) = some N.alpha →
    phi (NormalCycleEdge N c2) = some N.beta →
    G.ends (NormalCycleEdge N c1) = s(T.vertex v1, T.vertex v2) →
    G.ends (NormalCycleEdge N c2) = s(T.vertex v2, T.vertex v0) →
    IsProperEdgeColoring G phi →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) →
    (∀ (i : Fin (T.length + (1 : ℕ))), T.vertex i ∈ TreeSequenceVertexSet T) →
    (∀ {c : Fin k} {i : Fin (T.length + (1 : ℕ))},
        c ∈ MissingColors G phi (T.vertex i) →
          ∀ {f : E}, Incident G (T.vertex i) f → phi f ≠ some c) →
    ∀ (a2 : Fin ((↑r2 : ℕ) + (1 : ℕ))),
    let a2' : Fin (T.length + (1 : ℕ)) :=
      a2.castLT (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt));
    (↑a2' : ℕ) < (3 : ℕ) →
    G.ends (T.edge r2) = s(T.vertex v3, T.vertex a2') →
    Incident G (T.vertex v3) (T.edge r2) →
    Incident G (T.vertex a2') (T.edge r2) →
    (↑a2' : ℕ) ≠ (↑w : ℕ) →
    False := by
  classical
  intro V E _ _ _ G k e0 hheight e0 phi T N hbalanced hNheight this hlength v0 v1 v2 v3 v4 r2 r3
      w gamma he2gamma hw_bound hwgamma' he3gamma hcycle_colors c1 c2 hc1color hc2color hc1ends
      hc2ends hproper helem hvertex_mem hmissing_absent a2 a2' ha2val ha2ends' he2inc_new
      he2inc_attach ha2_ne_w
  have hw_eq_zero_of_alpha (hga : gamma = N.alpha) : w.val = 0 := by
    by_contra hw0
    have hne : T.vertex ⟨w.val, by omega⟩ ≠ T.vertex v0 := by
      intro hv
      have hi := T.vertex_injective hv
      apply hw0
      simpa [v0] using congrArg Fin.val hi
    have hd := helem (hvertex_mem ⟨w.val, by omega⟩) (hvertex_mem v0) hne
    exact (Finset.disjoint_left.mp hd) hwgamma' (by simpa [hga, v0] using N.alpha_missing)
  have hw_eq_one_of_beta (hgb : gamma = N.beta) : w.val = 1 := by
    by_contra hw1
    have hne : T.vertex ⟨w.val, by omega⟩ ≠ T.vertex v1 := by
      intro hv
      have hi := T.vertex_injective hv
      apply hw1
      simpa [v1] using congrArg Fin.val hi
    have hd := helem (hvertex_mem ⟨w.val, by omega⟩) (hvertex_mem v1) hne
    exact (Finset.disjoint_left.mp hd) hwgamma' (by simpa [hgb, v1] using N.beta_missing)
  have he2_ne_c1 : T.edge r2 ≠ NormalCycleEdge N c1 := by
    intro heq
    have hpairs : s(T.vertex v3, T.vertex a2') = s(T.vertex v1, T.vertex v2) := by
      rw [← ha2ends', ← hc1ends, heq]
    rcases Sym2.eq_iff.mp hpairs with h | h
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v1] at this
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v2] at this
  have he2_ne_c2 : T.edge r2 ≠ NormalCycleEdge N c2 := by
    intro heq
    have hpairs : s(T.vertex v3, T.vertex a2') = s(T.vertex v2, T.vertex v0) := by
      rw [← ha2ends', ← hc2ends, heq]
    rcases Sym2.eq_iff.mp hpairs with h | h
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v2] at this
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v0] at this
  have hgamma_alpha := @helper_hgamma_alpha_773 V E inferInstance inferInstance inferInstance G k e0
      phi T N hNheight hlength w gamma he2gamma hc1color hc1ends hproper a2 ha2val he2inc_attach
      ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta he2_ne_c1
  have hgamma_beta := @helper_hgamma_beta_795 V E inferInstance inferInstance inferInstance G k e0
      phi T N hNheight hlength w gamma he2gamma hc2color hc2ends hproper a2 ha2val he2inc_attach
      ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta he2_ne_c2 hgamma_alpha
  obtain ⟨a3, ha3ends⟩ := T.attaches r3
  let a3' : Fin (T.length + 1) :=
    Fin.castLT a3 (Nat.lt_trans a3.isLt (Nat.succ_lt_succ r3.isLt))
  have ha3val : a3'.val < 4 := by simp [a3', r3]
  have ha3ends' : G.ends (T.edge r3) = s(T.vertex v4, T.vertex a3') := by
    simpa [r3, v4, a3'] using ha3ends
  have he3inc_new : Incident G (T.vertex v4) (T.edge r3) := by
    rw [Incident, ha3ends']
    simp
  have he3inc_attach : Incident G (T.vertex a3') (T.edge r3) := by
    rw [Incident, ha3ends']
    simp
  have he23_ne : T.edge r2 ≠ T.edge r3 := by
    intro heq
    have hi := T.edge_injective heq
    have := congrArg Fin.val hi
    simp [r2, r3] at this
  have ha3_ne_three : a3'.val ≠ 3 := by
    intro ha
    have hv : T.vertex a3' = T.vertex v3 := by
      apply congrArg T.vertex
      apply Fin.ext
      simpa [v3] using ha
    have hadj : AdjacentEdges G (T.edge r2) (T.edge r3) :=
      ⟨T.vertex v3, he2inc_new, hv ▸ he3inc_attach⟩
    exact (hproper he23_ne hadj he2gamma) he3gamma
  have ha3trunk : a3'.val < 3 := by omega
  have ha3_ne_w : a3'.val ≠ w.val := by
    intro haw
    have hv : T.vertex a3' = T.vertex ⟨w.val, by omega⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      exact haw
    exact hmissing_absent hwgamma' (hv ▸ he3inc_attach) he3gamma
  have ha23_ne : a2'.val ≠ a3'.val := by
    intro ha
    have hv : T.vertex a2' = T.vertex a3' := by
      apply congrArg T.vertex
      apply Fin.ext
      exact ha
    have hadj : AdjacentEdges G (T.edge r2) (T.edge r3) :=
      ⟨T.vertex a2', he2inc_attach, hv ▸ he3inc_attach⟩
    exact (hproper he23_ne hadj he2gamma) he3gamma
  obtain ⟨e, psi, S, M, hSlen, hbalM, hMheight, hgamma0,
      htail2, htail3, hout2, hout3, hattach⟩ :
      ∃ (e : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
        (M : NormalGlobalMaximumTriple G k e psi S) (hSlen : 6 ≤ S.length),
        BalancedGlobalMaximumTriple M ∧ M.height = 3 ∧
        gamma ∈ MissingColors G psi
          (S.vertex ⟨0, by omega⟩) ∧
        psi (S.edge ⟨2, by omega⟩) = some gamma ∧
        psi (S.edge ⟨3, by omega⟩) = some gamma ∧
        Incident G (S.vertex ⟨3, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
        Incident G (S.vertex ⟨4, by omega⟩) (S.edge ⟨3, by omega⟩) ∧
        ((Incident G (S.vertex ⟨1, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
            Incident G (S.vertex ⟨2, by omega⟩) (S.edge ⟨3, by omega⟩)) ∨
          (Incident G (S.vertex ⟨2, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
            Incident G (S.vertex ⟨1, by omega⟩) (S.edge ⟨3, by omega⟩))) := by
    by_cases hw0 : w.val = 0
    · exact @helper_branch_300 V E inferInstance inferInstance inferInstance G k e0 e0 phi T N
        hbalanced hNheight hlength w gamma he2gamma hwgamma' he3gamma a2 ha2val he2inc_new
        he2inc_attach ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta hgamma_alpha hgamma_beta a3
        ha3val he3inc_new he3inc_attach ha3_ne_three ha3trunk ha3_ne_w ha23_ne hw0
    · exact @helper_branch_335 V E inferInstance inferInstance inferInstance G k e0 e0 phi T N
        hbalanced hNheight hlength w gamma he2gamma hw_bound hwgamma' he3gamma hcycle_colors a2
        ha2val he2inc_new he2inc_attach ha2_ne_w hw_eq_zero_of_alpha hw_eq_one_of_beta
        hgamma_alpha hgamma_beta a3 ha3val he3inc_new he3inc_attach ha3_ne_three ha3trunk
        ha3_ne_w ha23_ne hw0
  exact @helper_continuation_1208 V E inferInstance inferInstance inferInstance G k e0 hheight e0
      phi T N hlength w gamma a2 a3 e psi S M hSlen hbalM hMheight hgamma0 htail2 htail3 hout2
      hout3 hattach
theorem ScheideSmallHeightElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hsmall : ScheideGraphHeight G < 5) :
    Elementary G := by
  classical
  obtain ⟨e0, phi0, T0, hglobal0⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  have hheight : ScheideGraphHeight G = 3 := by
    have hodd := ScheideGraphHeightOdd G k e0 phi0 T0 hglobal0
    rcases hodd.2 with ⟨m, hm⟩
    omega
  obtain ⟨e0, phi, T, N, hbalanced⟩ :=
    ScheideBalancedExists G k e0 phi0 T0 hglobal0
  have hNheight : N.height = 3 := hbalanced.1.trans hheight
  let : DecidableEq V := Classical.decEq V
  by_contra hnon
  have horder : 7 ≤ TashkinovOrder G := by
    have hnlt : ¬ TashkinovOrder G - 4 < ScheideGraphHeight G := by
      intro hlt
      exact hnon (ScheideLargeHeightElementary G k hcritical hindex hdegree
        hnoisolated hlt)
    omega
  have hcard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_of_injective Finset.univ T.vertex_injective]
    simp
  have hlength : 6 ≤ T.length := by
    have hmax := N.global.2.2
    omega
  let v0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let v1 : Fin (T.length + 1) := ⟨1, by omega⟩
  let v2 : Fin (T.length + 1) := ⟨2, by omega⟩
  let v3 : Fin (T.length + 1) := ⟨3, by omega⟩
  let v4 : Fin (T.length + 1) := ⟨4, by omega⟩
  let r1 : Fin T.length := ⟨1, by omega⟩
  let r2 : Fin T.length := ⟨2, by omega⟩
  let r3 : Fin T.length := ⟨3, by omega⟩
  have htail : phi (T.edge r2) = phi (T.edge r3) := by
    simpa [r2, r3] using hbalanced.2 2 (by omega) (by omega)
  obtain ⟨w, gamma, he2gamma, hwgamma⟩ := N.global.2.1 r2 (by simp [r2])
  have hw_bound : w.val < 3 := w.isLt
  have hwgamma' : gamma ∈ MissingColors G phi
      (T.vertex ⟨w.val, by omega⟩) := by
    have hidx : Fin.castLT w
        (Nat.lt_trans w.isLt (Nat.succ_lt_succ r2.isLt)) =
        (⟨w.val, by omega⟩ : Fin (T.length + 1)) := Fin.ext rfl
    rw [← hidx]
    exact hwgamma
  have he3gamma : phi (T.edge r3) = some gamma := by
    rw [← htail]
    exact he2gamma
  have hcycle := ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  have hcycle_ends := hcycle.2.2.2.1
  have hcycle_colors := hcycle.2.2.2.2
  let c1 : Fin N.height := ⟨1, by omega⟩
  let c2 : Fin N.height := ⟨2, by omega⟩
  have hc1color : phi (NormalCycleEdge N c1) = some N.alpha := by
    simpa [c1] using hcycle_colors c1 (by simp [c1])
  have hc2color : phi (NormalCycleEdge N c2) = some N.beta := by
    have hnotodd : ¬ Odd (2 : ℕ) := by
      rintro ⟨x, hx⟩
      omega
    simpa [c2, hnotodd] using hcycle_colors c2 (by simp [c2])
  have hc1ends : G.ends (NormalCycleEdge N c1) =
      s(T.vertex v1, T.vertex v2) := by
    simpa [c1, v1, v2, hNheight] using hcycle_ends c1
  have hc2ends : G.ends (NormalCycleEdge N c2) =
      s(T.vertex v2, T.vertex v0) := by
    simpa [c2, v2, v0, hNheight] using hcycle_ends c2
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    (ScheideGlobalMaximumOrder G k e0 phi T N.global).2.2.2.1
  have hvertex_mem (i : Fin (T.length + 1)) :
      T.vertex i ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hmissing_absent {c : Fin k} {i : Fin (T.length + 1)}
      (hm : c ∈ MissingColors G phi (T.vertex i)) {f : E}
      (hinc : Incident G (T.vertex i) f) : phi f ≠ some c := by
    intro hfc
    have hp : c ∈ PresentColors G phi (T.vertex i) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hinc, hfc⟩
    have hnp : c ∉ PresentColors G phi (T.vertex i) := by
      simpa [MissingColors] using hm
    exact hnp hp
  obtain ⟨a2, ha2ends⟩ := T.attaches r2
  let a2' : Fin (T.length + 1) :=
    Fin.castLT a2 (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt))
  have ha2val : a2'.val < 3 := by simp [a2', r2]
  have ha2ends' : G.ends (T.edge r2) = s(T.vertex v3, T.vertex a2') := by
    simpa [r2, v3, a2'] using ha2ends
  have he2inc_new : Incident G (T.vertex v3) (T.edge r2) := by
    rw [Incident, ha2ends']
    simp
  have he2inc_attach : Incident G (T.vertex a2') (T.edge r2) := by
    rw [Incident, ha2ends']
    simp
  have ha2_ne_w : a2'.val ≠ w.val := by
    intro haw
    have hv : T.vertex a2' = T.vertex ⟨w.val, by omega⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      exact haw
    exact hmissing_absent hwgamma' (hv ▸ he2inc_attach) he2gamma
  exact @helper_continuation_1136 V E inferInstance inferInstance inferInstance G k e0 hheight e0
      phi T N hbalanced hNheight hlength w gamma he2gamma hw_bound hwgamma' he3gamma
      hcycle_colors hc1color hc2color hc1ends hc2ends hproper helem hvertex_mem hmissing_absent
      a2 ha2val ha2ends' he2inc_new he2inc_attach ha2_ne_w
end GoldbergSeymour

end
