/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed

/-!
# Scheide Replacement Maximum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev ScheideReplacementMaximumBranch56Branch173Conditions.{u_1, u_2} : Prop :=
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); (IsProperEdgeColoring G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) e0 ∧ TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) (D.f0 d) = some (C.gamma
        (D.gammaIndex d)) ∧ MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = insert (↑d : Fin k) ((MissingColors G phi
        (D.v0 d)).erase (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → ¬f = D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, ¬v = D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) →
    ∀ (j : Fin R.replacementTree.length), 1 ≤ (↑j : ℕ) → R.replacementTree.length = T.length → 1 ≤
        T.length → (
    ∀ (q : ℕ) (hq : q < T.length), T.edge ⟨q, hq⟩ ≠ D.f0 d → phiD (T.edge ⟨q, hq⟩) = phi (T.edge
        ⟨q, hq⟩)) → (
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d → MissingColors G phiD v = MissingColors G phi v) →
    let alpha := C.gamma (D.gammaIndex d); (
    ∀ (c : Fin k), c ≠ alpha → c ∈ MissingColors G phi (D.v0 d) → c ∈ MissingColors G phiD (D.v0
        d)) → ¬(↑j : ℕ) < C.p - 1 + 2 * (↑(D.gammaIndex d) : ℕ) →
    ∃ (i : Fin ((↑j : ℕ) + 1)) (c : Fin k), TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)) (R.replacementTree.edge j) = some c ∧ c ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (R.replacementTree.vertex (i.castLT ((
    by
                  first
                  | omega
    ))))

private theorem ScheideReplacementMaximum_branch_56_branch_89.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); TashkinovTree G e0 phi T →
    ∀ (j : Fin R.replacementTree.length), 1 ≤ (↑j : ℕ) → R.replacementTree.length = T.length → (
    ∀ (q : ℕ) (hq : q < T.length), T.edge ⟨q, hq⟩ ≠ D.f0 d → phiD (T.edge ⟨q, hq⟩) = phi (T.edge
        ⟨q, hq⟩)) → (
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d → MissingColors G phiD v = MissingColors G phi v) →
    let alpha := C.gamma (D.gammaIndex d); (
    ∀ (c : Fin k), c ≠ alpha → c ∈ MissingColors G phi (D.v0 d) → c ∈ MissingColors G phiD (D.v0
        d)) → (↑j : ℕ) < C.p - 1 + 2 * (↑(D.gammaIndex d) : ℕ) →
    ∃ (i : Fin ((↑j : ℕ) + 1)) (c : Fin k), TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)) (R.replacementTree.edge j) = some c ∧ c ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (R.replacementTree.vertex (i.castLT ((
    by first  | omega
    )))) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R phiD htree j hj hlen edge_fixed missing_fixed alpha
      alpha_ne hbefore
  have hjold : j.val < T.length := by omega
  obtain ⟨i, c, he, hm⟩ := htree ⟨j.val, hjold⟩ (by omega)
  have hi := i.isLt
  have hij : i.val ≤ j.val := Nat.le_of_lt_succ hi
  have hcast : i.val < R.replacementTree.length := by omega
  refine ⟨⟨i.val, by omega⟩, c, ?_, ?_⟩
  · rw [R.retained_edges_before j.val hbefore (by omega)]
    have hfix := edge_fixed j.val (by omega) (by
      intro hzero
      have hz := D.f0_ends d
      have ha := T.attaches ⟨j.val, by omega⟩
      rw [hzero] at ha
      have hu := D.u0_outside d
      obtain ⟨q, hq⟩ := ha
      have huend : D.u0 d ∈ G.ends (T.edge ⟨j.val, by omega⟩) := by
        rw [hzero, D.f0_ends]
        simp
      rw [hzero, hq] at huend
      have huvertex : D.u0 d = T.vertex ⟨j.val + 1, by omega⟩ ∨
          D.u0 d = T.vertex (q.castLT (by omega)) := by
        simpa using huend
      have huin : D.u0 d ∈ TreeSequenceVertexSet T := by
        rcases huvertex with hleft | hright
        · simp [TreeSequenceVertexSet, hleft]
        · simp [TreeSequenceVertexSet, hright]
      exact hu huin)
    change phiD (T.edge ⟨j.val, by omega⟩) = some c
    rw [hfix]
    exact he
  · change c ∈ MissingColors G phiD (R.replacementTree.vertex ⟨i.val, by omega⟩)
    rw [R.retained_vertices_before i.val (by omega) (by omega)]
    by_cases hi0 : (T.vertex ⟨i.val, by omega⟩) = D.v0 d
    · by_cases hsmall : j.val < C.p - 1
      · have hc : c ≠ alpha := by
          dsimp [alpha]
          intro hac
          have havoid := C.initial_nonfirst_avoids_blocks ⟨j.val, by omega⟩ (by omega) c
            (by simpa [C.base_edge_position ⟨j.val, by omega⟩] using he) (D.gammaIndex d)
          exact havoid (hac.trans rfl)
        rw [hi0]
        apply alpha_ne c hc
        rw [← hi0]
        exact hm
      · let h : Fin C.s := ⟨(j.val - (C.p - 1)) / 2, by omega⟩
        have hcolor : c = C.gamma h := by
          have hdiv := Nat.mod_add_div (j.val - (C.p - 1)) 2
          have hlenC := C.length_eq
          have hval : h.val = (j.val - (C.p - 1)) / 2 := rfl
          have hb := C.block_color h ⟨(j.val - (C.p - 1)) % 2, by omega⟩
          have hentry : T.edge ⟨j.val, by omega⟩ =
              C.blockEdge h ⟨(j.val - (C.p - 1)) % 2, by omega⟩ := by
            calc
              T.edge ⟨j.val, by omega⟩ =
                  T.edge ⟨C.p - 1 + 2 * h.val + ((j.val - (C.p - 1)) % 2), by omega⟩ := by
                    apply congrArg T.edge
                    apply Fin.ext
                    have hnum : C.p - 1 + 2 * h.val +
                        ((j.val - (C.p - 1)) % 2) = j.val := by
                      dsimp [h]
                      omega
                    exact hnum.symm
              _ = C.blockEdge h ⟨(j.val - (C.p - 1)) % 2, by omega⟩ :=
                C.block_edge_position h ⟨(j.val - (C.p - 1)) % 2, by omega⟩
          rw [hentry] at he
          exact Option.some.inj (he.symm.trans hb)
        have hne : c ≠ alpha := by
          intro hh
          dsimp [alpha] at hh
          have heq := C.gamma_injective (hcolor.symm.trans hh)
          have hlt := h.isLt
          have hr := (D.gammaIndex d).isLt
          have heqv := congrArg Fin.val heq
          dsimp [h] at hlt heqv
          omega
        rw [hi0]
        apply alpha_ne c hne
        rw [← hi0]
        exact hm
    · rw [missing_fixed _ (by simp [TreeSequenceVertexSet]) hi0]
      have hv : T.vertex (⟨i.val, by omega⟩ : Fin (T.length + 1)) =
          T.vertex (i.castLT (by omega)) := by
        congr 1
      rw [hv]
      exact hm

private theorem ScheideReplacementMaximum_branch_56_branch_173.{u_1, u_2} :
    ScheideReplacementMaximumBranch56Branch173Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R phiD heffect j hj hlen hpos edge_fixed missing_fixed
      alpha alpha_ne hbefore
  by_cases hafter : j.val + 2 < T.length
  · have hjold : j.val < T.length := by omega
    let h : Fin C.s := ⟨(j.val + 2 - (C.p - 1)) / 2, by
      have hc := C.length_eq
      omega⟩
    have hdiv := Nat.mod_add_div (j.val + 2 - (C.p - 1)) 2
    have hnum : C.p - 1 + 2 * h.val +
        ((j.val + 2 - (C.p - 1)) % 2) = j.val + 2 := by
      dsimp [h]
      omega
    have hentry : T.edge ⟨j.val + 2, hafter⟩ =
        C.blockEdge h ⟨(j.val + 2 - (C.p - 1)) % 2, by omega⟩ := by
      calc
        T.edge ⟨j.val + 2, hafter⟩ =
            T.edge ⟨C.p - 1 + 2 * h.val +
              ((j.val + 2 - (C.p - 1)) % 2), by omega⟩ := by
          apply congrArg T.edge
          apply Fin.ext
          exact hnum.symm
        _ = _ := C.block_edge_position h
          ⟨(j.val + 2 - (C.p - 1)) % 2, by omega⟩
    have hcolor : phi (T.edge ⟨j.val + 2, hafter⟩) = some (C.gamma h) := by
      rw [hentry]
      exact C.block_color h _
    obtain ⟨q, hq⟩ := C.block_color_missing_on_base h
    have hbase : T.vertex ⟨q.val, by omega⟩ = C.y q := C.base_vertex_position q
    have hneq : C.gamma h ≠ alpha := by
      intro heq
      have hh := C.gamma_injective (heq.symm.trans rfl)
      have hh' := congrArg Fin.val hh
      have hr := (D.gammaIndex d).isLt
      have hc := C.length_eq
      dsimp [alpha, h] at heq hh'
      omega
    have hqbound : q.val ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by
      have hq' := q.isLt
      omega
    have hqearly : q.val < j.val + 1 := by omega
    refine ⟨⟨q.val, hqearly⟩, C.gamma h, ?_, ?_⟩
    · rw [R.retained_edges_after j.val (by omega) hafter]
      have hfix := edge_fixed (j.val + 2) (by omega) (by
        intro hzero
        obtain ⟨q, hq⟩ := T.attaches ⟨j.val + 2, by omega⟩
        have hout := D.u0_outside d
        have huend : D.u0 d ∈ G.ends (T.edge ⟨j.val + 2, by omega⟩) := by
          have huend0 : D.u0 d ∈ G.ends (D.f0 d) := by
            rw [D.f0_ends]
            simp
          rw [← hzero] at huend0
          exact huend0
        rw [hq] at huend
        have huvertex : D.u0 d = T.vertex ⟨j.val + 3, by omega⟩ ∨
            D.u0 d = T.vertex (q.castLT (by omega)) := by
          simpa using huend
        have huin : D.u0 d ∈ TreeSequenceVertexSet T := by
          rcases huvertex with hleft | hright
          · simp [TreeSequenceVertexSet, hleft]
          · simp [TreeSequenceVertexSet, hright]
        exact hout huin)
      change phiD (T.edge ⟨j.val + 2, by omega⟩) = some (C.gamma h)
      rw [hfix, hcolor]
    · have hvrep := R.retained_vertices_before q.val hqbound (by omega)
      have hidx : (⟨q.val, hqearly⟩ : Fin (j.val + 1)).castLT (by omega) =
          (⟨q.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
      have hvrep' : R.replacementTree.vertex ((⟨q.val, hqearly⟩ : Fin (j.val + 1)).castLT
          (by omega)) =
          T.vertex ⟨q.val, by omega⟩ := by
        rw [hidx]
        exact hvrep
      rw [hvrep']
      by_cases hv : T.vertex ⟨q.val, by omega⟩ = D.v0 d
      · rw [hv]
        apply alpha_ne _ hneq
        rw [← hv, hbase]
        exact hq
      · rw [missing_fixed _ (by simp [TreeSequenceVertexSet]) hv]
        rw [hbase]
        exact hq
  · have hexit := D.v0_is_exit d
    have hbaseMem := (ScheideStructuralExitsInBase G k e0 phi T C) hexit
    obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp hbaseMem
    have haLt := a.isLt
    have hbound : a.val ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by
      omega
    have hvbase : T.vertex ⟨a.val, by omega⟩ = D.v0 d := by
      rw [C.base_vertex_position a]
      exact hva
    have hmiss : d.1 ∈ MissingColors G phiD (D.v0 d) := by
      rw [heffect.2.2.2.1]
      simp
    have hfirst : phiD (R.f1) = d.1 := by
      have hp := ScheideReplacementPairFixed G k e0 phi T C D d R R.f1
        (Or.inl (by
          change R.u1 ∈ G.ends R.f1
          rw [R.f1_ends]
          simp []))
      simpa [phiD] using hp.trans R.f1_color
    have hsecond : phiD (R.f2) = d.1 := by
      have hp := ScheideReplacementPairFixed G k e0 phi T C D d R R.f2
        (Or.inr (by
          change R.u2 ∈ G.ends R.f2
          rw [R.f2_ends]
          simp []))
      simpa [phiD] using hp.trans R.f2_color
    have hjlast : j.val = T.length - 2 ∨ j.val = T.length - 1 := by
      omega
    rcases hjlast with hjlast | hjlast
    · have haearly : a.val < j.val + 1 := by
        have hc := C.length_eq
        omega
      refine ⟨⟨a.val, haearly⟩, d.1, ?_, ?_⟩
      · rw [show R.replacementTree.edge j =
            R.replacementTree.edge ⟨T.length - 2, by rw [← hlen]; omega⟩ by
              apply congrArg R.replacementTree.edge
              apply Fin.ext
              omega]
        rw [R.replacement_last_edges.1]
        exact hfirst
      · have hvrep := R.retained_vertices_before a.val hbound (by omega)
        have hidx : (⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega) =
            (⟨a.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
        have hvrep' : R.replacementTree.vertex
            ((⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega)) =
            T.vertex ⟨a.val, by omega⟩ := by
          rw [hidx]
          exact hvrep
        rw [hvrep', hvbase]
        exact hmiss
    · have haearly : a.val < j.val + 1 := by
        have hc := C.length_eq
        omega
      refine ⟨⟨a.val, haearly⟩, d.1, ?_, ?_⟩
      · rw [show R.replacementTree.edge j =
            R.replacementTree.edge ⟨T.length - 1, by rw [← hlen]; omega⟩ by
              apply congrArg R.replacementTree.edge
              apply Fin.ext
              omega]
        rw [R.replacement_last_edges.2]
        exact hsecond
      · have hvrep := R.retained_vertices_before a.val hbound (by omega)
        have hidx : (⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega) =
            (⟨a.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
        have hvrep' : R.replacementTree.vertex
            ((⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega)) =
            T.vertex ⟨a.val, by omega⟩ := by
          rw [hidx]
          exact hvrep
        rw [hvrep', hvbase]
        exact hmiss

private theorem ScheideReplacementMaximum_branch_56.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let _ := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); (IsProperEdgeColoring G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) e0 ∧ TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) (D.f0 d) = some (C.gamma
        (D.gammaIndex d)) ∧ MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = insert (↑d : Fin k) ((MissingColors G phi
        (D.v0 d)).erase (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → ¬f = D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, ¬v = D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) → TashkinovTree G e0 phi T
        → TashkinovTree G e0 (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) R.replacementTree := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R phiD heffect htree j hj
  have hlen : R.replacementTree.length = T.length := R.replacement_length
  have hpos : 1 ≤ T.length := T.positive
  have edge_fixed : ∀ q : ℕ, ∀ hq : q < T.length,
      T.edge ⟨q, hq⟩ ≠ D.f0 d → phiD (T.edge ⟨q, hq⟩) = phi (T.edge ⟨q, hq⟩) := by
    intro q hq hne
    apply heffect.2.2.2.2.1 (T.edge ⟨q, hq⟩)
    · obtain ⟨i, hi⟩ := T.attaches ⟨q, hq⟩
      refine ⟨T.vertex ⟨q + 1, by omega⟩, ?_, ?_⟩
      · simp [TreeSequenceVertexSet]
      · change T.vertex ⟨q + 1, by omega⟩ ∈ G.ends (T.edge ⟨q, hq⟩)
        rw [hi]
        simp
    · exact hne
  have missing_fixed : ∀ v, v ∈ TreeSequenceVertexSet T → v ≠ D.v0 d →
      MissingColors G phiD v = MissingColors G phi v := heffect.2.2.2.2.2.1
  let alpha := C.gamma (D.gammaIndex d)
  have alpha_ne : ∀ c : Fin k, c ≠ alpha →
      c ∈ MissingColors G phi (D.v0 d) → c ∈ MissingColors G phiD (D.v0 d) := by
    intro c hc hm
    rw [heffect.2.2.2.1]
    have hc' : c ≠ C.gamma (D.gammaIndex d) := by
      simpa [alpha] using hc
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hc', hm⟩)
  by_cases hbefore : j.val < C.p - 1 + 2 * (D.gammaIndex d).val
  · exact @ScheideReplacementMaximum_branch_56_branch_89 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d R htree j hj hlen edge_fixed missing_fixed
      alpha_ne hbefore
  · exact @ScheideReplacementMaximum_branch_56_branch_173 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d R heffect j hj hlen hpos edge_fixed
      missing_fixed alpha_ne hbefore
theorem ScheideReplacementMaximum {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let phiD := TwoColorComponentSwap G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
    IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
      GlobalMaximumTriple G k e0 phiD R.replacementTree := by
  dsimp
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  have heffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp at heffect
  have htriple := C.globally_maximum
  have htree := htriple.2.1
  have hproper : IsProperEdgeColoring G phiD := heffect.1
  have huncolored : IsOneEdgeUncolored phiD e0 := heffect.2.1
  refine ⟨hproper, huncolored, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨htriple.1.1, htriple.1.2.1, htriple.1.2.2.1, hproper, huncolored⟩
  · exact @ScheideReplacementMaximum_branch_56 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R heffect htree
  · classical
    have vertex_card : ∀ U : TreeSequence G e0,
        (TreeSequenceVertexSet U).card = U.length + 1 := by
      intro U
      unfold TreeSequenceVertexSet
      calc
        (@Finset.image (Fin (U.length + 1)) V (Classical.decEq V)
          U.vertex Finset.univ).card = Finset.univ.card :=
          @Finset.card_image_of_injective (Fin (U.length + 1)) V U.vertex
            (Classical.decEq V) Finset.univ U.vertex_injective
        _ = U.length + 1 := by simp
    calc
      (TreeSequenceVertexSet R.replacementTree).card = R.replacementTree.length + 1 :=
        vertex_card R.replacementTree
      _ = T.length + 1 := by rw [R.replacement_length]
      _ = (TreeSequenceVertexSet T).card := (vertex_card T).symm
      _ = TashkinovOrder G := htriple.2.2

end GoldbergSeymour

end
