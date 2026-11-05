/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Scheide Replacement Used Witness

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev ScheideReplacementUsedWitnessWitness127Conditions.{u_1, u_2} : Prop :=
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (d : ↥(DefectiveColors G phi
        (TreeSequenceVertexSet T))) (c0 : Fin k), (
    ∃ (j : Fin (R d).replacementTree.length), 1 ≤ (↑j : ℕ) ∧ TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) ((R d).replacementTree.edge j) = some
        c0) →
    let _ := C.p - 1 + 2 * (↑(D.gammaIndex d) : ℕ);
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); (
    have phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)); IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧ phiD (D.f0 d) = some
        (C.gamma (D.gammaIndex d)) ∧ MissingColors G phiD (D.v0 d) = insert (↑d : Fin k)
        ((MissingColors G phi (D.v0 d)).erase (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → f ≠ D.f0 d → phiD f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d → MissingColors G phiD v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G phiD v = MissingColors G phi v) → (
    ∀ (n : Fin T.length), 1 ≤ (↑n : ℕ) →
    ∃ (i : Fin ((↑n : ℕ) + 1)) (a : Fin k), phi (T.edge n) = some a ∧ a ∈ MissingColors G phi
        (T.vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ n.isLt))))) → (
    ∀ (n : Fin T.length), 1 ≤ (↑n : ℕ) → phiD (T.edge n) = phi (T.edge n)) → phiD (R d).f1 = some
        (↑d : Fin k) → phiD (R d).f2 = some (↑d : Fin k) → (
    ∀ (a : Fin C.p), C.y a ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}) → D.v0 d ∈
        TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} →
    ∀ c ∈ TreeUsedColors phiD (R d).replacementTree,
    ∃ z ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}, c ∈ MissingColors G
        phiD z

private theorem ScheideReplacementUsedWitness_witness_127.{u_1, u_2} :
    ScheideReplacementUsedWitnessWitness127Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R d c0 hc0 q phiD effect oldWitness originalFixed f1Fixed
      f2Fixed hbaseZ hv0Z c hc
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨j, hj, hjc⟩
  by_cases hbase : j.val < C.p - 1
  · let n : Fin T.length := ⟨j.val, by rw [← (R d).replacement_length]; exact j.isLt⟩
    have hlen := (R d).replacement_length
    have he : (R d).replacementTree.edge j = T.edge n := by
      calc
        (R d).replacementTree.edge j =
            (R d).replacementTree.edge ⟨j.val, by omega⟩ := by
          congr 1
        _ = T.edge n := (R d).retained_edges_before j.val (by omega) n.isLt
    obtain ⟨i, a, ha, hm⟩ := oldWitness n hj
    have hrep : phiD ((R d).replacementTree.edge j) = some a := by
      rw [he, originalFixed n hj]
      exact ha
    have hc' : a = c := Option.some.inj (hrep.symm.trans hjc)
    have hp := C.p_ge_two
    have hi := i.isLt
    have hn := n.isLt
    have hji : i.val ≤ n.val := Nat.le_of_lt_succ i.isLt
    have hjp : j.val + 1 < C.p := by omega
    have hnj : n.val = j.val := rfl
    let b : Fin C.p := ⟨i.val, by omega⟩
    have hv : T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ n.isLt))) = C.y b := by
      have hi : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ n.isLt)) =
          ⟨i.val, by omega⟩ := Fin.ext rfl
      rw [hi]
      exact C.base_vertex_position b
    have hne : c ≠ C.gamma (D.gammaIndex d) := by
      intro hcg
      let bi : Fin (C.p - 1) := ⟨j.val, by omega⟩
      have oldc : phi (C.baseEdge bi) = some c := by
        rw [← C.base_edge_position bi]
        simpa [hc'] using ha
      have hb := C.initial_nonfirst_avoids_blocks bi hj c oldc
        (D.gammaIndex d)
      exact hb hcg
    refine ⟨C.y b, hbaseZ b, ?_⟩
    by_cases hz : C.y b = D.v0 d
    · rw [hz, effect.2.2.2.1]
      have hm' : c ∈ MissingColors G phi (C.y b) := by simpa [hv, hc'] using hm
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, by simpa [hz] using hm'⟩)
    · have hbX : C.y b ∈ TreeSequenceVertexSet T :=
        (Finset.mem_sdiff.mp (hbaseZ b)).1
      rw [effect.2.2.2.2.2.1 (C.y b) hbX hz]
      simpa [hv, hc'] using hm
  · by_cases hbefore : j.val < q
    · let n := j.val - (C.p - 1)
      have hp := C.p_ge_two
      have hs := C.length_eq
      have hlen := (R d).replacement_length
      have hjlt := j.isLt
      let r : Fin C.s := ⟨n / 2, by omega⟩
      let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
      have hpos : j.val = C.p - 1 + 2 * r.val + t.val := by
        dsimp [r, t, n]
        omega
      have hr : r ≠ D.gammaIndex d := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [r, n] at hv
        omega
      have he : (R d).replacementTree.edge j = T.edge ⟨j.val, by omega⟩ :=
        (R d).retained_edges_before j.val hbefore (by omega)
      have hold : T.edge ⟨j.val, by omega⟩ = C.blockEdge r t := by
        calc
          T.edge ⟨j.val, by omega⟩ =
              T.edge ⟨C.p - 1 + 2 * r.val + t.val, by omega⟩ := by
            congr 1
            exact Fin.ext hpos
          _ = C.blockEdge r t := C.block_edge_position r t
      have hrep : phiD ((R d).replacementTree.edge j) = some (C.gamma r) := by
        rw [he, originalFixed ⟨j.val, by omega⟩ (by omega), hold, C.block_color]
      have hcol : C.gamma r = c := Option.some.inj (hrep.symm.trans hjc)
      obtain ⟨b, hb⟩ := C.block_color_missing_on_base r
      have hne : c ≠ C.gamma (D.gammaIndex d) := by
        intro h
        apply hr
        apply C.gamma_injective
        simpa [hcol] using h
      refine ⟨C.y b, hbaseZ b, ?_⟩
      by_cases hz : C.y b = D.v0 d
      · rw [hz, effect.2.2.2.1]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, by simpa [hz, hcol] using hb⟩)
      · have htree : C.y b ∈ TreeSequenceVertexSet T :=
          (Finset.mem_sdiff.mp (hbaseZ b)).1
        rw [effect.2.2.2.2.2.1 (C.y b) htree hz]
        simpa [hcol] using hb
    · by_cases hafter : j.val + 2 < T.length
      · let n := j.val + 2 - (C.p - 1)
        have hlen := (R d).replacement_length
        have hstruct := C.length_eq
        let r : Fin C.s := ⟨n / 2, by omega⟩
        let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
        have hpos : j.val + 2 = C.p - 1 + 2 * r.val + t.val := by
          dsimp [r, t, n]
          omega
        have hr : r ≠ D.gammaIndex d := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [r, n] at hv
          omega
        have he := (R d).retained_edges_after j.val (by omega) hafter
        have hold : T.edge ⟨j.val + 2, hafter⟩ = C.blockEdge r t := by
          calc
            T.edge ⟨j.val + 2, hafter⟩ =
                T.edge ⟨C.p - 1 + 2 * r.val + t.val, by omega⟩ := by
              congr 1
              exact Fin.ext hpos
            _ = C.blockEdge r t := C.block_edge_position r t
        have hrep : phiD ((R d).replacementTree.edge j) = some (C.gamma r) := by
          have hposj : 1 ≤ j.val + 2 := by omega
          rw [he, originalFixed (⟨j.val + 2, hafter⟩ : Fin T.length) hposj, hold,
            C.block_color]
        have hcol : C.gamma r = c := Option.some.inj (hrep.symm.trans hjc)
        obtain ⟨b, hb⟩ := C.block_color_missing_on_base r
        have hne : c ≠ C.gamma (D.gammaIndex d) := by
          intro h
          apply hr
          apply C.gamma_injective
          simpa [hcol] using h
        refine ⟨C.y b, hbaseZ b, ?_⟩
        by_cases hz : C.y b = D.v0 d
        · rw [hz, effect.2.2.2.1]
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, by simpa [hz, hcol] using hb⟩)
        · have htree : C.y b ∈ TreeSequenceVertexSet T :=
            (Finset.mem_sdiff.mp (hbaseZ b)).1
          rw [effect.2.2.2.2.2.1 (C.y b) htree hz]
          simpa [hcol] using hb
      · have hlen := (R d).replacement_length
        have hjlast : j.val = T.length - 2 ∨ j.val = T.length - 1 := by omega
        rcases hjlast with hlast | hlast
        · have he : (R d).replacementTree.edge j = (R d).f1 := by
            calc
              (R d).replacementTree.edge j =
                  (R d).replacementTree.edge ⟨T.length - 2, by
                    rw [(R d).replacement_length]
                    omega⟩ := by
                congr 1
                exact Fin.ext hlast
              _ = (R d).f1 := (R d).replacement_last_edges.1
          refine ⟨D.v0 d, hv0Z, ?_⟩
          have hc' : c = d.1 := Option.some.inj (hjc.symm.trans (he ▸ f1Fixed))
          rw [hc', effect.2.2.2.1]
          exact Finset.mem_insert_self _ _
        · have he : (R d).replacementTree.edge j = (R d).f2 := by
            calc
              (R d).replacementTree.edge j =
                  (R d).replacementTree.edge ⟨T.length - 1, by
                    rw [(R d).replacement_length]
                    omega⟩ := by
                congr 1
                exact Fin.ext hlast
              _ = (R d).f2 := (R d).replacement_last_edges.2
          refine ⟨D.v0 d, hv0Z, ?_⟩
          have hc' : c = d.1 := Option.some.inj (hjc.symm.trans (he ▸ f2Fixed))
          rw [hc', effect.2.2.2.1]
          exact Finset.mem_insert_self _ _

theorem ScheideReplacementUsedWitness {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}) :
    ∀
      c ∈
        TreeUsedColors
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d)))
          (R d).replacementTree,
    ∃
      z ∈
        TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1},
    c ∈
      MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))) z := by
  classical
  intro c0 hc0
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc0
  let q := C.p - 1 + 2 * (D.gammaIndex d).val
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  have effect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  have global := C.globally_maximum
  have tash : TashkinovTree G e0 phi T := global.2.1
  have oldWitness : ∀ n : Fin T.length, 1 ≤ n.val →
      ∃ i : Fin (n.val + 1), ∃ a : Fin k,
        phi (T.edge n) = some a ∧
          a ∈ MissingColors G phi
            (T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ n.isLt)))) := by
    intro n hn
    exact tash n hn
  have originalFixed : ∀ n : Fin T.length, 1 ≤ n.val →
      phiD (T.edge n) = phi (T.edge n) := by
    intro n hnpos
    apply effect.2.2.2.2.1
    · obtain ⟨i, hi⟩ := T.attaches n
      refine ⟨T.vertex ⟨n + 1, by omega⟩, ?_, ?_⟩
      · simp [TreeSequenceVertexSet]
      · change T.vertex n.succ ∈ G.ends (T.edge n)
        rw [hi]
        simp
    · intro heq
      have unused := (ScheideGlobalMaximumUnused G k e0 phi T global).1
      apply (Finset.disjoint_left.mp unused) d.2
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨n, hnpos, ?_⟩
      simpa [heq] using D.f0_color d
  have f1Fixed : phiD (R d).f1 = some d.1 := by
    have hf := effect.2.2.2.2.1 (R d).f1
      ⟨(R d).v1, (Finset.mem_sdiff.mp (R d).v1_in_remainder).1, by
        change (R d).v1 ∈ G.ends ((R d).f1)
        rw [(R d).f1_ends]
        simp []⟩
      (R d).f0_ne_f1.symm
    simpa [phiD] using hf.trans (R d).f1_color
  have f2Fixed : phiD (R d).f2 = some d.1 := by
    have hf := effect.2.2.2.2.1 (R d).f2
      ⟨(R d).v2, (Finset.mem_sdiff.mp (R d).v2_in_remainder).1, by
        change (R d).v2 ∈ G.ends ((R d).f2)
        rw [(R d).f2_ends]
        simp []⟩
      (R d).f0_ne_f2.symm
    simpa [phiD] using hf.trans (R d).f2_color
  have hbaseZ : ∀ a : Fin C.p, C.y a ∈
      TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1} := by
    intro a
    have haX : C.y a ∈ TreeSequenceVertexSet T := by
      rw [← C.base_vertex_position a]
      simp [TreeSequenceVertexSet]
    refine Finset.mem_sdiff.mpr ⟨haX, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro heq
    rcases heq with heq | heq
    · have hi := T.vertex_injective (C.base_vertex_position a |>.trans
        (heq ▸ (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2))).symm)
      have hv := congrArg Fin.val hi
      have hp := C.p_ge_two
      have hr := (D.gammaIndex d).isLt
      simp at hv
      omega
    · have hi := T.vertex_injective (C.base_vertex_position a |>.trans
        (heq ▸ (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2))).symm)
      have hv := congrArg Fin.val hi
      have hp := C.p_ge_two
      have hr := (D.gammaIndex d).isLt
      simp at hv
      omega
  have hv0Z : D.v0 d ∈ TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1} := by
    have hb := ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d)
    obtain ⟨b, hbv, hvb⟩ := Finset.mem_image.mp hb
    have hby : D.v0 d = C.y b := hvb.symm
    simpa [hby] using hbaseZ b
  have witness : ∀ c : Fin k, c ∈ TreeUsedColors phiD (R d).replacementTree →
      ∃ z ∈ TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}, c ∈ MissingColors G phiD z := by
    exact @ScheideReplacementUsedWitness_witness_127 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 phi T C D R d c0 hc0 effect oldWitness originalFixed
        f1Fixed f2Fixed hbaseZ hv0Z
  have hc0' : c0 ∈ TreeUsedColors phiD (R d).replacementTree := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc0
  simpa [phiD] using witness c0 hc0'

end GoldbergSeymour

end
