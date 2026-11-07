/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreMissingColors
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Incident Core Tree Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreTreeTransport {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) :
    (∀ (e0 : E) (k : ℕ) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0),
      ∃ Tc : TreeSequence (IncidentCore G) e0,
        ∃ hlen : Tc.length = T.length,
          (∀ i : Fin (Tc.length + 1),
            (Tc.vertex i).1 = T.vertex (Fin.cast
              (congrArg (fun n => n + 1) hlen) i)) ∧
          (∀ j : Fin Tc.length,
            Tc.edge j = T.edge (Fin.cast hlen j)) ∧
          (TreeSequenceVertexSet Tc).card = (TreeSequenceVertexSet T).card ∧
          (TashkinovTree (IncidentCore G) e0 phi Tc ↔
            TashkinovTree G e0 phi T)) ∧
    (∀ (e0 : E) (k : ℕ) (phi : PartialEdgeColoring E k)
      (Tc : TreeSequence (IncidentCore G) e0),
      ∃ T : TreeSequence G e0,
        ∃ hlen : T.length = Tc.length,
          (∀ i : Fin (T.length + 1),
            T.vertex i = (Tc.vertex (Fin.cast
              (congrArg (fun n => n + 1) hlen) i)).1) ∧
          (∀ j : Fin T.length,
            T.edge j = Tc.edge (Fin.cast hlen j)) ∧
          (TreeSequenceVertexSet Tc).card = (TreeSequenceVertexSet T).card ∧
          (TashkinovTree G e0 phi T ↔
            TashkinovTree (IncidentCore G) e0 phi Tc)) := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · intro e0 k phi T
    have incidentAt : ∀ i : Fin (T.length + 1),
        ∃ e : E, Incident G (T.vertex i) e := by
      intro i
      refine Fin.cases ?_ (fun q => ?_) i
      · refine ⟨T.edge ⟨0, T.positive⟩, ?_⟩
        change T.vertex ⟨0, _⟩ ∈ G.ends (T.edge ⟨0, T.positive⟩)
        obtain ⟨h, hends⟩ := T.attaches ⟨0, T.positive⟩
        rw [hends]
        simp [Fin.castLT]
      · refine ⟨T.edge q, ?_⟩
        change T.vertex q.succ ∈ G.ends (T.edge q)
        obtain ⟨h, hends⟩ := T.attaches q
        rw [hends]
        exact Sym2.mem_mk_left _ _
    let witness : ∀ i : Fin (T.length + 1),
        {e : E // Incident G (T.vertex i) e} :=
      fun i => ⟨Classical.choose (incidentAt i), Classical.choose_spec (incidentAt i)⟩
    let lifted : Fin (T.length + 1) → IncidentVertex G :=
      fun i => ⟨T.vertex i, ⟨(witness i).val, (witness i).property⟩⟩
    have lifted_coe : ∀ i, (lifted i).1 = T.vertex i := by
      intro i
      rfl
    have lifted_injective : Function.Injective lifted := by
      intro i j h
      apply T.vertex_injective
      exact congrArg Subtype.val h
    let Tc : TreeSequence (IncidentCore G) e0 :=
      { length := T.length
        positive := T.positive
        vertex := lifted
        edge := T.edge
        vertex_injective := lifted_injective
        edge_injective := T.edge_injective
        first_edge := T.first_edge
        attaches := by
          intro j
          obtain ⟨i, hi⟩ := T.attaches j
          refine ⟨i, ?_⟩
          apply (Sym2.map.injective (f := fun x : IncidentVertex G => x.1)
            Subtype.coe_injective)
          rw [IncidentCoreEndpoints G (T.edge j)]
          simpa only [Sym2.map_mk, lifted_coe] using hi }
    refine ⟨Tc, rfl, ?_, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro j
      rfl
    · simp [Tc, TreeSequenceVertexSet,
        Finset.card_image_of_injective Finset.univ lifted_injective,
        Finset.card_image_of_injective Finset.univ T.vertex_injective]
    · unfold TashkinovTree
      constructor
      · intro h j hj
        obtain ⟨i, c, hc, hm⟩ := h j hj
        let ii : Fin (T.length + 1) :=
          Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
        refine ⟨i, c, hc, ?_⟩
        have colorTransport := IncidentCoreMissingColors G k phi (Tc.vertex ii)
        have bridge : c ∈ MissingColors G phi
            (Tc.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))).1 := by
          rw [← colorTransport.2]
          exact hm
        simpa [Tc, lifted, ii] using bridge
      · intro h j hj
        obtain ⟨i, c, hc, hm⟩ := h j hj
        let ii : Fin (T.length + 1) :=
          Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
        refine ⟨i, c, hc, ?_⟩
        have colorTransport := IncidentCoreMissingColors G k phi (Tc.vertex ii)
        have bridge : c ∈ MissingColors (IncidentCore G) phi
            (Tc.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))) := by
          rw [colorTransport.2]
          exact hm
        simpa [Tc, lifted, ii] using bridge
  · intro e0 k phi Tc
    let T : TreeSequence G e0 :=
      { length := Tc.length
        positive := Tc.positive
        vertex := fun i => (Tc.vertex i).1
        edge := Tc.edge
        vertex_injective := by
          intro i j h
          apply Tc.vertex_injective
          exact Subtype.ext h
        edge_injective := Tc.edge_injective
        first_edge := Tc.first_edge
        attaches := by
          intro j
          obtain ⟨i, hi⟩ := Tc.attaches j
          refine ⟨i, ?_⟩
          have hm := congrArg (Sym2.map (fun x : IncidentVertex G => x.1)) hi
          simpa [IncidentCoreEndpoints] using hm }
    refine ⟨T, rfl, ?_, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro j
      rfl
    · simp only [TreeSequenceVertexSet, T]
      rw [Finset.card_image_of_injective _ Tc.vertex_injective]
      have underlying_injective : Function.Injective (fun i => (Tc.vertex i).1) := by
        intro i j h
        apply Tc.vertex_injective
        exact Subtype.ext h
      rw [Finset.card_image_of_injective _ underlying_injective]
    · unfold TashkinovTree
      constructor
      · intro h j hj
        obtain ⟨i, c, hc, hm⟩ := h j hj
        let ii : Fin (Tc.length + 1) :=
          Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
        refine ⟨i, c, hc, ?_⟩
        have colorTransport := IncidentCoreMissingColors G k phi (Tc.vertex ii)
        have bridge : c ∈ MissingColors (IncidentCore G) phi
            (Tc.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))) := by
          rw [colorTransport.2]
          exact hm
        simpa [T, ii] using bridge
      · intro h j hj
        obtain ⟨i, c, hc, hm⟩ := h j hj
        let ii : Fin (Tc.length + 1) :=
          Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
        refine ⟨i, c, hc, ?_⟩
        have colorTransport := IncidentCoreMissingColors G k phi (Tc.vertex ii)
        have bridge : c ∈ MissingColors G phi
            (Tc.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))).1 := by
          rw [← colorTransport.2]
          exact hm
        simpa [T, ii] using bridge

end GoldbergSeymour

end
