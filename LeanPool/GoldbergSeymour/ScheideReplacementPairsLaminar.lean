/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementInternalMissing

/-!
# Scheide Replacement Pairs Laminar

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideReplacementPairsLaminar {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ∀ d d',
    ({(R d).u1, (R d).u2} : Finset V) = ({(R d').u1, (R d').u2} : Finset V) ∨
      Disjoint ({(R d).u1, (R d).u2} : Finset V) ({(R d').u1, (R d').u2} : Finset V) := by
  intro d d'
  let y₀ : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have y₀_mem : y₀ ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨⟨0, by omega⟩, ?_⟩
    simpa using (C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)
  have y₀_ne_block : ∀ q j,
      y₀ ≠ C.blockVertex (D.gammaIndex q) j := by
    intro q j h
    change C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ =
      C.blockVertex (D.gammaIndex q) j at h
    have hv : T.vertex ⟨0, by omega⟩ =
        T.vertex ⟨C.p + 2 * (D.gammaIndex q).val + j.val, by
        have hp := C.p_ge_two
        have hc := C.length_eq
        have hq := (D.gammaIndex q).isLt
        have hj := j.isLt
        omega⟩ := by
      calc
        T.vertex ⟨0, by omega⟩ = C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ :=
          (C.base_vertex_position
            ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)
        _ = C.blockVertex (D.gammaIndex q) j := h
        _ = T.vertex ⟨C.p + 2 * (D.gammaIndex q).val + j.val, by
          have hp := C.p_ge_two
          have hc := C.length_eq
          have hq := (D.gammaIndex q).isLt
          have hj := j.isLt
          omega⟩ := (C.block_vertex_position _ _).symm
    have hind := T.vertex_injective hv
    have hnum := congrArg Fin.val hind
    have hzero : (0 : ℕ) = C.p + 2 * (D.gammaIndex q).val + j.val := hnum
    have hp := C.p_ge_two
    omega
  have y₀_remainder : ∀ q, y₀ ∈ TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex q) 0, C.blockVertex (D.gammaIndex q) 1} := by
    intro q
    exact Finset.mem_sdiff.mpr ⟨y₀_mem, by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact y₀_ne_block q 0 h
      · exact y₀_ne_block q 1 h⟩
  have internal : ∀ q : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ∃ f : E,
      phi f = some D.alpha0 ∧ G.ends f = s((R q).u1, (R q).u2) := by
    intro q
    apply ScheideReplacementInternalMissing G k e0 phi T C D q (R q)
      D.alpha0
    · exact D.alpha0_not_block (D.gammaIndex q)
    · exact ⟨y₀, y₀_remainder q, D.alpha0_missing_at_y0⟩
  have proper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  by_cases overlap : Disjoint ({(R d).u1, (R d).u2} : Finset V)
      ({(R d').u1, (R d').u2} : Finset V)
  · exact Or.inr overlap
  · left
    have common : ∃ v : V, v ∈ ({(R d).u1, (R d).u2} : Finset V) ∧
        v ∈ ({(R d').u1, (R d').u2} : Finset V) := by
      by_contra no_common
      apply overlap
      exact Finset.disjoint_left.mpr (by
        intro v hv hv'
        exact no_common ⟨v, hv, hv'⟩)
    obtain ⟨v, hv, hv'⟩ := common
    obtain ⟨f, hfcolor, hfends⟩ := internal d
    obtain ⟨f', hf'color, hf'ends⟩ := internal d'
    have hinc : Incident G v f := by
      change v ∈ G.ends f
      rw [hfends]
      apply Sym2.mem_iff.mpr
      simpa using hv
    have hinc' : Incident G v f' := by
      change v ∈ G.ends f'
      rw [hf'ends]
      apply Sym2.mem_iff.mpr
      simpa using hv'
    have hedge : f = f' := by
      by_contra hne
      have hbad := proper hne ⟨v, hinc, hinc'⟩ hfcolor
      exact hbad hf'color
    have hpair : s((R d).u1, (R d).u2) =
        s((R d').u1, (R d').u2) := by
      rw [← hfends, hedge, hf'ends]
    rcases Sym2.eq_iff.mp hpair with h | h
    · simp [h.1, h.2]
    · rw [h.1, h.2]
      exact Finset.pair_comm _ _

end GoldbergSeymour

end
