/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TwoColorComponentCycle
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Two Color Interchangeable Distinct Component Cycle

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorInterchangeableDistinctComponentCycle {V E : Type*}
    [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z w : Sum V E)
    (hzPath : TwoColorPathComponent G phi alpha beta z)
    (hinterchangeable : TreeInterchangeable G T phi alpha beta)
    (hzMeets : ∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta z)
    (hwMeets : ∃ v ∈ TreeSequenceVertexSet T,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta w)
    (hdistinct : TwoColorComponent G phi alpha beta z ≠
      TwoColorComponent G phi alpha beta w) :
    TwoColorComponentCycle G phi alpha beta w := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  rcases hzPath with ⟨hab, hzpoint, hzpoint_mem⟩
  have no_singleton : ∀ x ∈ TwoColorComponent G phi alpha beta w,
      ¬ Set.Subsingleton ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x) := by
    intro x hx hs
    apply hdistinct
    exact hinterchangeable z w
      ⟨hab, hzpoint, hzpoint_mem⟩
      ⟨hab, x, hx, hs⟩ hzMeets hwMeets
  obtain ⟨u, v, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper w
  have p_nontrivial : ¬ p.Nil := by
    intro hnil
    have hucomp : u ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hsupport]
      simp
    let component := (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk w
    apply no_singleton u hucomp
    intro x hx y hy
    have hxcomp : x ∈ TwoColorComponent G phi alpha beta w := by
      exact (component.mem_supp_congr_adj hx).mp (by
        exact hucomp)
    have hycomp : y ∈ TwoColorComponent G phi alpha beta w := by
      exact (component.mem_supp_congr_adj hy).mp (by
        exact hucomp)
    have hxpath : x ∈ p.support := by
      change x ∈ {x | x ∈ p.support}
      rw [hsupport]
      exact hxcomp
    have hypath : y ∈ p.support := by
      change y ∈ {x | x ∈ p.support}
      rw [hsupport]
      exact hycomp
    cases hnil
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hxpath hypath
    have hxu : x = u := hxpath
    have hyu : y = u := hypath
    exact hxu.trans hyu.symm
  cases p with
  | nil => exact False.elim (p_nontrivial (by simp))
  | cons h q =>
    have hpq : q.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      have hnodup := hp.support_nodup
      exact List.Pairwise.of_cons hnodup
    have ha_mem : u ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hsupport]
      simp
    have hnot_single : ¬ Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet u) :=
      no_singleton u ha_mem
    have exists_extra : ∃ a',
        (TwoColorIncidenceGraph G phi alpha beta).Adj u a' ∧
          a' ≠ q.getVert 0 := by
      by_contra hn
      push Not at hn
      apply hnot_single
      intro x hx y hy
      exact (hn x hx).trans (hn y hy).symm
    obtain ⟨a', ha'a, ha'a'⟩ := exists_extra
    have ha'comp : a' ∈ TwoColorComponent G phi alpha beta w := by
      let component := (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk w
      exact (component.mem_supp_congr_adj ha'a).mp (by
        exact ha_mem)
    have ha'path : a' ∈ (SimpleGraph.Walk.cons h q).support := by
      change a' ∈ {x | x ∈ (SimpleGraph.Walk.cons h q).support}
      rw [hsupport]
      exact ha'comp
    obtain ⟨i, hi_eq', hi_le⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha'path
    have hi_not_zero : i ≠ 0 := by
      intro hi0
      have : a' = u := by simpa [hi0] using hi_eq'.symm
      exact False.elim (ha'a.ne this.symm)
    by_cases hi_end : i = (SimpleGraph.Walk.cons h q).length
    · have hav : a' = v := by simpa [hi_end] using hi_eq'.symm
      have hclose : (TwoColorIncidenceGraph G phi alpha beta).Adj v u := by
        rw [← hi_eq', hi_end] at ha'a
        simpa using ha'a.symm
      refine ⟨⟨v, SimpleGraph.Walk.cons hclose (SimpleGraph.Walk.cons h q), ?_⟩, ?_⟩
      · apply (SimpleGraph.Walk.cons_isCycle_iff _ hclose).mpr
        constructor
        · exact hp
        · intro he
          have he' : s(u, v) ∈ (SimpleGraph.Walk.cons h q).edges := by
            have hsuv : s(v, u) = s(u, v) := by simp
            rw [← hsuv]
            exact he
          have hvfirst := hp.eq_snd_of_mem_edges he'
          exact ha'a' (hav.trans (by simpa [hi_end] using hvfirst))
      · intro x
        rw [← hsupport]
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq,
            or_iff_right_iff_imp]
        intro hx
        subst x
        exact Or.inr (by simp)
    · have hi_lt : i < (SimpleGraph.Walk.cons h q).length :=
        Nat.lt_of_le_of_ne hi_le hi_end
      have hleft : (TwoColorIncidenceGraph G phi alpha beta).Adj
          ((SimpleGraph.Walk.cons h q).getVert i)
          ((SimpleGraph.Walk.cons h q).getVert (i - 1)) := by
        have hh := (SimpleGraph.Walk.cons h q).adj_getVert_succ (i := i - 1) (by omega)
        simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi_not_zero)] using hh.symm
      have hright : (TwoColorIncidenceGraph G phi alpha beta).Adj
          ((SimpleGraph.Walk.cons h q).getVert i)
          ((SimpleGraph.Walk.cons h q).getVert (i + 1)) :=
        (SimpleGraph.Walk.cons h q).adj_getVert_succ hi_lt
      rw [hi_eq'] at hleft hright
      have hne_left : u ≠ (SimpleGraph.Walk.cons h q).getVert (i - 1) := by
        intro he
        have he' : (SimpleGraph.Walk.cons h q).getVert 0 =
            (SimpleGraph.Walk.cons h q).getVert (i - 1) :=
          (by simpa using he)
        have hinj := hp.getVert_injOn (by simp) (Nat.le_trans (Nat.sub_le _ _) hi_le) he'
        have hi1 : i = 1 := by omega
        exact ha'a' (by simpa [hi1] using hi_eq'.symm)
      have hne_right : u ≠ (SimpleGraph.Walk.cons h q).getVert (i + 1) := by
        intro he
        have he' : (SimpleGraph.Walk.cons h q).getVert 0 =
            (SimpleGraph.Walk.cons h q).getVert (i + 1) :=
          (by simpa using he)
        have hinj := hp.getVert_injOn (by simp) (Nat.succ_le_iff.mpr hi_lt) he'
        exact hi_not_zero (by omega)
      have hne_lr :
          (SimpleGraph.Walk.cons h q).getVert (i - 1) ≠
            (SimpleGraph.Walk.cons h q).getVert (i + 1) := by
        intro he
        have hinj := hp.getVert_injOn
          (Nat.le_trans (Nat.sub_le _ _) hi_le) (Nat.succ_le_iff.mpr hi_lt) he
        exact (Nat.ne_of_lt (by omega)) hinj
      let : Fintype ((TwoColorIncidenceGraph G phi alpha beta).neighborSet a') :=
        Fintype.ofFinite _
      have hthree : 3 ≤ Fintype.card
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet a') := by
        rw [SimpleGraph.card_neighborSet_eq_degree
          (TwoColorIncidenceGraph G phi alpha beta) a']
        let s : Finset (Sum V E) :=
          {u, (SimpleGraph.Walk.cons h q).getVert (i - 1),
            (SimpleGraph.Walk.cons h q).getVert (i + 1)}
        have hs : s ⊆ (TwoColorIncidenceGraph G phi alpha beta).neighborFinset a' := by
          intro x hx
          simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset] using ha'a.symm
          · simpa [SimpleGraph.mem_neighborFinset] using hleft
          · simpa [SimpleGraph.mem_neighborFinset] using hright
        have hc : 3 ≤ s.card := by
          have hnl := hne_left
          have hnr := hne_right
          have hnlr := hne_lr
          simp at hnl hnr hnlr
          simp [s, hnl, hnr, hnlr]
        exact le_trans hc (Finset.card_le_card hs)
      have hdegree : @SimpleGraph.degree _
          (TwoColorIncidenceGraph G phi alpha beta) a'
          (Fintype.ofFinite _) ≤ 2 := by
        simpa using TwoColorIncidenceDegreeAtMostTwo G phi alpha beta hproper a'
      rw [SimpleGraph.card_neighborSet_eq_degree
        (TwoColorIncidenceGraph G phi alpha beta) a'] at hthree
      omega

end GoldbergSeymour

end
