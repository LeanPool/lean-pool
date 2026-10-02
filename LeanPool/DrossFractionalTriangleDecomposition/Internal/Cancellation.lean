/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CancellationConfigs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cancellation of off-root K₄ transfers

The two configurations obtained by swapping transfer edges have opposite flow.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The off-root transfer terms cancel in pairs. -/
public theorem hkey_cancel (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
        if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0) = 0 := by
  classical
  let Cfg := cancellationConfigs G e
  have hflat :
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
          if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0) =
      ∑ p ∈ Cfg, F.f (Ghat.edge p.2.1) (Ghat.edge p.2.2) := by
    rw [show Cfg = cancellationConfigs G e from rfl, cancellationConfigs,
      Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_product]
    by_cases het : e ∈ triEdges t
    · rw [ite_eq_left het]
      rw [show (∑ e'' : Sym2 V, ∑ e' : Sym2 V,
            if e ∈ triEdges t ∧ e'' ∈ (triEdges t).erase e ∧ K4pair G e'' e' ∧
                (∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'') then
              F.f (Ghat.edge e'') (Ghat.edge e') else 0) =
          ∑ e'' : Sym2 V, if e'' ∈ (triEdges t).erase e then
              (∑ e' : Sym2 V, if K4pair G e'' e' ∧
                  (∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'') then
                F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0 from ?_]
      · rw [Finset.sum_ite_mem, Finset.univ_inter]
      · refine Finset.sum_congr rfl fun e'' _ => ?_
        by_cases hee : e'' ∈ (triEdges t).erase e
        · rw [ite_eq_left hee]
          refine Finset.sum_congr rfl fun e' _ => ?_
          exact if_congr ⟨fun h => h.2.2, fun h => ⟨het, hee, h⟩⟩ rfl rfl
        · rw [ite_eq_right hee]
          refine Finset.sum_eq_zero fun e' _ => ?_
          exact ite_eq_right fun h => hee h.2.1
    · rw [ite_eq_right het]
      refine (Finset.sum_eq_zero fun e'' _ => Finset.sum_eq_zero fun e' _ => ?_).symm
      exact ite_eq_right fun h => het h.1
  rw [hflat]
  refine Finset.sum_involution
    (fun p _ => ((e.toFinset ∪ p.2.2.toFinset, p.2.2, p.2.1) :
      Finset V × Sym2 V × Sym2 V)) ?_ ?_ ?_ ?_
  · intro p _
    change F.f (Ghat.edge p.2.1) (Ghat.edge p.2.2) +
      F.f (Ghat.edge p.2.2) (Ghat.edge p.2.1) = 0
    rw [F.skew (Ghat.edge p.2.1) (Ghat.edge p.2.2)]
    ring
  · intro p _ hfp
    have hne : p.2.1 ≠ p.2.2 := by
      intro h
      apply hfp
      rw [h]
      have hs := F.skew (Ghat.edge p.2.2) (Ghat.edge p.2.2)
      linarith
    intro hcontra
    rw [Prod.ext_iff, Prod.ext_iff] at hcontra
    exact hne hcontra.2.1.symm
  · intro p hp
    exact cancellationConfigs_swap_mem G e p hp
  · intro p hp
    have hp' := hp
    simp only [Cfg, cancellationConfigs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true] at hp'
    obtain ⟨htc, hetri, herase, _hk, _hap⟩ := hp'
    have hkey := tri_eq_edge_union G htc hetri herase
    apply Prod.ext
    · exact hkey
    · rfl

end LeanPool.DrossFractionalTriangleDecomposition
