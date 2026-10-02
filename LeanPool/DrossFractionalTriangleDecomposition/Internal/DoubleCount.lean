/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.FlowSaturation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Double counting rooted K₄ transfers

A K₄ partner has exactly two possible triangle apices over a fixed root edge.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rooted K₄ pair contributes exactly two triangles over its first edge. -/
public lemma two_apex_count (G : SimpleGraph V) [DecidableRel G.Adj] (e e' : Sym2 V) :
    ((G.cliqueFinset 3).filter (fun t =>
      K4pair G e e' ∧ e ∈ triEdges t ∧
        ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e)).card =
      if K4pair G e e' then 2 else 0 := by
  induction e using Sym2.inductionOn with | _ a b =>
  induction e' using Sym2.inductionOn with | _ x y =>
  by_cases hk : K4pair G (s(a,b)) (s(x,y))
  · have hcl := (k4pair_iff_clique G a b x y).mp hk
    have hd := card4_pairwise hcl.card_eq
    rw [ite_eq_left hk]
    have heq :
        (G.cliqueFinset 3).filter (fun t =>
          K4pair G (s(a,b)) (s(x,y)) ∧ s(a,b) ∈ triEdges t ∧
            ∃ v, v ∈ t ∧ v ∈ s(x,y) ∧ v ∉ s(a,b)) =
          {{a,b,x}, {a,b,y}} := by
      ext t
      simp only [Finset.mem_filter, hk, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hedge, v, hvt, hvxy, hvab⟩
        have habt : a ∈ t ∧ b ∈ t := by
          exact (show (a ∈ t ∧ b ∈ t) ∧ ¬s(a,b).IsDiag from
            (by simpa only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff] using hedge)).1
        have hv : v = x ∨ v = y := by simpa only [Sym2.mem_iff] using hvxy
        rcases hv with hv | hv
        · subst v
          left
          symm
          apply Finset.eq_of_subset_of_card_le
          · exact fun z hz => by
              rcases (show z = a ∨ z = b ∨ z = x by simpa using hz) with hza | hzb | hzx
              · simpa [hza] using habt.1
              · simpa [hzb] using habt.2
              · simpa [hzx] using hvt
          · rw [((SimpleGraph.mem_cliqueFinset_iff).mp ht).card_eq]
            simp [hd.1, hd.2.1, hd.2.2.2.1]
        · subst v
          right
          symm
          apply Finset.eq_of_subset_of_card_le
          · exact fun z hz => by
              rcases (show z = a ∨ z = b ∨ z = y by simpa using hz) with hza | hzb | hzy
              · simpa [hza] using habt.1
              · simpa [hzb] using habt.2
              · simpa [hzy] using hvt
          · rw [((SimpleGraph.mem_cliqueFinset_iff).mp ht).card_eq]
            simp [hd.1, hd.2.2.1, hd.2.2.2.2.1]
      · intro ht
        rcases ht with rfl | rfl
        · refine ⟨?_, ?_, x, by simp, by simp, ?_⟩
          · rw [SimpleGraph.mem_cliqueFinset_iff]
            apply is3Clique_iff.mpr
            exact ⟨a, b, x,
              hcl.1 (by simp) (by simp) hd.1,
              hcl.1 (by simp) (by simp) hd.2.1,
              hcl.1 (by simp) (by simp) hd.2.2.2.1, rfl⟩
          · simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
            exact ⟨⟨by simp, by simp⟩, by simpa [Sym2.mk_isDiag_iff] using hd.1⟩
          · simpa only [Sym2.mem_iff, not_or] using ⟨hd.2.1.symm, hd.2.2.2.1.symm⟩
        · refine ⟨?_, ?_, y, by simp, by simp, ?_⟩
          · rw [SimpleGraph.mem_cliqueFinset_iff]
            apply is3Clique_iff.mpr
            exact ⟨a, b, y,
              hcl.1 (by simp) (by simp) hd.1,
              hcl.1 (by simp) (by simp) hd.2.2.1,
              hcl.1 (by simp) (by simp) hd.2.2.2.2.1, rfl⟩
          · simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
            exact ⟨⟨by simp, by simp⟩, by simpa [Sym2.mk_isDiag_iff] using hd.1⟩
          · simpa only [Sym2.mem_iff, not_or] using ⟨hd.2.2.1.symm, hd.2.2.2.2.1.symm⟩
    rw [heq]
    rw [Finset.card_pair]
    have hne : ({a,b,x} : Finset V) ≠ {a,b,y} := by
      intro hxy
      have hy : y ∈ ({a,b,x} : Finset V) := hxy ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hya | hyb | hyx
      · exact hd.2.2.1 hya.symm
      · exact hd.2.2.2.2.1 hyb.symm
      · exact hd.2.2.2.2.2 hyx.symm
    exact hne
  · rw [ite_eq_right hk]
    simp [hk]

/-- K₄-ineligible arcs have zero flow, by zero capacity in both directions. -/
public lemma flow_zero_off_k4pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ))
    (x y : Sym2 V) (hxy : ¬ K4pair G x y) :
    F.f (Ghat.edge x) (Ghat.edge y) = 0 := by
  have hle : F.f (Ghat.edge x) (Ghat.edge y) ≤ 0 := by
    have h := F.capacitated (Ghat.edge x) (Ghat.edge y)
    simp only [drossNet, dcap, ite_eq_right hxy] at h
    exact h
  have hge : F.f (Ghat.edge y) (Ghat.edge x) ≤ 0 := by
    have h := F.capacitated (Ghat.edge y) (Ghat.edge x)
    simp only [drossNet, dcap,
      ite_eq_right (fun hp => hxy ((k4pair_symm G y x).mp hp))] at h
    exact h
  have hsk := F.skew (Ghat.edge x) (Ghat.edge y)
  linarith

/-- Summing over triangles through `e`, each K₄-partner contributes twice. -/
public theorem hkey_double (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0) =
      2 * ∑ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') := by
  have hswap :
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (∑ e' : Sym2 V, if K4pair G e e' ∧
          ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0) =
      ∑ e' : Sym2 V, ∑ t ∈ G.cliqueFinset 3,
        if K4pair G e e' ∧ e ∈ triEdges t ∧
          ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0 := by
    calc
      _ = ∑ t ∈ G.cliqueFinset 3, ∑ e' : Sym2 V,
          if K4pair G e e' ∧ e ∈ triEdges t ∧
            ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
              F.f (Ghat.edge e) (Ghat.edge e') else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            by_cases het : e ∈ triEdges t <;> simp [het]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' _
  by_cases hk : K4pair G e e'
  · have hc := two_apex_count G e e'
    rw [ite_eq_left hk] at hc
    rw [← Finset.sum_filter, Finset.sum_const, hc, nsmul_eq_mul]
    norm_num
  · have hf := flow_zero_off_k4pair G wΔ F e e' hk
    simp [hk, hf]

public lemma tri_eq_edge_union (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    {e e2 : Sym2 V} (htc : t ∈ G.cliqueFinset 3) (het : e ∈ triEdges t)
    (he2 : e2 ∈ (triEdges t).erase e) : e.toFinset ∪ e2.toFinset = t := by
  have ht3 : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htc).card_eq
  have hsube : e.toFinset ⊆ t := fun z hz =>
    (Finset.mem_sym2_iff.mp (by rw [triEdges, Finset.mem_filter] at het; exact het.1)) z
      (Sym2.mem_toFinset.mp hz)
  have hsub2 : e2.toFinset ⊆ t := fun z hz =>
    (Finset.mem_sym2_iff.mp (by
      have hmem := (Finset.mem_erase.mp he2).2
      rw [triEdges, Finset.mem_filter] at hmem
      exact hmem.1)) z
      (Sym2.mem_toFinset.mp hz)
  have hsub : e.toFinset ∪ e2.toFinset ⊆ t := Finset.union_subset hsube hsub2
  have hne : e ≠ e2 := (Finset.mem_erase.mp he2).1.symm
  have hec : e.toFinset.card = 2 := by
    induction e using Sym2.inductionOn with | _ a b =>
      rw [triEdges, Finset.mem_filter, Sym2.mk_isDiag_iff] at het
      rw [Sym2.toFinset_mk_eq]; simp [Sym2.mk_isDiag_iff.not.mp (by simpa using het.2)]
  have hpc : e2.toFinset.card = 2 := by
    induction h : e2 using Sym2.inductionOn with | _ a b =>
      have hd : a ≠ b := by
        have hmem := (Finset.mem_erase.mp he2).2
        rw [triEdges, Finset.mem_filter, h] at hmem
        simpa [Sym2.mk_isDiag_iff] using hmem.2
      simp [Sym2.toFinset_mk_eq, hd]
  have hcard3 : (e.toFinset ∪ e2.toFinset).card = 3 := by
    have hle : (e.toFinset ∪ e2.toFinset).card ≤ 3 := (Finset.card_le_card hsub).trans_eq ht3
    have hinter : (e.toFinset ∩ e2.toFinset).card ≤ 1 := by
      by_contra hh
      push Not at hh
      have heq : e.toFinset = e2.toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          have hii : e.toFinset ∩ e2.toFinset = e.toFinset :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          rw [← hii] at hz; exact (Finset.mem_inter.mp hz).2
        · omega
      exact hne (Sym2.ext fun z => by simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp heq z)
    have hun := Finset.card_union_add_card_inter e.toFinset e2.toFinset
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [ht3, hcard3])

end LeanPool.DrossFractionalTriangleDecomposition
