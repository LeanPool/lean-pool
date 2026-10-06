/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnpweq`. -/
@[expose]
noncomputable def gNnpweq (A : Class) (B : Class) (n : Var) (M : Class)
    (dv_A_n : n ∉ A.fv) (dv_B_n : n ∉ B.fv) (_dv_M_n : n ∉ M.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem A M) (.classMem B M))
        (synWrex n (synCnnc)
          (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ n } : Finset Var) ∪ M.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let j : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let e : Var := freshVar proofSupport 7
  let x : Var := freshVar proofSupport 8
  let f : Var := freshVar proofSupport 9
  let y : Var := freshVar proofSupport 10
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_c : n ≠ c := Ne.symm fresh_c_ne_n
  have fresh_j : j ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_j_ne_n : j ≠ n := by
    intro h
    exact
      fresh_j
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_j : n ≠ j := Ne.symm fresh_j_ne_n
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d := Ne.symm fresh_d_ne_n
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_e_ne_n : e ≠ n := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_e : n ≠ e := Ne.symm fresh_e_ne_n
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_f_ne_n : f ≠ n := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_f : n ≠ f := Ne.symm fresh_f_ne_n
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_k : a ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_e : a ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_b_ne_m : b ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_b : m ≠ b := Ne.symm fresh_b_ne_m
  have fresh_b_ne_k : b ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_b : k ≠ b := Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_e : b ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
  have fresh_b_ne_f : b ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_j : m ≠ j :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_m_ne_d : m ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_k_ne_c : k ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_k : c ≠ k := Ne.symm fresh_k_ne_c
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have fresh_k_ne_e : k ≠ e :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_e_ne_k : e ≠ k := Ne.symm fresh_k_ne_e
  have fresh_k_ne_x : k ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_f : k ≠ f :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_f_ne_k : f ≠ k := Ne.symm fresh_k_ne_f
  have fresh_k_ne_y : k ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
  have fresh_y_ne_k : y ≠ k := Ne.symm fresh_k_ne_y
  have fresh_c_ne_j : c ≠ j :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_j_ne_c : j ≠ c := Ne.symm fresh_c_ne_j
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_e : c ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_f : c ≠ f :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_f_ne_c : f ≠ c := Ne.symm fresh_c_ne_f
  have fresh_c_ne_y : c ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
  have fresh_y_ne_c : y ≠ c := Ne.symm fresh_c_ne_y
  have fresh_j_ne_d : j ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_j_ne_e : j ≠ e :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_e_ne_j : e ≠ j := Ne.symm fresh_j_ne_e
  have fresh_j_ne_x : j ≠ x :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_x_ne_j : x ≠ j := Ne.symm fresh_j_ne_x
  have fresh_j_ne_f : j ≠ f :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_f_ne_j : f ≠ j := Ne.symm fresh_j_ne_f
  have fresh_j_ne_y : j ≠ y :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 5) (j := 10) (by decide)
  have fresh_y_ne_j : y ≠ j := Ne.symm fresh_j_ne_y
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_f : d ≠ f :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_f_ne_d : f ≠ d := Ne.symm fresh_d_ne_f
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 6) (j := 10) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_e_ne_x : e ≠ x :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_x_ne_e : x ≠ e := Ne.symm fresh_e_ne_x
  have fresh_e_ne_f : e ≠ f :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_f_ne_e : f ≠ e := Ne.symm fresh_e_ne_f
  have fresh_e_ne_y : e ≠ y :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_y_ne_e : y ≠ e := Ne.symm fresh_e_ne_y
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_f_ne_y : f ≠ y :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_y_ne_f : y ≠ f := Ne.symm fresh_f_ne_y
  have dv_cache_0001 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0002 : a ≠ m := by
    clear dv_cache_0001
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have dv_cache_0003 : a ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0004 : b ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ m from (by exact fresh_b_ne_m))
  have dv_cache_0005 : b ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ n from (by exact fresh_b_ne_n))
  have dv_cache_0006 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0007 : b ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_m, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_m, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.classEq (.cv a) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.classEq (.cv a) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : a ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 :
    a ∉
      ((synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCsn (synC0)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_n, fresh_a_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((Wff.classEq (.cv b) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : b ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0017 :
    b ∉ ((synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_n, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_k, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_k, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 : a ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : n ∉ ((Wff.objEq a c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_c, or_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((Wff.objEq b d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_d, or_false, not_false_eq_true])
  have dv_cache_0024 : c ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0025 : d ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0026 :
    d ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_d_ne_c, fresh_d_ne_n, fresh_d_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0027 :
    a ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_n, fresh_a_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 :
    c ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_n, fresh_c_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0029 :
    b ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
            (.classMem (synCpw (.cv d)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_n, fresh_b_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0031 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0032 : j ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0033 :
    j ∉
      ((synWa (.classMem (synCpw (.cv c)) (.cv n))
          (.classMem (synCpw (.cv d)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_j_ne_c, fresh_j_ne_n, fresh_j_ne_d, or_false,
          not_false_eq_true])
  have dv_cache_0034 :
    n ∉
      ((synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_c, fresh_n_ne_j, fresh_n_ne_d, or_false,
          not_false_eq_true])
  have dv_cache_0035 : b ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_M, not_false_eq_true])
  have dv_cache_0036 : a ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0037 : n ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0038 : n ∉ ((Wff.classMem (synCsn (synC0)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0039 : f ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_k, not_false_eq_true])
  have dv_cache_0040 : e ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_k, not_false_eq_true])
  have dv_cache_0041 :
    f ∉
      ((synWrex x (synCcompl (.cv e))
          (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_e, fresh_f_ne_c,
          fresh_f_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0042 :
    e ∉
      ((synWrex y (synCcompl (.cv f))
          (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_f, fresh_e_ne_d,
          fresh_e_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0043 : e ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact (show e ≠ f from (by exact fresh_e_ne_f))
  have dv_cache_0044 : y ∉ ((synCcompl (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_e,
          not_false_eq_true])
  have dv_cache_0045 : x ∉ ((synCcompl (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_f,
          not_false_eq_true])
  have dv_cache_0046 :
    y ∉ ((Wff.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_e, fresh_y_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0047 :
    x ∉ ((Wff.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, fresh_x_ne_f, fresh_x_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0048 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0049 : e ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_c, not_false_eq_true])
  have dv_cache_0050 : x ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_c, not_false_eq_true])
  have dv_cache_0051 : e ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show e ≠ x from (by exact fresh_e_ne_x))
  have dv_cache_0052 : f ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_d, not_false_eq_true])
  have dv_cache_0053 : y ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_d, not_false_eq_true])
  have dv_cache_0054 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0055 : n ∉ ((Wff.objEq a e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_e, or_false, not_false_eq_true])
  have dv_cache_0056 : n ∉ ((Wff.objEq b f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_f, or_false, not_false_eq_true])
  have dv_cache_0057 : a ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_e, not_false_eq_true])
  have dv_cache_0058 : b ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_e, not_false_eq_true])
  have dv_cache_0059 : b ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_f, not_false_eq_true])
  have dv_cache_0060 :
    a ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv e)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_e, fresh_a_ne_n, fresh_a_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0061 :
    b ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv e)) (.cv n))
            (.classMem (synCpw (.cv f)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_e, fresh_b_ne_n, fresh_b_ne_f,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0062 : j ∉ ((synCplc (.cv n) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_j_ne_n, or_false, not_false_eq_true])
  have dv_cache_0063 :
    j ∉
      ((synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x))))
            (synCplc (.cv n) (.cv n))) (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y))))
            (synCplc (.cv n) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_j_ne_e, fresh_j_ne_x, fresh_j_ne_n, fresh_j_ne_f,
          fresh_j_ne_y, or_false, not_false_eq_true])
  have dv_cache_0064 :
    j ∉
      ((synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
          (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_j_ne_c, fresh_j_ne_e, fresh_j_ne_x, fresh_j_ne_d,
          fresh_j_ne_f, fresh_j_ne_y, or_false, not_false_eq_true])
  have dv_cache_0065 :
    x ∉
      ((synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
            (.classMem (synCpw (.cv d)) (.cv j))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_j, fresh_x_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0066 :
    y ∉
      ((synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
            (.classMem (synCpw (.cv d)) (.cv j))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_j, fresh_y_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0067 :
    x ∉
      ((synWa (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWa (synWa (.objMem e k) (.objMem f k))
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv f)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_n,
          fresh_x_ne_e, fresh_x_ne_f, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0068 :
    y ∉
      ((synWa (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWa (synWa (.objMem e k) (.objMem f k))
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv f)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_n,
          fresh_y_ne_e, fresh_y_ne_f, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0069 :
    n ∉
      ((Wff.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
              (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
                (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
            (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_e, fresh_n_ne_f,
          fresh_n_ne_c, fresh_n_ne_x, fresh_n_ne_d, fresh_n_ne_y, fresh_n_ne_j,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0070 :
    n ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem e k) (.objMem f k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_e, fresh_n_ne_f,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0071 :
    e ∉
      ((synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
            (.classMem (synCpw (.cv d)) (.cv j))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_e_ne_c, fresh_e_ne_j, fresh_e_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0072 :
    f ∉
      ((synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
            (.classMem (synCpw (.cv d)) (.cv j))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_f_ne_c, fresh_f_ne_j, fresh_f_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0073 :
    e ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_k, fresh_e_ne_a,
          fresh_e_ne_n, fresh_e_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0074 :
    f ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_k, fresh_f_ne_a,
          fresh_f_ne_n, fresh_f_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0075 :
    c ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_k, fresh_c_ne_a,
          fresh_c_ne_n, fresh_c_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0076 :
    d ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_k, fresh_d_ne_a,
          fresh_d_ne_n, fresh_d_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0077 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0078 : m ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_M, not_false_eq_true])
  have dv_cache_0079 :
    m ∉
      ((synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_a,
          fresh_m_ne_n, fresh_m_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0080 :
    k ∉
      ((synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_a,
          fresh_k_ne_n, fresh_k_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0081 :
    m ∉ ((synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0082 :
    m ∉
      ((synWral a M (synWral b M (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_m_not_M, fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0083 :
    m ∉
      ((synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
            (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
                (.classMem (synCpw (.cv d)) (.cv j))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_c,
          fresh_m_ne_j, fresh_m_ne_d, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0084 : m ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0085 : n ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, dv_A_n, or_false, not_false_eq_true])
  have dv_cache_0086 : n ∉ ((Wff.classEq (.cv b) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, dv_B_n, or_false, not_false_eq_true])
  have dv_cache_0087 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0088 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0089 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0090 :
    a ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw A) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_n, fresh_a_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0091 :
    b ∉
      ((synWrex n (synCnnc)
          (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_n, fresh_b_not_B,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gNnpweqlem1 m n a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (.cv m) (synC0c) dv_cache_0007 dv_cache_0008
  have p0002 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (synWral b (synC0c) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      a (.cv m) (synC0c) dv_cache_0009 dv_cache_0010 p0001
  have p0003 :=
    (Nominal.biimpRefl (synWral a (synC0c) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))))))
  have p0004 := @gEl0c (.cv a)
  have p0005 :=
    @gImbi1i (.classMem (.cv a) (synC0c)) (.classEq (.cv a) (synC0))
      (synWral b (synC0c) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      p0004
  have p0006 :=
    @gAlbii
      (.imp (.classMem (.cv a) (synC0c)) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.imp (.classEq (.cv a) (synC0)) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      a p0005
  have p0007 := @gN0ex
  have p0008 := @gPweq (.cv a) (synC0)
  have p0009 := @gPw0
  have p0010 :=
    @gSyl6eq (.classEq (.cv a) (synC0)) (synCpw (.cv a)) (synCpw (synC0))
      (synCsn (synC0)) p0008 p0009
  have p0011 :=
    @gEleq1d (.classEq (.cv a) (synC0)) (synCpw (.cv a)) (synCsn (synC0)) (.cv n)
      p0010
  have p0012 :=
    @gAnbi1d (.classEq (.cv a) (synC0)) (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)) p0011
  have p0013 :=
    @gRexbidv (.classEq (.cv a) (synC0))
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      n (synCnnc) dv_cache_0011 p0012
  have p0014 :=
    @gRalbidv (.classEq (.cv a) (synC0))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCsn (synC0)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (synC0c) dv_cache_0012 p0013
  have p0015 :=
    @gCeqsalv
      (synWral b (synC0c) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (synWral b (synC0c) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      a (synC0) dv_cache_0013 dv_cache_0014 p0007 p0014
  have p0016 :=
    (Nominal.biimpRefl (synWral b (synC0c) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n))))))
  have p0017 := @gEl0c (.cv b)
  have p0018 :=
    @gImbi1i (.classMem (.cv b) (synC0c)) (.classEq (.cv b) (synC0))
      (synWrex n (synCnnc) (synWa (.classMem (synCsn (synC0)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      p0017
  have p0019 :=
    @gAlbii
      (.imp (.classMem (.cv b) (synC0c)) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (.imp (.classEq (.cv b) (synC0)) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      b p0018
  have p0020 :=
    @gBitri
      (synWral b (synC0c) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (.all b (.imp (.classMem (.cv b) (synC0c)) (synWrex n (synCnnc)
            (synWa (.classMem (synCsn (synC0)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.all b (.imp (.classEq (.cv b) (synC0)) (synWrex n (synCnnc)
            (synWa (.classMem (synCsn (synC0)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0016 p0019
  have p0022 := @gPweq (.cv b) (synC0)
  have p0024 :=
    @gSyl6eq (.classEq (.cv b) (synC0)) (synCpw (.cv b)) (synCpw (synC0))
      (synCsn (synC0)) p0022 p0009
  have p0025 :=
    @gEleq1d (.classEq (.cv b) (synC0)) (synCpw (.cv b)) (synCsn (synC0)) (.cv n)
      p0024
  have p0026 :=
    @gAnbi2d (.classEq (.cv b) (synC0)) (.classMem (synCpw (.cv b)) (.cv n))
      (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCsn (synC0)) (.cv n)) p0025
  have p0027 := @gAnidm (.classMem (synCsn (synC0)) (.cv n))
  have p0028 :=
    @gSyl6bb (.classEq (.cv b) (synC0))
      (synWa (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCsn (synC0)) (.cv n)))
      (.classMem (synCsn (synC0)) (.cv n)) p0026 p0027
  have p0029 :=
    @gRexbidv (.classEq (.cv b) (synC0))
      (synWa (.classMem (synCsn (synC0)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (.classMem (synCsn (synC0)) (.cv n)) n (synCnnc) dv_cache_0015 p0028
  have p0030 :=
    @gCeqsalv
      (synWrex n (synCnnc) (synWa (.classMem (synCsn (synC0)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n))) b (synC0)
      dv_cache_0016 dv_cache_0017 p0007 p0029
  have p0031 :=
    @gN3bitri
      (.all a (.imp (.classEq (.cv a) (synC0)) (synWral b (synC0c) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWral b (synC0c) (synWrex n (synCnnc)
          (synWa (.classMem (synCsn (synC0)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (.all b (.imp (.classEq (.cv b) (synC0)) (synWrex n (synCnnc)
            (synWa (.classMem (synCsn (synC0)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n))) p0015 p0020 p0030
  have p0032 :=
    @gN3bitri
      (synWral a (synC0c) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.all a (.imp (.classMem (.cv a) (synC0c)) (synWral b (synC0c) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (.all a (.imp (.classEq (.cv a) (synC0)) (synWral b (synC0c) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n))) p0003 p0006 p0031
  have p0033 :=
    @gSyl6bb (.classEq (.cv m) (synC0c))
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral a (synC0c) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n))) p0002 p0032
  have p0034 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (.cv m) (.cv k) dv_cache_0007 dv_cache_0018
  have p0035 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (synWral b (.cv k) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      a (.cv m) (.cv k) dv_cache_0009 dv_cache_0019 p0034
  have p0036 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (.cv m) (synCplc (.cv k) (synC1c)) dv_cache_0007 dv_cache_0020
  have p0037 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (synWral b (synCplc (.cv k) (synC1c)) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))))
      a (.cv m) (synCplc (.cv k) (synC1c)) dv_cache_0009 dv_cache_0021 p0036
  have p0038 := @gPweq (.cv a) (.cv c)
  have p0039_e00_recanon :
    Nominal.NPrf (.imp (.objEq a c) (.classEq (synCpw (.cv a)) (synCpw (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gEleq1d (.objEq a c) (synCpw (.cv a)) (synCpw (.cv c)) (.cv n) p0039_e00_recanon
  have p0040 :=
    @gAnbi1d (.objEq a c) (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCpw (.cv c)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)) p0039
  have p0041 :=
    @gRexbidv (.objEq a c)
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw (.cv c)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      n (synCnnc) dv_cache_0022 p0040
  have p0042 := @gPweq (.cv b) (.cv d)
  have p0043_e00_recanon :
    Nominal.NPrf (.imp (.objEq b d) (.classEq (synCpw (.cv b)) (synCpw (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @gEleq1d (.objEq b d) (synCpw (.cv b)) (synCpw (.cv d)) (.cv n) p0043_e00_recanon
  have p0044 :=
    @gAnbi2d (.objEq b d) (.classMem (synCpw (.cv b)) (.cv n))
      (.classMem (synCpw (.cv d)) (.cv n)) (.classMem (synCpw (.cv c)) (.cv n)) p0043
  have p0045 :=
    @gRexbidv (.objEq b d)
      (synWa (.classMem (synCpw (.cv c)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw (.cv c)) (.cv n)) (.classMem (synCpw (.cv d)) (.cv n)))
      n (synCnnc) dv_cache_0023 p0044
  have p0046 :=
    @gCbvral2v
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
          (.classMem (synCpw (.cv d)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      a b c d (synCplc (.cv k) (synC1c)) (synCplc (.cv k) (synC1c)) dv_cache_0021
      dv_cache_0024 dv_cache_0025 dv_cache_0021 dv_cache_0020 dv_cache_0024 dv_cache_0026
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0001 dv_cache_0030 p0041 p0045
  have p0047 := @gEleq2 (.cv n) (.cv j) (synCpw (.cv c))
  have p0048 := @gEleq2 (.cv n) (.cv j) (synCpw (.cv d))
  have p0049_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n j) (synWb (.classMem (synCpw (.cv c)) (.cv n))
          (.classMem (synCpw (.cv c)) (.cv j)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0047
  have p0049_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq n j) (synWb (.classMem (synCpw (.cv d)) (.cv n))
          (.classMem (synCpw (.cv d)) (.cv j)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0049 :=
    @gAnbi12d (.objEq n j) (.classMem (synCpw (.cv c)) (.cv n))
      (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv n))
      (.classMem (synCpw (.cv d)) (.cv j)) p0049_e00_recanon p0049_e01_recanon
  have p0050 :=
    @gCbvrexv
      (synWa (.classMem (synCpw (.cv c)) (.cv n)) (.classMem (synCpw (.cv d)) (.cv n)))
      (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))
      n j (synCnnc) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 p0049
  have p0051 :=
    @gN2ralbii
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
          (.classMem (synCpw (.cv d)) (.cv n))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      c d (synCplc (.cv k) (synC1c)) (synCplc (.cv k) (synC1c)) p0050
  have p0052 :=
    @gBitri
      (synWral a (synCplc (.cv k) (synC1c)) (synWral b (synCplc (.cv k) (synC1c))
          (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
          (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv n))
              (.classMem (synCpw (.cv d)) (.cv n))))))
      (synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
          (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j))))))
      p0046 p0051
  have p0053 :=
    @gSyl6bb (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral a (synCplc (.cv k) (synC1c)) (synWral b (synCplc (.cv k) (synC1c))
          (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
          (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j))))))
      p0037 p0052
  have p0054 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (.cv m) M dv_cache_0007 dv_cache_0035
  have p0055 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      (synWral b M (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      a (.cv m) M dv_cache_0009 dv_cache_0036 p0054
  have p0056 := @gN1cnnc
  have p0058 := @gSnel1c (synC0) p0007
  have p0059 := @gEleq2 (.cv n) (synC1c) (synCsn (synC0))
  have p0060 :=
    @gRspcev (.classMem (synCsn (synC0)) (.cv n))
      (.classMem (synCsn (synC0)) (synC1c)) n (synC1c) (synCnnc) dv_cache_0037
      dv_cache_0031 dv_cache_0038 p0059
  have p0061 :=
    @gMp2an (.classMem (synC1c) (synCnnc)) (.classMem (synCsn (synC0)) (synC1c))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n))) p0056 p0058 p0060
  have p0062 :=
    @gReeanv
      (synWrex x (synCcompl (.cv e)) (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))))
      (synWrex y (synCcompl (.cv f)) (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))
      e f (.cv k) (.cv k) dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
      dv_cache_0043
  have p0063 :=
    @gReeanv (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
      (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))) x y (synCcompl (.cv e))
      (synCcompl (.cv f)) dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
  have p0064 :=
    @gN2rexbii
      (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
          (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
            (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))))
      (synWa (synWrex x (synCcompl (.cv e))
          (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))))
        (synWrex y (synCcompl (.cv f))
          (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))
      e f (.cv k) (.cv k) p0063
  have p0065 :=
    @gElsuc x (.cv c) (.cv k) e dv_cache_0049 dv_cache_0050 dv_cache_0040 dv_cache_0051
  have p0066 :=
    @gElsuc y (.cv d) (.cv k) f dv_cache_0052 dv_cache_0053 dv_cache_0039 dv_cache_0054
  have p0067 :=
    @gAnbi12i (.classMem (.cv c) (synCplc (.cv k) (synC1c)))
      (synWrex e (.cv k) (synWrex x (synCcompl (.cv e))
          (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))))
      (.classMem (.cv d) (synCplc (.cv k) (synC1c)))
      (synWrex f (.cv k) (synWrex y (synCcompl (.cv f))
          (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))
      p0065 p0066
  have p0068 :=
    @gN3bitr4ri
      (synWrex e (.cv k) (synWrex f (.cv k) (synWa (synWrex x (synCcompl (.cv e))
              (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))))
            (synWrex y (synCcompl (.cv f))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))))
      (synWa (synWrex e (.cv k) (synWrex x (synCcompl (.cv e))
            (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))))) (synWrex f (.cv k)
          (synWrex y (synCcompl (.cv f))
            (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))))
      (synWrex e (.cv k) (synWrex f (.cv k) (synWrex x (synCcompl (.cv e))
            (synWrex y (synCcompl (.cv f))
              (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
                (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))))))
      (synWa (.classMem (.cv c) (synCplc (.cv k) (synC1c)))
        (.classMem (.cv d) (synCplc (.cv k) (synC1c))))
      p0062 p0064 p0067
  have p0069 := @gPweq (.cv a) (.cv e)
  have p0070_e00_recanon :
    Nominal.NPrf (.imp (.objEq a e) (.classEq (synCpw (.cv a)) (synCpw (.cv e)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0069
  have p0070 :=
    @gEleq1d (.objEq a e) (synCpw (.cv a)) (synCpw (.cv e)) (.cv n) p0070_e00_recanon
  have p0071 :=
    @gAnbi1d (.objEq a e) (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)) p0070
  have p0072 :=
    @gRexbidv (.objEq a e)
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      n (synCnnc) dv_cache_0055 p0071
  have p0073 := @gPweq (.cv b) (.cv f)
  have p0074_e00_recanon :
    Nominal.NPrf (.imp (.objEq b f) (.classEq (synCpw (.cv b)) (synCpw (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0073
  have p0074 :=
    @gEleq1d (.objEq b f) (synCpw (.cv b)) (synCpw (.cv f)) (.cv n) p0074_e00_recanon
  have p0075 :=
    @gAnbi2d (.objEq b f) (.classMem (synCpw (.cv b)) (.cv n))
      (.classMem (synCpw (.cv f)) (.cv n)) (.classMem (synCpw (.cv e)) (.cv n)) p0074
  have p0076 :=
    @gRexbidv (.objEq b f)
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
      n (synCnnc) dv_cache_0056 p0075
  have p0077_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv e)) (synWb (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCnnc, synCint]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0072
  have p0077_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv f)) (synWb (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv f)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCnnc, synCint]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0076
  have p0077 :=
    @gRspc2v
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      a b (.cv e) (.cv f) (.cv k) (.cv k) dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0019 dv_cache_0019 dv_cache_0018 dv_cache_0060 dv_cache_0061 dv_cache_0001
      p0077_e00_recanon p0077_e01_recanon
  have p0078_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objMem e k) (.objMem f k)) (.imp (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv e)) (.cv n))
              (.classMem (synCpw (.cv f)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWral synWrex synWex synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @gAdantl (synWa (.objMem e k) (.objMem f k))
      (.imp (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))))
      (.classMem (.cv k) (synCnnc)) p0078_e00_recanon
  have p0079 := @gNncaddccl (.cv n) (.cv n)
  have p0080 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0079
  have p0081 :=
    @gAdantl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) (.classMem (.cv k) (synCnnc))
      p0080
  have p0082 :=
    @gN3ad2ant1 (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
      p0081
  have p0083 :=
    @gSimp1l (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0084 :=
    @gSimp1r (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0085 :=
    @gSimp2ll (.objMem e k) (.objMem f k)
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0086 :=
    @gSimp3l (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f)))
  have p0087 :=
    @gSimp2rl (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))
      (synWa (.objMem e k) (.objMem f k))
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0088 := @gNnadjoinpw (.cv e) (.cv k) (.cv n) (.cv x)
  have p0089_e05_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWa (.objMem e k) (.classMem (.cv x) (synCcompl (.cv e))))
          (.classMem (synCpw (.cv e)) (.cv n)))
        (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (synCplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCpw synWss synCin synCcompl synCnin synWnan
          synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0088
  have p0089 :=
    @gSyl221anc
      (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWa (synWa (.objMem e k) (.objMem f k))
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))))
        (synWa (.classMem (.cv x) (synCcompl (.cv e)))
          (.classMem (.cv y) (synCcompl (.cv f)))))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)) (.objMem e k)
      (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (synCpw (.cv e)) (.cv n))
      (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (synCplc (.cv n) (.cv n)))
      p0083 p0084 p0085 p0086 p0087 p0089_e05_recanon
  have p0090 :=
    @gSimp2lr (.objMem e k) (.objMem f k)
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0091 :=
    @gSimp3r (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f)))
  have p0092 :=
    @gSimp2rr (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))
      (synWa (.objMem e k) (.objMem f k))
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
  have p0093 := @gNnadjoinpw (.cv f) (.cv k) (.cv n) (.cv y)
  have p0094_e05_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWa (.objMem f k) (.classMem (.cv y) (synCcompl (.cv f))))
          (.classMem (synCpw (.cv f)) (.cv n)))
        (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (synCplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCpw synWss synCin synCcompl synCnin synWnan
          synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0093
  have p0094 :=
    @gSyl221anc
      (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWa (synWa (.objMem e k) (.objMem f k))
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))))
        (synWa (.classMem (.cv x) (synCcompl (.cv e)))
          (.classMem (.cv y) (synCcompl (.cv f)))))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)) (.objMem f k)
      (.classMem (.cv y) (synCcompl (.cv f))) (.classMem (synCpw (.cv f)) (.cv n))
      (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (synCplc (.cv n) (.cv n)))
      p0083 p0084 p0090 p0091 p0092 p0094_e05_recanon
  have p0095 :=
    @gEleq2 (.cv j) (synCplc (.cv n) (.cv n))
      (synCpw (synCun (.cv e) (synCsn (.cv x))))
  have p0096 :=
    @gEleq2 (.cv j) (synCplc (.cv n) (.cv n))
      (synCpw (synCun (.cv f) (synCsn (.cv y))))
  have p0097 :=
    @gAnbi12d (.classEq (.cv j) (synCplc (.cv n) (.cv n)))
      (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
      (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (synCplc (.cv n) (.cv n)))
      (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j))
      (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (synCplc (.cv n) (.cv n)))
      p0095 p0096
  have p0098 :=
    @gRspcev
      (synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
        (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j)))
      (synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x))))
          (synCplc (.cv n) (.cv n))) (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y))))
          (synCplc (.cv n) (.cv n))))
      j (synCplc (.cv n) (.cv n)) (synCnnc) dv_cache_0062 dv_cache_0032 dv_cache_0063
      p0097
  have p0099 :=
    @gSyl12anc
      (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWa (synWa (.objMem e k) (.objMem f k))
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))))
        (synWa (.classMem (.cv x) (synCcompl (.cv e)))
          (.classMem (.cv y) (synCcompl (.cv f)))))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (synCplc (.cv n) (.cv n)))
      (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (synCplc (.cv n) (.cv n)))
      (synWrex j (synCnnc)
        (synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
          (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j))))
      p0082 p0089 p0094 p0098
  have p0100 := @gPweq (.cv c) (synCun (.cv e) (synCsn (.cv x)))
  have p0101 :=
    @gEleq1d (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x)))) (synCpw (.cv c))
      (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j) p0100
  have p0102 := @gPweq (.cv d) (synCun (.cv f) (synCsn (.cv y)))
  have p0103 :=
    @gEleq1d (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))) (synCpw (.cv d))
      (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j) p0102
  have p0104 :=
    @gBi2anan9 (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
      (.classMem (synCpw (.cv c)) (.cv j))
      (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
      (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))
      (.classMem (synCpw (.cv d)) (.cv j))
      (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j)) p0101 p0103
  have p0105 :=
    @gRexbidv
      (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
        (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))
      (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))
      (synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
        (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j)))
      j (synCnnc) dv_cache_0064 p0104
  have p0106 :=
    @gSyl5ibrcom
      (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWa (synWa (.objMem e k) (.objMem f k))
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n))))
        (synWa (.classMem (.cv x) (synCcompl (.cv e)))
          (.classMem (.cv y) (synCcompl (.cv f)))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
        (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))
      (synWrex j (synCnnc)
        (synWa (.classMem (synCpw (synCun (.cv e) (synCsn (.cv x)))) (.cv j))
          (.classMem (synCpw (synCun (.cv f) (synCsn (.cv y)))) (.cv j))))
      p0099 p0105
  have p0107 :=
    @gN3expia (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (.objMem e k) (.objMem f k)) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (synWa (.classMem (.cv x) (synCcompl (.cv e))) (.classMem (.cv y) (synCcompl (.cv f))))
      (.imp (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
          (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      p0106
  have p0108 :=
    @gRexlimdvv
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWa (synWa (.objMem e k) (.objMem f k))
          (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))))
      (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
        (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      x y (synCcompl (.cv e)) (synCcompl (.cv f)) dv_cache_0044 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0048 p0107
  have p0109 :=
    @gExpr (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWa (.objMem e k) (.objMem f k))
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
      (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
            (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      p0108
  have p0110 :=
    @gAn32s (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWa (.objMem e k) (.objMem f k))
      (.imp (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
        (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
              (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
                (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
            (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j))))))
      p0109
  have p0111 :=
    @gRexlimdva
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem e k) (.objMem f k)))
      (synWa (.classMem (synCpw (.cv e)) (.cv n)) (.classMem (synCpw (.cv f)) (.cv n)))
      (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
            (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      n (synCnnc) dv_cache_0069 dv_cache_0070 p0110
  have p0112 :=
    @gSyld (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem e k) (.objMem f k)))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv e)) (.cv n))
          (.classMem (synCpw (.cv f)) (.cv n))))
      (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
            (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      p0078 p0111
  have p0113 :=
    @gImp (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem e k) (.objMem f k)))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
            (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      p0112
  have p0114 :=
    @gAn32s (.classMem (.cv k) (synCnnc)) (synWa (.objMem e k) (.objMem f k))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.imp (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
            (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
              (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
          (synWa (.classMem (synCpw (.cv c)) (.cv j)) (.classMem (synCpw (.cv d)) (.cv j)))))
      p0113
  have p0115_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k)
              (synWral b (.cv k) (synWrex n (synCnnc)
                  (synWa (.classMem (synCpw (.cv a)) (.cv n))
                    (.classMem (synCpw (.cv b)) (.cv n)))))))
          (synWa (.classMem (.cv e) (.cv k)) (.classMem (.cv f) (.cv k)))) (.imp
          (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
              (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
                (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y))))))) (synWrex j (synCnnc)
            (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0114
  have p0115 :=
    @gRexlimdvva
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWrex x (synCcompl (.cv e)) (synWrex y (synCcompl (.cv f))
          (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
            (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      e f (.cv k) (.cv k) dv_cache_0039 dv_cache_0071 dv_cache_0072 dv_cache_0073
      dv_cache_0074 dv_cache_0043 p0115_e00_recanon
  have p0116 :=
    @gSyl5bi
      (synWa (.classMem (.cv c) (synCplc (.cv k) (synC1c)))
        (.classMem (.cv d) (synCplc (.cv k) (synC1c))))
      (synWrex e (.cv k) (synWrex f (.cv k) (synWrex x (synCcompl (.cv e))
            (synWrex y (synCcompl (.cv f))
              (synWa (.classEq (.cv c) (synCun (.cv e) (synCsn (.cv x))))
                (.classEq (.cv d) (synCun (.cv f) (synCsn (.cv y)))))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      p0068 p0115
  have p0117 :=
    @gRalrimivv
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
          (.classMem (synCpw (.cv d)) (.cv j))))
      c d (synCplc (.cv k) (synC1c)) (synCplc (.cv k) (synC1c)) dv_cache_0025
      dv_cache_0075 dv_cache_0076 dv_cache_0077 p0116
  have p0118 :=
    @gEx (.classMem (.cv k) (synCnnc))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
          (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j))))))
      p0117
  have p0119_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (synWb (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))) (synWral a (.cv k)
            (synWral b (.cv k) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0119 :=
    @gFinds
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWrex n (synCnnc) (.classMem (synCsn (synC0)) (.cv n)))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWral c (synCplc (.cv k) (synC1c)) (synWral d (synCplc (.cv k) (synC1c))
          (synWrex j (synCnnc) (synWa (.classMem (synCpw (.cv c)) (.cv j))
              (.classMem (synCpw (.cv d)) (.cv j))))))
      (synWral a M (synWral b M (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      m k M dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
      dv_cache_0083 dv_cache_0084 p0000 p0033 p0119_e02_recanon p0053 p0055 p0061 p0118
  have p0120 := @gPweq (.cv a) A
  have p0121 := @gEleq1d (.classEq (.cv a) A) (synCpw (.cv a)) (synCpw A) (.cv n) p0120
  have p0122 :=
    @gAnbi1d (.classEq (.cv a) A) (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCpw A) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)) p0121
  have p0123 :=
    @gRexbidv (.classEq (.cv a) A)
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n))) n
      (synCnnc) dv_cache_0085 p0122
  have p0124 := @gPweq (.cv b) B
  have p0125 := @gEleq1d (.classEq (.cv b) B) (synCpw (.cv b)) (synCpw B) (.cv n) p0124
  have p0126 :=
    @gAnbi2d (.classEq (.cv b) B) (.classMem (synCpw (.cv b)) (.cv n))
      (.classMem (synCpw B) (.cv n)) (.classMem (synCpw A) (.cv n)) p0125
  have p0127 :=
    @gRexbidv (.classEq (.cv b) B)
      (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))) n
      (synCnnc) dv_cache_0086 p0126
  have p0128 :=
    @gRspc2v
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n))))
      a b A B M M dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0036 dv_cache_0036
      dv_cache_0035 dv_cache_0090 dv_cache_0091 dv_cache_0001 p0123 p0127
  have p0129 :=
    @gSyl5com (.classMem M (synCnnc))
      (synWral a M (synWral b M (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (synWa (.classMem A M) (.classMem B M))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))))
      p0119 p0128
  have p0130 :=
    @gN3impib (.classMem M (synCnnc)) (.classMem A M) (.classMem B M)
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw A) (.cv n)) (.classMem (synCpw B) (.cv n))))
      p0129
  exact p0130


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_srelk`. -/
@[expose]
noncomputable def gSrelk (A : Class) (B : Class)
    (hyp_srelk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_srelk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B) (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
              (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synWsfin A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 :
    t ∉
      ((synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCopk A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    t ∉
      ((synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCins2k (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synCopk (synCsn (synCsn (.cv x))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((synCsn (synCsn (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) A)) (synCin (synCins3k (synCsik
                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synCpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0016 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((synCopk (synCsn (synCsn (.cv x))) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_B, or_false, not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) B)) (synCin (synCins3k (synCsik (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    t ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((synCopk (.cv y) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0023 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0024 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 : t ∉ ((synCsn (synCsn (synCsn (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0026 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (.cv y) (synCsn (.cv x)))) (synCsymdif (synCins3k (synCssetk))
            (synCins2k (synCsik (synCssetk)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0028 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0029 : y ∉ ((synCpw (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0030 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0031 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0032 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 := @gOpkelxpk A B (synCnnc) (synCnnc) hyp_srelk_1 hyp_srelk_2
  have p0001 := @gOpkex A B
  have p0002 :=
    @gElimak t
      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (synCopk A B) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0001
  have p0003 := @gElpw131c x (.cv t) dv_cache_0004
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0003
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      x dv_cache_0005
  have p0006 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t p0006
  have p0008 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))))
  have p0009 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      x t
  have p0010 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
          (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWex x
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak
                    (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak
                    (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0007 p0008 p0009
  have p0011 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0012 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B)
  have p0013 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCopk (.cv t) (synCopk A B))
      (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      p0012
  have p0014 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      t (synCsn (synCsn (synCsn (synCsn (.cv x))))) dv_cache_0006 dv_cache_0007 p0011
      p0013
  have p0015 :=
    @gElin (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
      (synCins3k (synCimak (synCin (synCins3k (synCsik
                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
  have p0016 := @gOpkex (synCsn (synCsn (.cv x))) A
  have p0017 :=
    @gElimak t
      (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
              (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn (synCsn (.cv x))) A)
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0016
  have p0018 := @gElpw121c y (.cv t) dv_cache_0011
  have p0019 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
          (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      p0018
  have p0020 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
          (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      y dv_cache_0012
  have p0021 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
              (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                    (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      p0019 p0020
  have p0022 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
              (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                    (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      t p0021
  have p0023 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))))
  have p0024 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      y t
  have p0025 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
              (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                    (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (synWex t (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      p0022 p0023 p0024
  have p0026 := @gSnex (synCsn (synCsn (.cv y)))
  have p0027 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv y))))
      (synCopk (synCsn (synCsn (.cv x))) A)
  have p0028 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A))
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (synCsn (synCsn (.cv x))) A))
      (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
              (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      p0027
  have p0029 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
          (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCin (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv y)))) dv_cache_0013 dv_cache_0014 p0026 p0028
  have p0030 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (synCsn (synCsn (.cv x))) A))
      (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCins2k (synCssetk))
  have p0031 := @gSnex (.cv y)
  have p0032 := @gSnex (synCsn (.cv x))
  have p0033 :=
    @gOtkelins3k (synCsn (.cv y)) (synCsn (synCsn (.cv x))) A
      (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0031 p0032 hyp_srelk_1
  have p0034 := @gVex y
  have p0035 := @gSnex (.cv x)
  have p0036 :=
    @gOpksnelsik (.cv y) (synCsn (.cv x))
      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0034 p0035
  have p0037 := @gVex x
  have p0038 := @gEqpw1relk (.cv y) (.cv x) p0034 p0037
  have p0039 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCins3k (synCsik
            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv y)) (synCsn (synCsn (.cv x)))) (synCsik
          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (.cv y) (synCsn (.cv x)))
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv y) (synCpw1 (.cv x))) p0033 p0036 p0038
  have p0040 :=
    @gOtkelins2k (synCsn (.cv y)) (synCsn (synCsn (.cv x))) A (synCssetk) p0031 p0032
      hyp_srelk_1
  have p0041 := @gElssetk (.cv y) A p0034 hyp_srelk_1
  have p0042 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)) (.classMem (.cv y) A) p0040
      p0041
  have p0043 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCins3k (synCsik
            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classEq (.cv y) (synCpw1 (.cv x)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCins2k (synCssetk)))
      (.classMem (.cv y) A) p0039 p0042
  have p0044 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
              (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                    (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) A)) (synCin (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) A)) (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) A)) (synCins2k (synCssetk))))
      (synWa (.classEq (.cv y) (synCpw1 (.cv x))) (.classMem (.cv y) A)) p0029 p0030
      p0043
  have p0045 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
              (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                    (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (synWa (.classEq (.cv y) (synCpw1 (.cv x))) (.classMem (.cv y) A)) y p0044
  have p0046 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) A) (synCimak (synCin (synCins3k
              (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
            (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) A)) (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      (synWex y (synWa (.classEq (.cv y) (synCpw1 (.cv x))) (.classMem (.cv y) A)))
      p0017 p0025 p0045
  have p0047 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) A B
      (synCimak (synCin (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0032 hyp_srelk_1 hyp_srelk_2
  have p0048 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y
      (synCpw1 (.cv x)) A dv_cache_0015 dv_cache_0016)
  have p0049 :=
    @gN3bitr4i
      (.classMem (synCopk (synCsn (synCsn (.cv x))) A) (synCimak (synCin (synCins3k
              (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex y (synWa (.classEq (.cv y) (synCpw1 (.cv x))) (.classMem (.cv y) A)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCins3k (synCimak (synCin (synCins3k (synCsik
                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw1 (.cv x)) A) p0046 p0047 p0048
  have p0050 := @gOpkex (synCsn (synCsn (.cv x))) B
  have p0051 :=
    @gElimak t
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn (synCsn (.cv x))) B)
      dv_cache_0017 dv_cache_0009 dv_cache_0018 p0050
  have p0052 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
          (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      p0018
  have p0053 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
          (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      y dv_cache_0019
  have p0054 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      p0052 p0053
  have p0055 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      t p0054
  have p0056 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))))
  have p0057 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      y t
  have p0058 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (synWex t (synWex y (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      p0055 p0056 p0057
  have p0059 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv y))))
      (synCopk (synCsn (synCsn (.cv x))) B)
  have p0060 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B))
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (synCsn (synCsn (.cv x))) B))
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
      p0059
  have p0061 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
          (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCin (synCins3k (synCsik (synCcompl
                (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv y)))) dv_cache_0013 dv_cache_0020 p0026 p0060
  have p0062 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (synCsn (synCsn (.cv x))) B))
      (synCins3k (synCsik (synCcompl (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synCins2k (synCssetk))
  have p0063 :=
    @gOtkelins3k (synCsn (.cv y)) (synCsn (synCsn (.cv x))) B
      (synCsik (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0031 p0032 hyp_srelk_2
  have p0064 :=
    @gOpksnelsik (.cv y) (synCsn (.cv x))
      (synCcompl (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0034 p0035
  have p0065 := @gOpkex (.cv y) (synCsn (.cv x))
  have p0066 :=
    @gElimak t
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv y) (synCsn (.cv x))) dv_cache_0021
      dv_cache_0009 dv_cache_0022 p0065
  have p0067 := @gElpw121c z (.cv t) dv_cache_0023
  have p0068 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      p0067
  have p0069 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      z dv_cache_0024
  have p0070 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      p0068 p0069
  have p0071 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      t p0070
  have p0072 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
  have p0073 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      z t
  have p0074 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      p0071 p0072 p0073
  have p0075 := @gSnex (synCsn (synCsn (.cv z)))
  have p0076 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z))))
      (synCopk (.cv y) (synCsn (.cv x)))
  have p0077 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv y) (synCsn (.cv x))))
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) p0076
  have p0078 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x))))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      t (synCsn (synCsn (synCsn (.cv z)))) dv_cache_0025 dv_cache_0026 p0075 p0077
  have p0079 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv y) (synCsn (.cv x))))
      (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))
  have p0080 := @gSnex (.cv z)
  have p0081 :=
    @gOtkelins3k (synCsn (.cv z)) (.cv y) (synCsn (.cv x)) (synCssetk) p0080 p0034
      p0035
  have p0082 := @gVex z
  have p0083 := @gElssetk (.cv z) (.cv y) p0082 p0034
  have p0084_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0083
  have p0084 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x)))) (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y) p0081
      p0084_e01_recanon
  have p0085 :=
    @gOtkelins2k (synCsn (.cv z)) (.cv y) (synCsn (.cv x)) (synCsik (synCssetk))
      p0080 p0034 p0035
  have p0086 := @gOpksnelsik (.cv z) (.cv x) (synCssetk) p0082 p0037
  have p0087 := @gOpkelssetkg (.cv z) (.cv x) (synCvv) (synCvv)
  have p0088 :=
    @gMp2an (.classMem (.cv z) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv z) (.cv x)) (synCssetk)) (synWss (.cv z) (.cv x)))
      p0082 p0037 p0087
  have p0089 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x)))) (synCins2k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv x))) (synCsik (synCssetk)))
      (.classMem (synCopk (.cv z) (.cv x)) (synCssetk)) (synWss (.cv z) (.cv x)) p0085
      p0086 p0088
  have p0090 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x)))) (synCins3k (synCssetk)))
      (.objMem z y)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x)))) (synCins2k (synCsik (synCssetk))))
      (synWss (.cv z) (.cv x)) p0084 p0089
  have p0091 :=
    @gNotbii
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (.cv y) (synCsn (.cv x)))) (synCins3k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv y) (synCsn (.cv x))))
          (synCins2k (synCsik (synCssetk)))))
      (synWb (.objMem z y) (synWss (.cv z) (.cv x))) p0090
  have p0092 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (.cv y) (synCsn (.cv x))))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      (.neg (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
              (synCopk (.cv y) (synCsn (.cv x)))) (synCins3k (synCssetk))) (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv z))))
              (synCopk (.cv y) (synCsn (.cv x)))) (synCins2k (synCsik (synCssetk))))))
      (.neg (synWb (.objMem z y) (synWss (.cv z) (.cv x)))) p0078 p0079 p0091
  have p0093 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (.neg (synWb (.objMem z y) (synWss (.cv z) (.cv x)))) z p0092
  have p0094 :=
    @gN3bitri
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv x))))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      (synWex z (.neg (synWb (.objMem z y) (synWss (.cv z) (.cv x))))) p0066 p0074
      p0093
  have p0095 :=
    @gNotbii
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex z (.neg (synWb (.objMem z y) (synWss (.cv z) (.cv x))))) p0094
  have p0096 :=
    @gElcompl (synCopk (.cv y) (synCsn (.cv x)))
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))
      p0065
  have p0097 := @gAlex (synWb (.objMem z y) (synWss (.cv z) (.cv x))) z
  have p0098 :=
    @gN3bitr4i
      (.neg (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWex z (.neg (synWb (.objMem z y) (synWss (.cv z) (.cv x))))))
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.all z (synWb (.objMem z y) (synWss (.cv z) (.cv x)))) p0095 p0096 p0097
  have p0099 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw z (.cv x)
      dv_cache_0027
  have p0100 :=
    @gEqeq2i (synCpw (.cv x)) (.cab z (synWss (.cv z) (.cv x))) (.cv y) p0099
  have p0101 := @gEqabb (synWss (.cv z) (.cv x)) z (.cv y) dv_cache_0028
  have p0102_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (.cab z (synWss (.cv z) (.cv x))))
        (.all z (synWb (.objMem z y) (synWss (.cv z) (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0101
  have p0102 :=
    @gBitri (.classEq (.cv y) (synCpw (.cv x)))
      (.classEq (.cv y) (.cab z (synWss (.cv z) (.cv x))))
      (.all z (synWb (.objMem z y) (synWss (.cv z) (.cv x)))) p0100 p0102_e01_recanon
  have p0103 :=
    @gBitr4i
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.all z (synWb (.objMem z y) (synWss (.cv z) (.cv x))))
      (.classEq (.cv y) (synCpw (.cv x))) p0098 p0102
  have p0104 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (.cv y)) (synCsn (synCsn (.cv x)))) (synCsik (synCcompl
            (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv y) (synCpw (.cv x))) p0063 p0064 p0103
  have p0105 :=
    @gOtkelins2k (synCsn (.cv y)) (synCsn (synCsn (.cv x))) B (synCssetk) p0031 p0032
      hyp_srelk_2
  have p0106 := @gElssetk (.cv y) B p0034 hyp_srelk_2
  have p0107 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv y)) B) (synCssetk)) (.classMem (.cv y) B) p0105
      p0106
  have p0108 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classEq (.cv y) (synCpw (.cv x)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCins2k (synCssetk)))
      (.classMem (.cv y) B) p0104 p0107
  have p0109 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
          (synCopk (synCsn (synCsn (.cv x))) B)) (synCin (synCins3k (synCsik (synCcompl
                (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) B)) (synCins3k (synCsik (synCcompl
                (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
        (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y))))
            (synCopk (synCsn (synCsn (.cv x))) B)) (synCins2k (synCssetk))))
      (synWa (.classEq (.cv y) (synCpw (.cv x))) (.classMem (.cv y) B)) p0061 p0062
      p0108
  have p0110 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (synWa (.classEq (.cv y) (synCpw (.cv x))) (.classMem (.cv y) B)) y p0109
  have p0111 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) B) (synCimak (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv x))) B)) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      (synWex y (synWa (.classEq (.cv y) (synCpw (.cv x))) (.classMem (.cv y) B)))
      p0051 p0058 p0110
  have p0112 :=
    @gOtkelins2k (synCsn (synCsn (.cv x))) A B
      (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0032 hyp_srelk_1 hyp_srelk_2
  have p0113 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y
      (synCpw (.cv x)) B dv_cache_0029 dv_cache_0030)
  have p0114 :=
    @gN3bitr4i
      (.classMem (synCopk (synCsn (synCsn (.cv x))) B) (synCimak (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      (synWex y (synWa (.classEq (.cv y) (synCpw (.cv x))) (.classMem (.cv y) B)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv x)) B) p0111 p0112 p0113
  have p0115 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCins3k (synCimak (synCin (synCins3k (synCsik
                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw1 (.cv x)) A)
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv x)) B) p0049 p0114
  have p0116 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B))
        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B)) (synCins3k
            (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A B)) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B)) p0014
      p0015 p0115
  have p0117 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B)) x p0116
  have p0118 :=
    @gN3bitri
      (.classMem (synCopk A B) (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k
                    (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A B)) (synCin (synCins3k (synCimak
                    (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex x (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B)))
      p0002 p0010 p0117
  have p0119 :=
    @gAnbi12i (.classMem (synCopk A B) (synCxpk (synCnnc) (synCnnc)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k
                    (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex x (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B)))
      p0000 p0118
  have p0120 :=
    (Nominal.biimpRefl (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B)))))
  have p0121 :=
    @gBitr4i
      (synWa (.classMem (synCopk A B) (synCxpk (synCnnc) (synCnnc)))
        (.classMem (synCopk A B) (synCimak (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B))))
      p0119 p0120
  have p0122 :=
    @gElin (synCopk A B) (synCxpk (synCnnc) (synCnnc))
      (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0123 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin A B x
      dv_cache_0031 dv_cache_0032
  have p0124 :=
    @gN3bitr4i
      (synWa (.classMem (synCopk A B) (synCxpk (synCnnc) (synCnnc)))
        (.classMem (synCopk A B) (synCimak (synCin (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) A) (.classMem (synCpw (.cv x)) B))))
      (.classMem (synCopk A B) (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
              (synCins3k (synCimak (synCin (synCins3k (synCsik
                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWsfin A B) p0121 p0122 p0123
  exact p0124


end NFChoice.DirectNominalPrf.WPPReplay

end
