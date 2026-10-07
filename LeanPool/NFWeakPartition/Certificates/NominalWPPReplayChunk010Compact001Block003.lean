/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnadjoin`. -/
@[expose]
noncomputable def gNnadjoin (x : Var) (L : Class) (N : Class) (X : Class) (b : Var)
    (dv_L_b : b ∉ L.fv) (dv_L_x : x ∉ L.fv) (dv_X_b : b ∉ X.fv) (dv_X_x : x ∉ X.fv)
    (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (.imp (synW3a (.classMem N (synCnnc)) (.classMem L N)
          (.classMem X (synCcompl (synCuni L)))) (.classMem
          (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ L.fv ∪ N.fv ∪ X.fv ∪ ({ b } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let l : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let z : Var := freshVar proofSupport 6
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_L : y ∉ L.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_l : l ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_l_ne_x : l ≠ x := by
    intro h
    exact
      fresh_l
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_l : x ≠ l := Ne.symm fresh_l_ne_x
  have fresh_l_not_L : l ∉ L.fv := by
    intro h
    exact
      fresh_l
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_l_not_N : l ∉ N.fv := by
    intro h
    exact
      fresh_l
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_l_ne_b : l ≠ b := by
    intro h
    exact fresh_l (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_l : b ≠ l := Ne.symm fresh_l_ne_b
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_ne_b : n ≠ b := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_k_ne_b : k ≠ b := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_k : b ≠ k := Ne.symm fresh_k_ne_b
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_b : a ≠ b := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_y_ne_l : y ≠ l :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_l_ne_y : l ≠ y := Ne.symm fresh_y_ne_l
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_k : y ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_y : k ≠ y := Ne.symm fresh_y_ne_k
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_l_ne_n : l ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_l : n ≠ l := Ne.symm fresh_l_ne_n
  have fresh_l_ne_k : l ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_l : k ≠ l := Ne.symm fresh_l_ne_k
  have fresh_l_ne_a : l ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_l : a ≠ l := Ne.symm fresh_l_ne_a
  have fresh_l_ne_c : l ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_l : c ≠ l := Ne.symm fresh_l_ne_c
  have fresh_l_ne_z : l ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_z_ne_l : z ≠ l := Ne.symm fresh_l_ne_z
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_a : n ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_k_ne_a : k ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_k : a ≠ k := Ne.symm fresh_k_ne_a
  have fresh_k_ne_c : k ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_k : c ≠ k := Ne.symm fresh_k_ne_c
  have fresh_k_ne_z : k ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_z_ne_k : z ≠ k := Ne.symm fresh_k_ne_z
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_c_ne_z : c ≠ z :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : b ∉ ((Wff.classEq (.cv y) X)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_y, dv_X_b, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) X)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_X_x, or_false, not_false_eq_true])
  have dv_cache_0003 : b ≠ l :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show b ≠ l from (by exact fresh_b_ne_l))
  have dv_cache_0004 : b ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ n from (by exact fresh_b_ne_n))
  have dv_cache_0005 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ x from (by exact dv_b_x))
  have dv_cache_0006 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0007 : l ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show l ≠ n from (by exact fresh_l_ne_n))
  have dv_cache_0008 : l ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show l ≠ x from (by exact fresh_l_ne_x))
  have dv_cache_0009 : l ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show l ≠ y from (by exact fresh_l_ne_y))
  have dv_cache_0010 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0011 : n ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show n ≠ y from (by exact fresh_n_ne_y))
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : l ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_l_ne_n, not_false_eq_true])
  have dv_cache_0014 : l ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : b ∉ ((Class.cv l)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_l, not_false_eq_true])
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
  have dv_cache_0017 : x ∉ ((Wff.classEq (.cv l) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_l, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 : l ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 :
    l ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
              (synWrex b (synC0)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_l_ne_y, fresh_l_ne_x,
          fresh_l_ne_b, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : l ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_l_ne_k, not_false_eq_true])
  have dv_cache_0021 : l ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_l_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : b ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_a, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Wff.objEq l a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_l, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
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
  have dv_cache_0025 :
    a ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_l,
          fresh_a_ne_x, fresh_a_ne_b, fresh_a_ne_k, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0026 :
    l ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_l_ne_y, fresh_l_ne_a,
          fresh_l_ne_x, fresh_l_ne_b, fresh_l_ne_k, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0027 : l ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_l_not_N, not_false_eq_true])
  have dv_cache_0028 : c ∉ ((Class.cv a)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_a, not_false_eq_true])
  have dv_cache_0029 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0030 : c ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_k, not_false_eq_true])
  have dv_cache_0031 : c ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show c ≠ z from (by exact fresh_c_ne_z))
  have dv_cache_0032 : b ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_c, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((Wff.objEq l c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_l, fresh_x_ne_c, or_false, not_false_eq_true])
  have dv_cache_0034 : l ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_l_ne_c, not_false_eq_true])
  have dv_cache_0035 :
    l ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_l_ne_y, fresh_l_ne_c,
          fresh_l_ne_x, fresh_l_ne_b, fresh_l_ne_k, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0036 :
    b ∉
      ((synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_c,
          fresh_b_ne_z, fresh_b_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0037 :
    b ∉ ((Wff.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y))))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, dv_b_x, fresh_b_ne_z, fresh_b_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0038 : x ∉ ((synCun (.cv z) (synCsn (.cv y)))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0039 :
    x ∉
      ((synWrex b (.cv c) (.classEq (synCun (.cv z) (synCsn (.cv y)))
            (synCun (.cv b) (synCsn (.cv y)))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_z,
          fresh_x_ne_y, (Ne.symm dv_b_x), or_false, and_false, not_false_eq_true])
  have dv_cache_0040 : b ∉ ((synCun (.cv c) (synCsn (.cv z)))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0041 :
    x ∉ ((Wff.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_c, fresh_x_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0042 : b ∉ ((Class.cv z)).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0043 : z ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_k, not_false_eq_true])
  have dv_cache_0044 :
    c ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c))))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_a,
          fresh_c_ne_x, fresh_c_ne_b, fresh_c_ne_k, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0045 :
    z ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c))))).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_a,
          fresh_z_ne_x, fresh_z_ne_b, fresh_z_ne_k, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0046 :
    c ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k)))))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_k, fresh_c_ne_y,
          fresh_c_ne_l, fresh_c_ne_x, fresh_c_ne_b, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0047 :
    z ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k)))))).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_k, fresh_z_ne_y,
          fresh_z_ne_l, fresh_z_ne_x, fresh_z_ne_b, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0048 :
    a ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_k, fresh_a_ne_y,
          fresh_a_ne_l, fresh_a_ne_x, fresh_a_ne_b, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0049 : n ∉ (N).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0050 :
    n ∉
      ((synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
              (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y,
          fresh_n_ne_l, fresh_n_ne_x, fresh_n_ne_b, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0051 :
    k ∉
      ((synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
              (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))))).fv :=
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
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_n, fresh_k_ne_y,
          fresh_k_ne_l, fresh_k_ne_x, fresh_k_ne_b, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0052 :
    n ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
              (synWrex b (synC0)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_y, fresh_n_ne_x,
          fresh_n_ne_b, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0053 :
    n ∉
      ((synWral l N (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
              (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_N, fresh_n_ne_y,
          fresh_n_ne_l, fresh_n_ne_x, fresh_n_ne_b, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0054 :
    n ∉
      ((synWral a (synCplc (.cv k) (synC1c))
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
                (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (synCplc (.cv k) (synC1c)))))).fv :=
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
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y,
          fresh_n_ne_a, fresh_n_ne_x, fresh_n_ne_b, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0055 : n ≠ k :=
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
    exact (show n ≠ k from (by exact fresh_n_ne_k))
  have dv_cache_0056 : b ∉ (L).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_b, not_false_eq_true])
  have dv_cache_0057 : x ∉ ((Wff.classEq (.cv l) L)).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_l, dv_L_x, or_false, not_false_eq_true])
  have dv_cache_0058 : l ∉ (L).fv :=
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
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_l_not_L, not_false_eq_true])
  have dv_cache_0059 :
    l ∉
      ((Wff.imp (.classMem (.cv y) (synCcompl (synCuni L))) (.classMem
            (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            N))).fv :=
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
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_l_ne_y, fresh_l_not_L,
          fresh_l_ne_x, fresh_l_ne_b, fresh_l_not_N, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0060 : y ∉ (X).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0061 : y ∉ ((synCcompl (synCuni L))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_y_not_L,
          not_false_eq_true])
  have dv_cache_0062 :
    y ∉
      ((Wff.imp (.classMem N (synCnnc)) (.imp (.classMem L N) (.classMem
              (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X)))))
              N)))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_N, fresh_y_not_L,
          fresh_y_ne_x, fresh_y_ne_b, fresh_y_not_X, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 := @gSneq (.cv y) X
  have p0001 := @gUneq2d (.classEq (.cv y) X) (synCsn (.cv y)) (synCsn X) (.cv b) p0000
  have p0002 :=
    @gEqeq2d (.classEq (.cv y) X) (synCun (.cv b) (synCsn (.cv y)))
      (synCun (.cv b) (synCsn X)) (.cv x) p0001
  have p0003 :=
    @gRexbidv (.classEq (.cv y) X) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))
      (.classEq (.cv x) (synCun (.cv b) (synCsn X))) b L dv_cache_0001 p0002
  have p0004 :=
    @gAbbidv (.classEq (.cv y) X)
      (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X)))) x dv_cache_0002
      p0003
  have p0005 :=
    @gEleq1d (.classEq (.cv y) X)
      (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N p0004
  have p0006 :=
    @gImbi2d (.classEq (.cv y) X)
      (.classMem
        (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)
      (.classMem (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N)
      (.classMem L N) p0005
  have p0007 :=
    @gImbi2d (.classEq (.cv y) X)
      (.imp (.classMem L N) (.classMem
          (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N))
      (.imp (.classMem L N) (.classMem
          (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N))
      (.classMem N (synCnnc)) p0006
  have p0008 :=
    @gNnadjoinlem1 x y n b l dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @gEleq2 (.cv n) (synC0c)
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0010 :=
    @gEl0c
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0011 :=
    @gAb0 (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) x
  have p0012 :=
    @gBitri
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synC0c))
      (.classEq (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (synC0))
      (.all x (.neg
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0010 p0011
  have p0013 :=
    @gSyl6bb (.classEq (.cv n) (synC0c))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synC0c))
      (.all x (.neg
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0009 p0012
  have p0014 :=
    @gImbi2d (.classEq (.cv n) (synC0c))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.all x (.neg
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) p0013
  have p0015 :=
    @gRaleqbi1dv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      l (.cv n) (synC0c) dv_cache_0013 dv_cache_0014 p0014
  have p0016 :=
    (Nominal.biimpRefl (synWral l (synC0c)
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))))
  have p0017 := @gEl0c (.cv l)
  have p0018 :=
    @gImbi1i (.classMem (.cv l) (synC0c)) (.classEq (.cv l) (synC0))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      p0017
  have p0019 :=
    @gAlbii
      (.imp (.classMem (.cv l) (synC0c))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))))
      (.imp (.classEq (.cv l) (synC0))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))))
      l p0018
  have p0020 := @gN0ex
  have p0021 := @gUnieq (.cv l) (synC0)
  have p0022 :=
    @gCompleqd (.classEq (.cv l) (synC0)) (synCuni (.cv l)) (synCuni (synC0)) p0021
  have p0023 :=
    @gEleq2d (.classEq (.cv l) (synC0)) (synCcompl (synCuni (.cv l)))
      (synCcompl (synCuni (synC0))) (.cv y) p0022
  have p0024 :=
    @gRexeq (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv l) (synC0)
      dv_cache_0015 dv_cache_0016
  have p0025 :=
    @gNotbid (.classEq (.cv l) (synC0))
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) p0024
  have p0026 :=
    @gAlbidv (.classEq (.cv l) (synC0))
      (.neg (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.neg (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      x dv_cache_0017 p0025
  have p0027 :=
    @gImbi12d (.classEq (.cv l) (synC0))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.classMem (.cv y) (synCcompl (synCuni (synC0))))
      (.all x (.neg
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.all x (.neg
          (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0023 p0026
  have p0028 :=
    @gCeqsalv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
            (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      l (synC0) dv_cache_0018 dv_cache_0019 p0020 p0027
  have p0029 :=
    @gN3bitrri
      (synWral l (synC0c) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x
            (.neg (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))))
      (.all l (.imp (.classMem (.cv l) (synC0c))
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))))
      (.all l (.imp (.classEq (.cv l) (synC0))
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x (.neg
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
            (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      p0016 p0019 p0028
  have p0030 :=
    @gSyl6bbr (.classEq (.cv n) (synC0c))
      (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      (synWral l (synC0c) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.all x
            (.neg (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
            (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      p0015 p0029
  have p0031 :=
    @gEleq2 (.cv n) (.cv k)
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (synWb (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n)) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gImbi2d (.objEq n k)
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) p0032_e00_recanon
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv k)) (synWb
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv n))) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
              (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa synCuni synWex synWrex
          synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @gRaleqbi1dv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      l (.cv n) (.cv k) dv_cache_0013 dv_cache_0020 p0033_e00_recanon
  have p0034 :=
    @gEleq2 (.cv n) (synCplc (.cv k) (synC1c))
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0035 :=
    @gImbi2d (.classEq (.cv n) (synCplc (.cv k) (synC1c)))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCplc (.cv k) (synC1c)))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) p0034
  have p0036 :=
    @gRaleqbi1dv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      l (.cv n) (synCplc (.cv k) (synC1c)) dv_cache_0013 dv_cache_0021 p0035
  have p0037 := @gUnieq (.cv l) (.cv a)
  have p0038_e00_recanon :
    Nominal.NPrf (.imp (.objEq l a) (.classEq (synCuni (.cv l)) (synCuni (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @gCompleqd (.objEq l a) (synCuni (.cv l)) (synCuni (.cv a)) p0038_e00_recanon
  have p0039 :=
    @gEleq2d (.objEq l a) (synCcompl (synCuni (.cv l))) (synCcompl (synCuni (.cv a)))
      (.cv y) p0038
  have p0040 :=
    @gRexeq (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv l) (.cv a)
      dv_cache_0015 dv_cache_0022
  have p0041_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq l a) (synWb
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
          (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0040
  have p0041 :=
    @gAbbidv (.objEq l a)
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) x
      dv_cache_0023 p0041_e00_recanon
  have p0042 :=
    @gEleq1d (.objEq l a)
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cab x (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (synCplc (.cv k) (synC1c)) p0041
  have p0043 :=
    @gImbi12d (.objEq l a) (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv a))))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCplc (.cv k) (synC1c)))
      (.classMem (.cab x
          (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCplc (.cv k) (synC1c)))
      p0039 p0042
  have p0044 :=
    @gCbvralv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
            (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      l a (synCplc (.cv k) (synC1c)) dv_cache_0021 dv_cache_0024 dv_cache_0025
      dv_cache_0026 p0043
  have p0045 :=
    @gSyl6bb (.classEq (.cv n) (synCplc (.cv k) (synC1c)))
      (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      (synWral l (synCplc (.cv k) (synC1c))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c)))))
      (synWral a (synCplc (.cv k) (synC1c))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c)))))
      p0036 p0044
  have p0046 :=
    @gEleq2 (.cv n) N
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0047 :=
    @gImbi2d (.classEq (.cv n) N)
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)
      (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) p0046
  have p0048 :=
    @gRaleqbi1dv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N))
      l (.cv n) N dv_cache_0013 dv_cache_0027 p0047
  have p0049 := @gRex0 (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b
  have p0050 := Nominal.gen p0049 x
  have p0051 :=
    @gA1i
      (.all x (.neg
          (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.classMem (.cv y) (synCcompl (synCuni (synC0)))) p0050
  have p0052 :=
    @gElsuc z (.cv a) (.cv k) c dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
  have p0053 := @gUnieq (.cv l) (.cv c)
  have p0054_e00_recanon :
    Nominal.NPrf (.imp (.objEq l c) (.classEq (synCuni (.cv l)) (synCuni (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0053
  have p0054 :=
    @gCompleqd (.objEq l c) (synCuni (.cv l)) (synCuni (.cv c)) p0054_e00_recanon
  have p0055 :=
    @gEleq2d (.objEq l c) (synCcompl (synCuni (.cv l))) (synCcompl (synCuni (.cv c)))
      (.cv y) p0054
  have p0056 :=
    @gRexeq (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv l) (.cv c)
      dv_cache_0015 dv_cache_0032
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq l c) (synWb
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @gAbbidv (.objEq l c)
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) x
      dv_cache_0033 p0057_e00_recanon
  have p0058 :=
    @gEleq1d (.objEq l c)
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cab x (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cv k) p0057
  have p0059 :=
    @gImbi12d (.objEq l c) (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      p0055 p0058
  have p0060_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv l) (.cv c)) (synWb
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv k))) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem
              (.cab x (synWrex b (.cv c)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa synCuni synWex synWrex
          synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0059
  have p0060 :=
    @gRspcv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      l (.cv c) (.cv k) dv_cache_0034 dv_cache_0020 dv_cache_0035 p0060_e00_recanon
  have p0061_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem c k) (.imp (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k)))) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem
              (.cab x (synWrex b (.cv c)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWral synCcompl synCnin synWnan synWa synCuni synWex synWrex
          synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @gAdantr (.objMem c k)
      (.imp (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (.classMem (.cv z) (synCcompl (.cv c))) p0061_e00_recanon
  have p0062 :=
    @gAdantl (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (.imp (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (.classMem (.cv k) (synCnnc)) p0061
  have p0063 :=
    @gElin (.cv y) (synCcompl (synCuni (.cv c)))
      (synCcompl (synCuni (synCsn (.cv z))))
  have p0064 :=
    @gSimp3l (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z)))))
  have p0065 := @gVex z
  have p0066 := @gUnisn (.cv z) p0065
  have p0067 := @gCompleqi (synCuni (synCsn (.cv z))) (.cv z) p0066
  have p0068 :=
    @gEleq2i (synCcompl (synCuni (synCsn (.cv z)))) (synCcompl (.cv z)) (.cv y) p0067
  have p0069 :=
    @gAnbi2i (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z)))))
      (.classMem (.cv y) (synCcompl (.cv z)))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) p0068
  have p0070 :=
    @gSimpr
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
  have p0071 :=
    @gSimpl2r (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
        (.classMem (.cv y) (synCcompl (.cv z))))
      (.objMem b c)
  have p0072 := @gElcompl (.cv z) (.cv c) p0065
  have p0073_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv z) (synCcompl (.cv c))) (.neg (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0072
  have p0073 :=
    @gSylib
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.objMem b c))
      (.classMem (.cv z) (synCcompl (.cv c))) (.neg (.objMem z c)) p0071
      p0073_e01_recanon
  have p0074 := @gEleq1a (.cv b) (.cv c) (.cv z)
  have p0075_e00_recanon :
    Nominal.NPrf (.imp (.objMem b c) (.imp (.objEq z b) (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0074
  have p0075 :=
    @gAdantl (.objMem b c) (.imp (.objEq z b) (.objMem z c))
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      p0075_e00_recanon
  have p0076 :=
    @gMtod
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.objMem b c))
      (.objEq z b) (.objMem z c) p0073 p0075
  have p0077 :=
    @gSimpl3r (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.classMem (.cv y) (synCcompl (.cv z))) (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))) (.objMem b c)
  have p0078 := @gVex y
  have p0079 := @gElcompl (.cv y) (.cv z) p0078
  have p0080_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCcompl (.cv z))) (.neg (.objMem y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0079
  have p0080 :=
    @gSylib
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.objMem b c))
      (.classMem (.cv y) (synCcompl (.cv z))) (.neg (.objMem y z)) p0077
      p0080_e01_recanon
  have p0081 :=
    @gSimp3l (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.classMem (.cv y) (synCcompl (.cv z)))
  have p0082 := @gElcompl (.cv y) (synCuni (.cv c)) p0078
  have p0083 :=
    @gSylib
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.neg (.classMem (.cv y) (synCuni (.cv c)))) p0081 p0082
  have p0084 := @gElunii (.cv y) (.cv b) (.cv c)
  have p0085_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objMem y b) (.objMem b c)) (.classMem (.cv y) (synCuni (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCuni synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @gExpcom (.objMem y b) (.objMem b c) (.classMem (.cv y) (synCuni (.cv c)))
      p0085_e00_recanon
  have p0086 :=
    @gCon3d (.objMem b c) (.objMem y b) (.classMem (.cv y) (synCuni (.cv c))) p0085
  have p0087 :=
    @gMpan9
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.neg (.classMem (.cv y) (synCuni (.cv c)))) (.objMem b c) (.neg (.objMem y b))
      p0083 p0086
  have p0088 := @gAdj11 (.cv z) (.cv b) (.cv y)
  have p0089_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.neg (.objMem y z)) (.neg (.objMem y b))) (synWb
          (.classEq (synCun (.cv z) (synCsn (.cv y))) (synCun (.cv b) (synCsn (.cv y))))
          (.objEq z b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb synCun synCnin synWnan synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0088
  have p0089 :=
    @gSyl2anc
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.objMem b c))
      (.neg (.objMem y z)) (.neg (.objMem y b))
      (synWb (.classEq (synCun (.cv z) (synCsn (.cv y))) (synCun (.cv b) (synCsn (.cv y))))
        (.objEq z b))
      p0080 p0087 p0089_e02_recanon
  have p0090 :=
    @gMtbird
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.objMem b c))
      (.classEq (synCun (.cv z) (synCsn (.cv y))) (synCun (.cv b) (synCsn (.cv y))))
      (.objEq z b) p0076 p0089
  have p0091_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem (.cv k) (synCnnc))
            (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
            (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
              (.classMem (.cv y) (synCcompl (.cv z))))) (.classMem (.cv b) (.cv c))) (.neg
          (.classEq (synCun (.cv z) (synCsn (.cv y)))
            (synCun (.cv b) (synCsn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synW3a synCnnc synCint synCun synCnin synWnan synCcompl
          synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0090
  have p0091 :=
    @gNrexdv
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.classEq (synCun (.cv z) (synCsn (.cv y))) (synCun (.cv b) (synCsn (.cv y)))) b
      (.cv c) dv_cache_0036 p0091_e00_recanon
  have p0092 :=
    @gEqeq1 (.cv x) (synCun (.cv z) (synCsn (.cv y)))
      (synCun (.cv b) (synCsn (.cv y)))
  have p0093 :=
    @gRexbidv (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y))))
      (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))
      (.classEq (synCun (.cv z) (synCsn (.cv y))) (synCun (.cv b) (synCsn (.cv y)))) b
      (.cv c) dv_cache_0037 p0092
  have p0094 :=
    @gElabg (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b (.cv c) (.classEq (synCun (.cv z) (synCsn (.cv y)))
          (synCun (.cv b) (synCsn (.cv y)))))
      x (synCun (.cv z) (synCsn (.cv y)))
      (.cab x (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      dv_cache_0038 dv_cache_0039 p0093
  have p0095 :=
    @gIbi
      (.classMem (synCun (.cv z) (synCsn (.cv y))) (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (synWrex b (.cv c) (.classEq (synCun (.cv z) (synCsn (.cv y)))
          (synCun (.cv b) (synCsn (.cv y)))))
      p0094
  have p0096 :=
    @gNsyl
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (synWrex b (.cv c) (.classEq (synCun (.cv z) (synCsn (.cv y)))
          (synCun (.cv b) (synCsn (.cv y)))))
      (.classMem (synCun (.cv z) (synCsn (.cv y))) (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0091 p0095
  have p0097 :=
    @gAdantr
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.neg (.classMem (synCun (.cv z) (synCsn (.cv y))) (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      p0096
  have p0098 := @gSnex (.cv y)
  have p0099 := @gUnex (.cv z) (synCsn (.cv y)) p0065 p0098
  have p0100 :=
    @gElsuci
      (.cab x (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cv k) (synCun (.cv z) (synCsn (.cv y))) p0099
  have p0101 :=
    @gSyl2anc
      (synWa (synW3a (.classMem (.cv k) (synCnnc))
          (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
          (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
            (.classMem (.cv y) (synCcompl (.cv z))))) (.classMem (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      (.neg (.classMem (synCun (.cv z) (synCsn (.cv y))) (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      (.classMem (synCun (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c)))
      p0070 p0097 p0100
  have p0102 :=
    @gEx
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (.cv z)))))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      (.classMem (synCun (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c)))
      p0101
  have p0103 :=
    @gSyl3an3b
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
        (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z))))))
      (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
        (.classMem (.cv y) (synCcompl (.cv z))))
      (.imp (.classMem (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0069 p0102
  have p0104 :=
    @gEmbantd
      (synW3a (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
        (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
          (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z)))))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
      (.classMem (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv k))
      (.classMem (synCun (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c)))
      p0064 p0103
  have p0105 :=
    @gN3expia (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
        (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z))))))
      (.imp (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0104
  have p0106 :=
    @gSyl5bi
      (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
          (synCcompl (synCuni (synCsn (.cv z))))))
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv c))))
        (.classMem (.cv y) (synCcompl (synCuni (synCsn (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))))
      (.imp (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0063 p0105
  have p0107 :=
    @gCom23
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))))
      (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
          (synCcompl (synCuni (synCsn (.cv z))))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      (.classMem (synCun (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c)))
      p0106
  have p0108 :=
    @gSyld
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))))
      (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv c)))) (.classMem (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv k)))
      (.imp (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
            (synCcompl (synCuni (synCsn (.cv z)))))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0062 p0107
  have p0109 :=
    @gImp
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))))
      (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
            (synCcompl (synCuni (synCsn (.cv z)))))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0108
  have p0110 :=
    @gAn32s (.classMem (.cv k) (synCnnc))
      (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c))))
      (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
            (synCcompl (synCuni (synCsn (.cv z)))))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0109
  have p0111 := @gUnieq (.cv a) (synCun (.cv c) (synCsn (.cv z)))
  have p0112 :=
    @gCompleqd (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z)))) (synCuni (.cv a))
      (synCuni (synCun (.cv c) (synCsn (.cv z)))) p0111
  have p0113 := @gUniun (.cv c) (synCsn (.cv z))
  have p0114 :=
    @gCompleqi (synCuni (synCun (.cv c) (synCsn (.cv z))))
      (synCun (synCuni (.cv c)) (synCuni (synCsn (.cv z)))) p0113
  have p0115 := @gIunin (synCuni (.cv c)) (synCuni (synCsn (.cv z)))
  have p0116 :=
    @gEqtri (synCcompl (synCuni (synCun (.cv c) (synCsn (.cv z)))))
      (synCcompl (synCun (synCuni (.cv c)) (synCuni (synCsn (.cv z)))))
      (synCin (synCcompl (synCuni (.cv c))) (synCcompl (synCuni (synCsn (.cv z)))))
      p0114 p0115
  have p0117 :=
    @gSyl6eq (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (synCcompl (synCuni (.cv a)))
      (synCcompl (synCuni (synCun (.cv c) (synCsn (.cv z)))))
      (synCin (synCcompl (synCuni (.cv c))) (synCcompl (synCuni (synCsn (.cv z)))))
      p0112 p0116
  have p0118 :=
    @gEleq2d (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (synCcompl (synCuni (.cv a)))
      (synCin (synCcompl (synCuni (.cv c))) (synCcompl (synCuni (synCsn (.cv z)))))
      (.cv y) p0117
  have p0119 :=
    @gRexeq (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv a)
      (synCun (.cv c) (synCsn (.cv z))) dv_cache_0022 dv_cache_0040
  have p0120 :=
    @gAbbidv (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b (synCun (.cv c) (synCsn (.cv z)))
        (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      x dv_cache_0041 p0119
  have p0121 :=
    @gUnab (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))) x
  have p0122 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x
      (synCun (.cv z) (synCsn (.cv y))) dv_cache_0038
  have p0123 :=
    @gUneq2i (synCsn (synCun (.cv z) (synCsn (.cv y))))
      (.cab x (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))))
      (.cab x (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      p0122
  have p0124 :=
    @gRexun (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv c)
      (synCsn (.cv z))
  have p0125 := @gUneq1 (.cv b) (.cv z) (synCsn (.cv y))
  have p0126_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq b z) (.classEq (synCun (.cv b) (synCsn (.cv y)))
          (synCun (.cv z) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0125
  have p0126 :=
    @gEqeq2d (.objEq b z) (synCun (.cv b) (synCsn (.cv y)))
      (synCun (.cv z) (synCsn (.cv y))) (.cv x) p0126_e00_recanon
  have p0127_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv z))
        (synWb (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))
          (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0126
  have p0127 :=
    @gRexsn (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))
      (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))) b (.cv z) dv_cache_0042
      dv_cache_0037 p0065 p0127_e01_recanon
  have p0128 :=
    @gOrbi2i
      (synWrex b (synCsn (.cv z)) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y))))
      (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) p0127
  have p0129 :=
    @gBitri
      (synWrex b (synCun (.cv c) (synCsn (.cv z)))
        (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWo (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
        (synWrex b (synCsn (.cv z)) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (synWo (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
        (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))))
      p0124 p0128
  have p0130 :=
    @gAbbii
      (synWrex b (synCun (.cv c) (synCsn (.cv z)))
        (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWo (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
        (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y)))))
      x p0129
  have p0131 :=
    @gN3eqtr4ri
      (synCun (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (.cab x (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y))))))
      (.cab x (synWo
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
          (.classEq (.cv x) (synCun (.cv z) (synCsn (.cv y))))))
      (synCun (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCsn (synCun (.cv z) (synCsn (.cv y)))))
      (.cab x (synWrex b (synCun (.cv c) (synCsn (.cv z)))
          (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      p0121 p0123 p0130
  have p0132 :=
    @gSyl6eq (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (.cab x (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cab x (synWrex b (synCun (.cv c) (synCsn (.cv z)))
          (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (synCun (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCsn (synCun (.cv z) (synCsn (.cv y)))))
      p0120 p0131
  have p0133 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (.cab x (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (synCun (.cab x
          (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCsn (synCun (.cv z) (synCsn (.cv y)))))
      (synCplc (.cv k) (synC1c)) p0132
  have p0134 :=
    @gImbi12d (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (.classMem (.cv y) (synCcompl (synCuni (.cv a))))
      (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
          (synCcompl (synCuni (synCsn (.cv z))))))
      (.classMem (.cab x
          (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
        (synCplc (.cv k) (synC1c)))
      (.classMem (synCun (.cab x
            (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c)))
      p0118 p0133
  have p0135 :=
    @gSyl5ibrcom
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k))))) (synWa (.objMem c k) (.classMem (.cv z) (synCcompl (.cv c)))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
            (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (.imp (.classMem (.cv y) (synCin (synCcompl (synCuni (.cv c)))
            (synCcompl (synCuni (synCsn (.cv z)))))) (.classMem (synCun (.cab x
              (synWrex b (.cv c) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCsn (synCun (.cv z) (synCsn (.cv y))))) (synCplc (.cv k) (synC1c))))
      p0110 p0134
  have p0136_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
              (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                    (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                  (.cv k)))))
          (synWa (.classMem (.cv c) (.cv k)) (.classMem (.cv z) (synCcompl (.cv c)))))
        (.imp (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
                (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (synCplc (.cv k) (synC1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCun synCnin synWnan synCcompl synCsn synWrex synWex
          synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0135
  have p0136 :=
    @gRexlimdvva
      (synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv k)))))
      (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
            (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      c z (.cv k) (synCcompl (.cv c)) dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0046 dv_cache_0047 dv_cache_0031 p0136_e00_recanon
  have p0137 :=
    @gSyl5bi (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
      (synWrex c (.cv k) (synWrex z (synCcompl (.cv c))
          (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv k)))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
            (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      p0052 p0136
  have p0138 :=
    @gRalrimiv
      (synWa (.classMem (.cv k) (synCnnc)) (synWral l (.cv k)
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv k)))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
            (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (synCplc (.cv k) (synC1c))))
      a (synCplc (.cv k) (synC1c)) dv_cache_0048 p0137
  have p0139 :=
    @gEx (.classMem (.cv k) (synCnnc))
      (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (synWral a (synCplc (.cv k) (synC1c))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c)))))
      p0138
  have p0140_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (synWb (synWral l (.cv n)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv n)))) (synWral l (.cv k)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral synCcompl synCnin synWnan synWa synCuni synWex
          synWrex synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0140 :=
    @gFinds
      (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      (.imp (.classMem (.cv y) (synCcompl (synCuni (synC0)))) (.all x (.neg
            (synWrex b (synC0) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      (synWral l (.cv k) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv k))))
      (synWral a (synCplc (.cv k) (synC1c))
        (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv a)))) (.classMem (.cab x
              (synWrex b (.cv a) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (synCplc (.cv k) (synC1c)))))
      (synWral l N (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)))
      n k N dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 p0008 p0030 p0140_e02_recanon p0045 p0048 p0051 p0139
  have p0141 := @gUnieq (.cv l) L
  have p0142 := @gCompleqd (.classEq (.cv l) L) (synCuni (.cv l)) (synCuni L) p0141
  have p0143 :=
    @gEleq2d (.classEq (.cv l) L) (synCcompl (synCuni (.cv l)))
      (synCcompl (synCuni L)) (.cv y) p0142
  have p0144 :=
    @gRexeq (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) b (.cv l) L
      dv_cache_0015 dv_cache_0056
  have p0145 :=
    @gAbbidv (.classEq (.cv l) L)
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
      (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) x
      dv_cache_0057 p0144
  have p0146 :=
    @gEleq1d (.classEq (.cv l) L)
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N
      p0145
  have p0147 :=
    @gImbi12d (.classEq (.cv l) L) (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.classMem (.cv y) (synCcompl (synCuni L)))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)
      (.classMem
        (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)
      p0143 p0146
  have p0148 :=
    @gRspccv
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N))
      (.imp (.classMem (.cv y) (synCcompl (synCuni L))) (.classMem
          (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N))
      l L N dv_cache_0058 dv_cache_0027 dv_cache_0059 p0147
  have p0149 :=
    @gSyl (.classMem N (synCnnc))
      (synWral l N (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)))
      (.imp (.classMem L N) (.imp (.classMem (.cv y) (synCcompl (synCuni L))) (.classMem
            (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)))
      p0140 p0148
  have p0150 :=
    @gCom3r (.classMem N (synCnnc)) (.classMem L N)
      (.classMem (.cv y) (synCcompl (synCuni L)))
      (.classMem
        (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)
      p0149
  have p0151 :=
    @gVtoclga
      (.imp (.classMem N (synCnnc)) (.imp (.classMem L N) (.classMem
            (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) N)))
      (.imp (.classMem N (synCnnc)) (.imp (.classMem L N) (.classMem
            (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N)))
      y X (synCcompl (synCuni L)) dv_cache_0060 dv_cache_0061 dv_cache_0062 p0007 p0150
  have p0152 :=
    @gCom3l (.classMem X (synCcompl (synCuni L))) (.classMem N (synCnnc))
      (.classMem L N)
      (.classMem (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N)
      p0151
  have p0153 :=
    @gN3imp (.classMem N (synCnnc)) (.classMem L N)
      (.classMem X (synCcompl (synCuni L)))
      (.classMem (.cab x (synWrex b L (.classEq (.cv x) (synCun (.cv b) (synCsn X))))) N)
      p0152
  exact p0153


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnadjoinpw`. -/
@[expose]
noncomputable def gNnadjoinpw (A : Class) (M : Class) (N : Class) (X : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
        (.classMem (synCpw (synCun A (synCsn X))) (synCplc N N))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ N.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
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
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_X : b ∉ X.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have dv_cache_0001 : a ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0003 : a ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_X, not_false_eq_true])
  have dv_cache_0004 : b ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_X, not_false_eq_true])
  have dv_cache_0005 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0006 : b ∉ ((synCpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_b_not_A,
          not_false_eq_true])
  have dv_cache_0007 : a ∉ ((synCpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_a_not_A,
          not_false_eq_true])
  have dv_cache_0008 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0009 :
    b ∉
      ((synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem A M) (.classMem X (synCcompl A)))
          (.classMem (synCpw A) N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_N, fresh_b_not_M, fresh_b_not_X,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synCpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_t_not_A,
          not_false_eq_true])
  have dv_cache_0011 :
    t ∉
      ((Class.cab a (synWrex b (synCpw A)
            (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_a,
          fresh_t_ne_b, fresh_t_not_X, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.objEq a t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_t, or_false, not_false_eq_true])
  have dv_cache_0013 :
    a ∉ ((synWrex b (synCpw A) (.classEq (.cv t) (synCun (.cv b) (synCsn X))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_t,
          fresh_a_ne_b, fresh_a_not_X, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 : t ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show t ≠ a from (by exact fresh_t_ne_a))
  have dv_cache_0015 : b ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ t from (by exact fresh_b_ne_t))
  have dv_cache_0016 : t ∉ ((synCun (.cv b) (synCsn X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_not_X, or_false, not_false_eq_true])
  have dv_cache_0017 :
    t ∉ ((Wff.neg (.classMem (synCun (.cv b) (synCsn X)) (synCpw A)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_not_X, fresh_t_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Wff.neg (.classMem (.cv t) (synCpw A)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_t, fresh_b_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @gPwadjoin A X a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gSimp3 (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N)
  have p0002 :=
    @gSimp1r (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N)
  have p0003 :=
    @gSimp2r (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) (.classMem A M)
      (.classMem X (synCcompl A)) (.classMem (synCpw A) N)
  have p0004 := @gUnipw A
  have p0005 := @gCompleqi (synCuni (synCpw A)) A p0004
  have p0006 :=
    @gSyl6eleqr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      X (synCcompl A) (synCcompl (synCuni (synCpw A))) p0003 p0005
  have p0007 :=
    @gNnadjoin a (synCpw A) N X b dv_cache_0006 dv_cache_0007 dv_cache_0004
      dv_cache_0003 dv_cache_0008
  have p0008 :=
    @gSyl3anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.classMem N (synCnnc)) (.classMem (synCpw A) N)
      (.classMem X (synCcompl (synCuni (synCpw A))))
      (.classMem
        (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))) N)
      p0002 p0001 p0006 p0007
  have p0009 := @gElcomplg X A (synCcompl A)
  have p0010 := @gIbi (.classMem X (synCcompl A)) (.neg (.classMem X A)) p0009
  have p0011 :=
    @gSyl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.classMem X (synCcompl A)) (.neg (.classMem X A)) p0003 p0010
  have p0012 := @gSnssg X A (synCcompl A)
  have p0013 :=
    @gSyl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.classMem X (synCcompl A)) (synWb (.classMem X A) (synWss (synCsn X) A)) p0003
      p0012
  have p0014 :=
    @gMtbid
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.classMem X A) (synWss (synCsn X) A) p0011 p0013
  have p0015 :=
    @gIntnand
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (synWss (synCsn X) A) (synWss (.cv b) A) p0014
  have p0016 :=
    @gRalrimivw
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.neg (synWa (synWss (.cv b) A) (synWss (synCsn X) A))) b (synCpw A)
      dv_cache_0009 p0015
  have p0017 :=
    @gDisjr t (synCpw A)
      (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))
      dv_cache_0010 dv_cache_0011
  have p0018 := @gEqeq1 (.cv a) (.cv t) (synCun (.cv b) (synCsn X))
  have p0019_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a t) (synWb (.classEq (.cv a) (synCun (.cv b) (synCsn X)))
          (.classEq (.cv t) (synCun (.cv b) (synCsn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCsn
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @gRexbidv (.objEq a t) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))
      (.classEq (.cv t) (synCun (.cv b) (synCsn X))) b (synCpw A) dv_cache_0012
      p0019_e00_recanon
  have p0020 :=
    @gRalab (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))
      (synWrex b (synCpw A) (.classEq (.cv t) (synCun (.cv b) (synCsn X))))
      (.neg (.classMem (.cv t) (synCpw A))) t a dv_cache_0013 dv_cache_0014 p0019
  have p0021 :=
    @gRalcom4
      (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
        (.neg (.classMem (.cv t) (synCpw A))))
      b t (synCpw A) dv_cache_0010 dv_cache_0015
  have p0022 := @gVex b
  have p0023 := @gSnex X
  have p0024 := @gUnex (.cv b) (synCsn X) p0022 p0023
  have p0025 := @gEleq1 (.cv t) (synCun (.cv b) (synCsn X)) (synCpw A)
  have p0026 :=
    @gNotbid (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
      (.classMem (.cv t) (synCpw A))
      (.classMem (synCun (.cv b) (synCsn X)) (synCpw A)) p0025
  have p0027 :=
    @gCeqsalv (.neg (.classMem (.cv t) (synCpw A)))
      (.neg (.classMem (synCun (.cv b) (synCsn X)) (synCpw A))) t
      (synCun (.cv b) (synCsn X)) dv_cache_0016 dv_cache_0017 p0024 p0026
  have p0028 := @gElpw (synCun (.cv b) (synCsn X)) A p0024
  have p0029 := @gUnss (.cv b) (synCsn X) A
  have p0030 :=
    @gBitr4i (.classMem (synCun (.cv b) (synCsn X)) (synCpw A))
      (synWss (synCun (.cv b) (synCsn X)) A)
      (synWa (synWss (.cv b) A) (synWss (synCsn X) A)) p0028 p0029
  have p0031 :=
    @gXchbinx
      (.all t (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
          (.neg (.classMem (.cv t) (synCpw A)))))
      (.classMem (synCun (.cv b) (synCsn X)) (synCpw A))
      (synWa (synWss (.cv b) A) (synWss (synCsn X) A)) p0027 p0030
  have p0032 :=
    @gRalbii
      (.all t (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
          (.neg (.classMem (.cv t) (synCpw A)))))
      (.neg (synWa (synWss (.cv b) A) (synWss (synCsn X) A))) b (synCpw A) p0031
  have p0033 :=
    @gR1923v (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
      (.neg (.classMem (.cv t) (synCpw A))) b (synCpw A) dv_cache_0018
  have p0034 :=
    @gAlbii
      (synWral b (synCpw A) (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
          (.neg (.classMem (.cv t) (synCpw A)))))
      (.imp (synWrex b (synCpw A) (.classEq (.cv t) (synCun (.cv b) (synCsn X))))
        (.neg (.classMem (.cv t) (synCpw A))))
      t p0033
  have p0035 :=
    @gN3bitr3ri
      (synWral b (synCpw A) (.all t (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
            (.neg (.classMem (.cv t) (synCpw A))))))
      (.all t (synWral b (synCpw A) (.imp (.classEq (.cv t) (synCun (.cv b) (synCsn X)))
            (.neg (.classMem (.cv t) (synCpw A))))))
      (synWral b (synCpw A) (.neg (synWa (synWss (.cv b) A) (synWss (synCsn X) A))))
      (.all t (.imp (synWrex b (synCpw A) (.classEq (.cv t) (synCun (.cv b) (synCsn X))))
          (.neg (.classMem (.cv t) (synCpw A)))))
      p0021 p0032 p0034
  have p0036 :=
    @gN3bitri
      (.classEq (synCin (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
        (synC0))
      (synWral t
        (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))
        (.neg (.classMem (.cv t) (synCpw A))))
      (.all t (.imp (synWrex b (synCpw A) (.classEq (.cv t) (synCun (.cv b) (synCsn X))))
          (.neg (.classMem (.cv t) (synCpw A)))))
      (synWral b (synCpw A) (.neg (synWa (synWss (.cv b) A) (synWss (synCsn X) A))))
      p0017 p0020 p0035
  have p0037 :=
    @gSylibr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (synWral b (synCpw A) (.neg (synWa (synWss (.cv b) A) (synWss (synCsn X) A))))
      (.classEq (synCin (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
        (synC0))
      p0016 p0036
  have p0038 :=
    @gEladdci (synCpw A)
      (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))) N
      N
  have p0039 :=
    @gSyl3anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (.classMem (synCpw A) N)
      (.classMem
        (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))) N)
      (.classEq (synCin (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
        (synC0))
      (.classMem (synCun (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
        (synCplc N N))
      p0001 p0008 p0037 p0038
  have p0040 :=
    @gSyl5eqel
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem X (synCcompl A))) (.classMem (synCpw A) N))
      (synCpw (synCun A (synCsn X)))
      (synCun (synCpw A) (.cab a
          (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
      (synCplc N N) p0000 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end
