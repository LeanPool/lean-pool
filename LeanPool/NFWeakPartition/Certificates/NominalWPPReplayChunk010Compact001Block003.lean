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

@[expose]
noncomputable def g_nnadjoin (x : Var) (L : Class) (N : Class) (X : Class) (b : Var)
    (dv_L_b : b ∉ L.fv) (dv_L_x : x ∉ L.fv) (dv_X_b : b ∉ X.fv) (dv_X_x : x ∉ X.fv)
    (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem N (syn_cnnc)) (.classMem L N)
          (.classMem X (syn_ccompl (syn_cuni L)))) (.classMem
          (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N)) :=
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
  have dv_cache_0014 : l ∉ ((syn_c0c)).fv :=
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
  have dv_cache_0016 : b ∉ ((syn_c0)).fv :=
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
  have dv_cache_0017 : x ∉ ((Wff.classEq (.cv l) (syn_c0))).fv :=
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
  have dv_cache_0018 : l ∉ ((syn_c0)).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
              (syn_wrex b (syn_c0)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))).fv :=
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
  have dv_cache_0021 : l ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
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
  have dv_cache_0024 : a ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
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
      ((syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z)))))).fv :=
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
    b ∉ ((Wff.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y))))).fv :=
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
  have dv_cache_0038 : x ∉ ((syn_cun (.cv z) (syn_csn (.cv y)))).fv :=
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
      ((syn_wrex b (.cv c) (.classEq (syn_cun (.cv z) (syn_csn (.cv y)))
            (syn_cun (.cv b) (syn_csn (.cv y)))))).fv :=
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
  have dv_cache_0040 : b ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv :=
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
    x ∉ ((Wff.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c))))).fv :=
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
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
      ((syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
              (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))).fv :=
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
      ((syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
              (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
              (syn_wrex b (syn_c0)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))).fv :=
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
      ((syn_wral l N (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
              (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)))).fv :=
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
      ((syn_wral a (syn_cplc (.cv k) (syn_c1c))
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
                (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (syn_cplc (.cv k) (syn_c1c)))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (syn_ccompl (syn_cuni L))) (.classMem
            (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
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
  have dv_cache_0061 : y ∉ ((syn_ccompl (syn_cuni L))).fv :=
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
      ((Wff.imp (.classMem N (syn_cnnc)) (.imp (.classMem L N) (.classMem
              (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X)))))
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
  have p0000 := @g_sneq (.cv y) X
  have p0001 := @g_uneq2d (.classEq (.cv y) X) (syn_csn (.cv y)) (syn_csn X) (.cv b) p0000
  have p0002 :=
    @g_eqeq2d (.classEq (.cv y) X) (syn_cun (.cv b) (syn_csn (.cv y)))
      (syn_cun (.cv b) (syn_csn X)) (.cv x) p0001
  have p0003 :=
    @g_rexbidv (.classEq (.cv y) X) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))) b L dv_cache_0001 p0002
  have p0004 :=
    @g_abbidv (.classEq (.cv y) X)
      (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X)))) x dv_cache_0002
      p0003
  have p0005 :=
    @g_eleq1d (.classEq (.cv y) X)
      (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N p0004
  have p0006 :=
    @g_imbi2d (.classEq (.cv y) X)
      (.classMem
        (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)
      (.classMem (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N)
      (.classMem L N) p0005
  have p0007 :=
    @g_imbi2d (.classEq (.cv y) X)
      (.imp (.classMem L N) (.classMem
          (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N))
      (.imp (.classMem L N) (.classMem
          (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N))
      (.classMem N (syn_cnnc)) p0006
  have p0008 :=
    @g_nnadjoinlem1 x y n b l dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @g_eleq2 (.cv n) (syn_c0c)
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0010 :=
    @g_el0c
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0011 :=
    @g_ab0 (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) x
  have p0012 :=
    @g_bitri
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_c0c))
      (.classEq (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (syn_c0))
      (.all x (.neg
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0010 p0011
  have p0013 :=
    @g_syl6bb (.classEq (.cv n) (syn_c0c))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_c0c))
      (.all x (.neg
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0009 p0012
  have p0014 :=
    @g_imbi2d (.classEq (.cv n) (syn_c0c))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.all x (.neg
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) p0013
  have p0015 :=
    @g_raleqbi1dv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      l (.cv n) (syn_c0c) dv_cache_0013 dv_cache_0014 p0014
  have p0016 :=
    (Nominal.biimpRefl (syn_wral l (syn_c0c)
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))))
  have p0017 := @g_el0c (.cv l)
  have p0018 :=
    @g_imbi1i (.classMem (.cv l) (syn_c0c)) (.classEq (.cv l) (syn_c0))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      p0017
  have p0019 :=
    @g_albii
      (.imp (.classMem (.cv l) (syn_c0c))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))))
      (.imp (.classEq (.cv l) (syn_c0))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))))
      l p0018
  have p0020 := @g_n_0ex
  have p0021 := @g_unieq (.cv l) (syn_c0)
  have p0022 :=
    @g_compleqd (.classEq (.cv l) (syn_c0)) (syn_cuni (.cv l)) (syn_cuni (syn_c0)) p0021
  have p0023 :=
    @g_eleq2d (.classEq (.cv l) (syn_c0)) (syn_ccompl (syn_cuni (.cv l)))
      (syn_ccompl (syn_cuni (syn_c0))) (.cv y) p0022
  have p0024 :=
    @g_rexeq (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv l) (syn_c0)
      dv_cache_0015 dv_cache_0016
  have p0025 :=
    @g_notbid (.classEq (.cv l) (syn_c0))
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) p0024
  have p0026 :=
    @g_albidv (.classEq (.cv l) (syn_c0))
      (.neg (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.neg (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      x dv_cache_0017 p0025
  have p0027 :=
    @g_imbi12d (.classEq (.cv l) (syn_c0))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0))))
      (.all x (.neg
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.all x (.neg
          (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0023 p0026
  have p0028 :=
    @g_ceqsalv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
            (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      l (syn_c0) dv_cache_0018 dv_cache_0019 p0020 p0027
  have p0029 :=
    @g_n_3bitrri
      (syn_wral l (syn_c0c) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x
            (.neg (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))))
      (.all l (.imp (.classMem (.cv l) (syn_c0c))
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))))
      (.all l (.imp (.classEq (.cv l) (syn_c0))
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x (.neg
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
            (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      p0016 p0019 p0028
  have p0030 :=
    @g_syl6bbr (.classEq (.cv n) (syn_c0c))
      (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      (syn_wral l (syn_c0c) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.all x
            (.neg (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
            (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      p0015 p0029
  have p0031 :=
    @g_eleq2 (.cv n) (.cv k)
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (syn_wb (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n)) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_imbi2d (.objEq n k)
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) p0032_e00_recanon
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv k)) (syn_wb
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv n))) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
              (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa syn_cuni syn_wex syn_wrex
          syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @g_raleqbi1dv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      l (.cv n) (.cv k) dv_cache_0013 dv_cache_0020 p0033_e00_recanon
  have p0034 :=
    @g_eleq2 (.cv n) (syn_cplc (.cv k) (syn_c1c))
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0035 :=
    @g_imbi2d (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) p0034
  have p0036 :=
    @g_raleqbi1dv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      l (.cv n) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0013 dv_cache_0021 p0035
  have p0037 := @g_unieq (.cv l) (.cv a)
  have p0038_e00_recanon :
    Nominal.NPrf (.imp (.objEq l a) (.classEq (syn_cuni (.cv l)) (syn_cuni (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @g_compleqd (.objEq l a) (syn_cuni (.cv l)) (syn_cuni (.cv a)) p0038_e00_recanon
  have p0039 :=
    @g_eleq2d (.objEq l a) (syn_ccompl (syn_cuni (.cv l))) (syn_ccompl (syn_cuni (.cv a)))
      (.cv y) p0038
  have p0040 :=
    @g_rexeq (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv l) (.cv a)
      dv_cache_0015 dv_cache_0022
  have p0041_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq l a) (syn_wb
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
          (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0040
  have p0041 :=
    @g_abbidv (.objEq l a)
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) x
      dv_cache_0023 p0041_e00_recanon
  have p0042 :=
    @g_eleq1d (.objEq l a)
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cab x (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (syn_cplc (.cv k) (syn_c1c)) p0041
  have p0043 :=
    @g_imbi12d (.objEq l a) (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a))))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (.cab x
          (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_cplc (.cv k) (syn_c1c)))
      p0039 p0042
  have p0044 :=
    @g_cbvralv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
            (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      l a (syn_cplc (.cv k) (syn_c1c)) dv_cache_0021 dv_cache_0024 dv_cache_0025
      dv_cache_0026 p0043
  have p0045 :=
    @g_syl6bb (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      (syn_wral l (syn_cplc (.cv k) (syn_c1c))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c)))))
      (syn_wral a (syn_cplc (.cv k) (syn_c1c))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c)))))
      p0036 p0044
  have p0046 :=
    @g_eleq2 (.cv n) N
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0047 :=
    @g_imbi2d (.classEq (.cv n) N)
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) p0046
  have p0048 :=
    @g_raleqbi1dv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N))
      l (.cv n) N dv_cache_0013 dv_cache_0027 p0047
  have p0049 := @g_rex0 (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b
  have p0050 := Nominal.gen p0049 x
  have p0051 :=
    @g_a1i
      (.all x (.neg
          (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) p0050
  have p0052 :=
    @g_elsuc z (.cv a) (.cv k) c dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
  have p0053 := @g_unieq (.cv l) (.cv c)
  have p0054_e00_recanon :
    Nominal.NPrf (.imp (.objEq l c) (.classEq (syn_cuni (.cv l)) (syn_cuni (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0053
  have p0054 :=
    @g_compleqd (.objEq l c) (syn_cuni (.cv l)) (syn_cuni (.cv c)) p0054_e00_recanon
  have p0055 :=
    @g_eleq2d (.objEq l c) (syn_ccompl (syn_cuni (.cv l))) (syn_ccompl (syn_cuni (.cv c)))
      (.cv y) p0054
  have p0056 :=
    @g_rexeq (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv l) (.cv c)
      dv_cache_0015 dv_cache_0032
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq l c) (syn_wb
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @g_abbidv (.objEq l c)
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) x
      dv_cache_0033 p0057_e00_recanon
  have p0058 :=
    @g_eleq1d (.objEq l c)
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cab x (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cv k) p0057
  have p0059 :=
    @g_imbi12d (.objEq l c) (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      p0055 p0058
  have p0060_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv l) (.cv c)) (syn_wb
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv k))) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem
              (.cab x (syn_wrex b (.cv c)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa syn_cuni syn_wex syn_wrex
          syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0059
  have p0060 :=
    @g_rspcv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      l (.cv c) (.cv k) dv_cache_0034 dv_cache_0020 dv_cache_0035 p0060_e00_recanon
  have p0061_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem c k) (.imp (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv k)))) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem
              (.cab x (syn_wrex b (.cv c)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_ccompl syn_cnin syn_wnan syn_wa syn_cuni syn_wex syn_wrex
          syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @g_adantr (.objMem c k)
      (.imp (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (.classMem (.cv z) (syn_ccompl (.cv c))) p0061_e00_recanon
  have p0062 :=
    @g_adantl (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (.imp (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (.classMem (.cv k) (syn_cnnc)) p0061
  have p0063 :=
    @g_elin (.cv y) (syn_ccompl (syn_cuni (.cv c)))
      (syn_ccompl (syn_cuni (syn_csn (.cv z))))
  have p0064 :=
    @g_simp3l (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))
  have p0065 := @g_vex z
  have p0066 := @g_unisn (.cv z) p0065
  have p0067 := @g_compleqi (syn_cuni (syn_csn (.cv z))) (.cv z) p0066
  have p0068 :=
    @g_eleq2i (syn_ccompl (syn_cuni (syn_csn (.cv z)))) (syn_ccompl (.cv z)) (.cv y) p0067
  have p0069 :=
    @g_anbi2i (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))
      (.classMem (.cv y) (syn_ccompl (.cv z)))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) p0068
  have p0070 :=
    @g_simpr
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
  have p0071 :=
    @g_simpl2r (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
        (.classMem (.cv y) (syn_ccompl (.cv z))))
      (.objMem b c)
  have p0072 := @g_elcompl (.cv z) (.cv c) p0065
  have p0073_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_ccompl (.cv c))) (.neg (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_sylib
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.objMem b c))
      (.classMem (.cv z) (syn_ccompl (.cv c))) (.neg (.objMem z c)) p0071
      p0073_e01_recanon
  have p0074 := @g_eleq1a (.cv b) (.cv c) (.cv z)
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
    @g_adantl (.objMem b c) (.imp (.objEq z b) (.objMem z c))
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      p0075_e00_recanon
  have p0076 :=
    @g_mtod
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.objMem b c))
      (.objEq z b) (.objMem z c) p0073 p0075
  have p0077 :=
    @g_simpl3r (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.classMem (.cv y) (syn_ccompl (.cv z))) (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))) (.objMem b c)
  have p0078 := @g_vex y
  have p0079 := @g_elcompl (.cv y) (.cv z) p0078
  have p0080_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_ccompl (.cv z))) (.neg (.objMem y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_sylib
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.objMem b c))
      (.classMem (.cv y) (syn_ccompl (.cv z))) (.neg (.objMem y z)) p0077
      p0080_e01_recanon
  have p0081 :=
    @g_simp3l (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.classMem (.cv y) (syn_ccompl (.cv z)))
  have p0082 := @g_elcompl (.cv y) (syn_cuni (.cv c)) p0078
  have p0083 :=
    @g_sylib
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.neg (.classMem (.cv y) (syn_cuni (.cv c)))) p0081 p0082
  have p0084 := @g_elunii (.cv y) (.cv b) (.cv c)
  have p0085_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objMem y b) (.objMem b c)) (.classMem (.cv y) (syn_cuni (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cuni syn_wex
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
    @g_expcom (.objMem y b) (.objMem b c) (.classMem (.cv y) (syn_cuni (.cv c)))
      p0085_e00_recanon
  have p0086 :=
    @g_con3d (.objMem b c) (.objMem y b) (.classMem (.cv y) (syn_cuni (.cv c))) p0085
  have p0087 :=
    @g_mpan9
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.neg (.classMem (.cv y) (syn_cuni (.cv c)))) (.objMem b c) (.neg (.objMem y b))
      p0083 p0086
  have p0088 := @g_adj11 (.cv z) (.cv b) (.cv y)
  have p0089_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.neg (.objMem y z)) (.neg (.objMem y b))) (syn_wb
          (.classEq (syn_cun (.cv z) (syn_csn (.cv y))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.objEq z b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
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
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.objMem b c))
      (.neg (.objMem y z)) (.neg (.objMem y b))
      (syn_wb (.classEq (syn_cun (.cv z) (syn_csn (.cv y))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.objEq z b))
      p0080 p0087 p0089_e02_recanon
  have p0090 :=
    @g_mtbird
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.objMem b c))
      (.classEq (syn_cun (.cv z) (syn_csn (.cv y))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.objEq z b) p0076 p0089
  have p0091_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
            (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
            (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
              (.classMem (.cv y) (syn_ccompl (.cv z))))) (.classMem (.cv b) (.cv c))) (.neg
          (.classEq (syn_cun (.cv z) (syn_csn (.cv y)))
            (syn_cun (.cv b) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_w3a syn_cnnc syn_cint syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn
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
    @g_nrexdv
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.classEq (syn_cun (.cv z) (syn_csn (.cv y))) (syn_cun (.cv b) (syn_csn (.cv y)))) b
      (.cv c) dv_cache_0036 p0091_e00_recanon
  have p0092 :=
    @g_eqeq1 (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))
      (syn_cun (.cv b) (syn_csn (.cv y)))
  have p0093 :=
    @g_rexbidv (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y))))
      (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.classEq (syn_cun (.cv z) (syn_csn (.cv y))) (syn_cun (.cv b) (syn_csn (.cv y)))) b
      (.cv c) dv_cache_0037 p0092
  have p0094 :=
    @g_elabg (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b (.cv c) (.classEq (syn_cun (.cv z) (syn_csn (.cv y)))
          (syn_cun (.cv b) (syn_csn (.cv y)))))
      x (syn_cun (.cv z) (syn_csn (.cv y)))
      (.cab x (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      dv_cache_0038 dv_cache_0039 p0093
  have p0095 :=
    @g_ibi
      (.classMem (syn_cun (.cv z) (syn_csn (.cv y))) (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (syn_wrex b (.cv c) (.classEq (syn_cun (.cv z) (syn_csn (.cv y)))
          (syn_cun (.cv b) (syn_csn (.cv y)))))
      p0094
  have p0096 :=
    @g_nsyl
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (syn_wrex b (.cv c) (.classEq (syn_cun (.cv z) (syn_csn (.cv y)))
          (syn_cun (.cv b) (syn_csn (.cv y)))))
      (.classMem (syn_cun (.cv z) (syn_csn (.cv y))) (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0091 p0095
  have p0097 :=
    @g_adantr
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.neg (.classMem (syn_cun (.cv z) (syn_csn (.cv y))) (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      p0096
  have p0098 := @g_snex (.cv y)
  have p0099 := @g_unex (.cv z) (syn_csn (.cv y)) p0065 p0098
  have p0100 :=
    @g_elsuci
      (.cab x (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cv k) (syn_cun (.cv z) (syn_csn (.cv y))) p0099
  have p0101 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
          (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
            (.classMem (.cv y) (syn_ccompl (.cv z))))) (.classMem (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      (.neg (.classMem (syn_cun (.cv z) (syn_csn (.cv y))) (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      (.classMem (syn_cun (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c)))
      p0070 p0097 p0100
  have p0102 :=
    @g_ex
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (.cv z)))))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      (.classMem (syn_cun (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c)))
      p0101
  have p0103 :=
    @g_syl3an3b
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
        (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
        (.classMem (.cv y) (syn_ccompl (.cv z))))
      (.imp (.classMem (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0069 p0102
  have p0104 :=
    @g_embantd
      (syn_w3a (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
        (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
          (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
      (.classMem (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv k))
      (.classMem (syn_cun (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c)))
      p0064 p0103
  have p0105 :=
    @g_n_3expia (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
        (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (.imp (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0104
  have p0106 :=
    @g_syl5bi
      (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
          (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c))))
        (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))))
      (.imp (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0063 p0105
  have p0107 :=
    @g_com23
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))))
      (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
          (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      (.classMem (syn_cun (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c)))
      p0106
  have p0108 :=
    @g_syld
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))))
      (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv c)))) (.classMem (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv k)))
      (.imp (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
            (syn_ccompl (syn_cuni (syn_csn (.cv z)))))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0062 p0107
  have p0109 :=
    @g_imp
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))))
      (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
            (syn_ccompl (syn_cuni (syn_csn (.cv z)))))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0108
  have p0110 :=
    @g_an32s (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c))))
      (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (.imp (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
            (syn_ccompl (syn_cuni (syn_csn (.cv z)))))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0109
  have p0111 := @g_unieq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z)))
  have p0112 :=
    @g_compleqd (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z)))) (syn_cuni (.cv a))
      (syn_cuni (syn_cun (.cv c) (syn_csn (.cv z)))) p0111
  have p0113 := @g_uniun (.cv c) (syn_csn (.cv z))
  have p0114 :=
    @g_compleqi (syn_cuni (syn_cun (.cv c) (syn_csn (.cv z))))
      (syn_cun (syn_cuni (.cv c)) (syn_cuni (syn_csn (.cv z)))) p0113
  have p0115 := @g_iunin (syn_cuni (.cv c)) (syn_cuni (syn_csn (.cv z)))
  have p0116 :=
    @g_eqtri (syn_ccompl (syn_cuni (syn_cun (.cv c) (syn_csn (.cv z)))))
      (syn_ccompl (syn_cun (syn_cuni (.cv c)) (syn_cuni (syn_csn (.cv z)))))
      (syn_cin (syn_ccompl (syn_cuni (.cv c))) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))
      p0114 p0115
  have p0117 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (syn_ccompl (syn_cuni (.cv a)))
      (syn_ccompl (syn_cuni (syn_cun (.cv c) (syn_csn (.cv z)))))
      (syn_cin (syn_ccompl (syn_cuni (.cv c))) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))
      p0112 p0116
  have p0118 :=
    @g_eleq2d (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (syn_ccompl (syn_cuni (.cv a)))
      (syn_cin (syn_ccompl (syn_cuni (.cv c))) (syn_ccompl (syn_cuni (syn_csn (.cv z)))))
      (.cv y) p0117
  have p0119 :=
    @g_rexeq (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv a)
      (syn_cun (.cv c) (syn_csn (.cv z))) dv_cache_0022 dv_cache_0040
  have p0120 :=
    @g_abbidv (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b (syn_cun (.cv c) (syn_csn (.cv z)))
        (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      x dv_cache_0041 p0119
  have p0121 :=
    @g_unab (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))) x
  have p0122 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x
      (syn_cun (.cv z) (syn_csn (.cv y))) dv_cache_0038
  have p0123 :=
    @g_uneq2i (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))
      (.cab x (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))))
      (.cab x (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      p0122
  have p0124 :=
    @g_rexun (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv c)
      (syn_csn (.cv z))
  have p0125 := @g_uneq1 (.cv b) (.cv z) (syn_csn (.cv y))
  have p0126_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq b z) (.classEq (syn_cun (.cv b) (syn_csn (.cv y)))
          (syn_cun (.cv z) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0125
  have p0126 :=
    @g_eqeq2d (.objEq b z) (syn_cun (.cv b) (syn_csn (.cv y)))
      (syn_cun (.cv z) (syn_csn (.cv y))) (.cv x) p0126_e00_recanon
  have p0127_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv z))
        (syn_wb (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0126
  have p0127 :=
    @g_rexsn (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))) b (.cv z) dv_cache_0042
      dv_cache_0037 p0065 p0127_e01_recanon
  have p0128 :=
    @g_orbi2i
      (syn_wrex b (syn_csn (.cv z)) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y))))
      (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) p0127
  have p0129 :=
    @g_bitri
      (syn_wrex b (syn_cun (.cv c) (syn_csn (.cv z)))
        (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wo (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
        (syn_wrex b (syn_csn (.cv z)) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (syn_wo (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
        (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))))
      p0124 p0128
  have p0130 :=
    @g_abbii
      (syn_wrex b (syn_cun (.cv c) (syn_csn (.cv z)))
        (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wo (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
        (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y)))))
      x p0129
  have p0131 :=
    @g_n_3eqtr4ri
      (syn_cun (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (.cab x (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y))))))
      (.cab x (syn_wo
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
          (.classEq (.cv x) (syn_cun (.cv z) (syn_csn (.cv y))))))
      (syn_cun (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_csn (syn_cun (.cv z) (syn_csn (.cv y)))))
      (.cab x (syn_wrex b (syn_cun (.cv c) (syn_csn (.cv z)))
          (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      p0121 p0123 p0130
  have p0132 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (.cab x (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cab x (syn_wrex b (syn_cun (.cv c) (syn_csn (.cv z)))
          (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (syn_cun (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_csn (syn_cun (.cv z) (syn_csn (.cv y)))))
      p0120 p0131
  have p0133 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (.cab x (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (syn_cun (.cab x
          (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_csn (syn_cun (.cv z) (syn_csn (.cv y)))))
      (syn_cplc (.cv k) (syn_c1c)) p0132
  have p0134 :=
    @g_imbi12d (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a))))
      (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
          (syn_ccompl (syn_cuni (syn_csn (.cv z))))))
      (.classMem (.cab x
          (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
        (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (syn_cun (.cab x
            (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c)))
      p0118 p0133
  have p0135 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv k))))) (syn_wa (.objMem c k) (.classMem (.cv z) (syn_ccompl (.cv c)))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
            (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (.imp (.classMem (.cv y) (syn_cin (syn_ccompl (syn_cuni (.cv c)))
            (syn_ccompl (syn_cuni (syn_csn (.cv z)))))) (.classMem (syn_cun (.cab x
              (syn_wrex b (.cv c) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_csn (syn_cun (.cv z) (syn_csn (.cv y))))) (syn_cplc (.cv k) (syn_c1c))))
      p0110 p0134
  have p0136_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
              (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                    (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                  (.cv k)))))
          (syn_wa (.classMem (.cv c) (.cv k)) (.classMem (.cv z) (syn_ccompl (.cv c)))))
        (.imp (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
                (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (syn_cplc (.cv k) (syn_c1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_wrex syn_wex
          syn_cplc syn_c1c
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
    @g_rexlimdvva
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv k)))))
      (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
            (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      c z (.cv k) (syn_ccompl (.cv c)) dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0046 dv_cache_0047 dv_cache_0031 p0136_e00_recanon
  have p0137 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wrex c (.cv k) (syn_wrex z (syn_ccompl (.cv c))
          (.classEq (.cv a) (syn_cun (.cv c) (syn_csn (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv k)))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
            (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      p0052 p0136
  have p0138 :=
    @g_ralrimiv
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral l (.cv k)
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv k)))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
            (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (syn_cplc (.cv k) (syn_c1c))))
      a (syn_cplc (.cv k) (syn_c1c)) dv_cache_0048 p0137
  have p0139 :=
    @g_ex (.classMem (.cv k) (syn_cnnc))
      (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (syn_wral a (syn_cplc (.cv k) (syn_c1c))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c)))))
      p0138
  have p0140_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (syn_wb (syn_wral l (.cv n)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv n)))) (syn_wral l (.cv k)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral syn_ccompl syn_cnin syn_wnan syn_wa syn_cuni syn_wex
          syn_wrex syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0140 :=
    @g_finds
      (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (syn_c0)))) (.all x (.neg
            (syn_wrex b (syn_c0) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      (syn_wral l (.cv k) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv k))))
      (syn_wral a (syn_cplc (.cv k) (syn_c1c))
        (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv a)))) (.classMem (.cab x
              (syn_wrex b (.cv a) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (syn_cplc (.cv k) (syn_c1c)))))
      (syn_wral l N (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)))
      n k N dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 p0008 p0030 p0140_e02_recanon p0045 p0048 p0051 p0139
  have p0141 := @g_unieq (.cv l) L
  have p0142 := @g_compleqd (.classEq (.cv l) L) (syn_cuni (.cv l)) (syn_cuni L) p0141
  have p0143 :=
    @g_eleq2d (.classEq (.cv l) L) (syn_ccompl (syn_cuni (.cv l)))
      (syn_ccompl (syn_cuni L)) (.cv y) p0142
  have p0144 :=
    @g_rexeq (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) b (.cv l) L
      dv_cache_0015 dv_cache_0056
  have p0145 :=
    @g_abbidv (.classEq (.cv l) L)
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
      (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) x
      dv_cache_0057 p0144
  have p0146 :=
    @g_eleq1d (.classEq (.cv l) L)
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N
      p0145
  have p0147 :=
    @g_imbi12d (.classEq (.cv l) L) (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.classMem (.cv y) (syn_ccompl (syn_cuni L)))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)
      (.classMem
        (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)
      p0143 p0146
  have p0148 :=
    @g_rspccv
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N))
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni L))) (.classMem
          (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N))
      l L N dv_cache_0058 dv_cache_0027 dv_cache_0059 p0147
  have p0149 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wral l N (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)))
      (.imp (.classMem L N) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni L))) (.classMem
            (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)))
      p0140 p0148
  have p0150 :=
    @g_com3r (.classMem N (syn_cnnc)) (.classMem L N)
      (.classMem (.cv y) (syn_ccompl (syn_cuni L)))
      (.classMem
        (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)
      p0149
  have p0151 :=
    @g_vtoclga
      (.imp (.classMem N (syn_cnnc)) (.imp (.classMem L N) (.classMem
            (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) N)))
      (.imp (.classMem N (syn_cnnc)) (.imp (.classMem L N) (.classMem
            (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N)))
      y X (syn_ccompl (syn_cuni L)) dv_cache_0060 dv_cache_0061 dv_cache_0062 p0007 p0150
  have p0152 :=
    @g_com3l (.classMem X (syn_ccompl (syn_cuni L))) (.classMem N (syn_cnnc))
      (.classMem L N)
      (.classMem (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N)
      p0151
  have p0153 :=
    @g_n_3imp (.classMem N (syn_cnnc)) (.classMem L N)
      (.classMem X (syn_ccompl (syn_cuni L)))
      (.classMem (.cab x (syn_wrex b L (.classEq (.cv x) (syn_cun (.cv b) (syn_csn X))))) N)
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

@[expose]
noncomputable def g_nnadjoinpw (A : Class) (M : Class) (N : Class) (X : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
        (.classMem (syn_cpw (syn_cun A (syn_csn X))) (syn_cplc N N))) :=
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
  have dv_cache_0006 : b ∉ ((syn_cpw A)).fv :=
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
  have dv_cache_0007 : a ∉ ((syn_cpw A)).fv :=
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
      ((syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem A M) (.classMem X (syn_ccompl A)))
          (.classMem (syn_cpw A) N))).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_cpw A)).fv :=
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
      ((Class.cab a (syn_wrex b (syn_cpw A)
            (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))).fv :=
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
    a ∉ ((syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))).fv :=
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
  have dv_cache_0016 : t ∉ ((syn_cun (.cv b) (syn_csn X))).fv :=
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
    t ∉ ((Wff.neg (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)))).fv :=
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
  have dv_cache_0018 : b ∉ ((Wff.neg (.classMem (.cv t) (syn_cpw A)))).fv :=
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
    @g_pwadjoin A X a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_simp3 (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)
  have p0002 :=
    @g_simp1r (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)
  have p0003 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem A M)
      (.classMem X (syn_ccompl A)) (.classMem (syn_cpw A) N)
  have p0004 := @g_unipw A
  have p0005 := @g_compleqi (syn_cuni (syn_cpw A)) A p0004
  have p0006 :=
    @g_syl6eleqr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      X (syn_ccompl A) (syn_ccompl (syn_cuni (syn_cpw A))) p0003 p0005
  have p0007 :=
    @g_nnadjoin a (syn_cpw A) N X b dv_cache_0006 dv_cache_0007 dv_cache_0004
      dv_cache_0003 dv_cache_0008
  have p0008 :=
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.classMem N (syn_cnnc)) (.classMem (syn_cpw A) N)
      (.classMem X (syn_ccompl (syn_cuni (syn_cpw A))))
      (.classMem
        (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N)
      p0002 p0001 p0006 p0007
  have p0009 := @g_elcomplg X A (syn_ccompl A)
  have p0010 := @g_ibi (.classMem X (syn_ccompl A)) (.neg (.classMem X A)) p0009
  have p0011 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.classMem X (syn_ccompl A)) (.neg (.classMem X A)) p0003 p0010
  have p0012 := @g_snssg X A (syn_ccompl A)
  have p0013 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.classMem X (syn_ccompl A)) (syn_wb (.classMem X A) (syn_wss (syn_csn X) A)) p0003
      p0012
  have p0014 :=
    @g_mtbid
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.classMem X A) (syn_wss (syn_csn X) A) p0011 p0013
  have p0015 :=
    @g_intnand
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (syn_wss (syn_csn X) A) (syn_wss (.cv b) A) p0014
  have p0016 :=
    @g_ralrimivw
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))) b (syn_cpw A)
      dv_cache_0009 p0015
  have p0017 :=
    @g_disjr t (syn_cpw A)
      (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))
      dv_cache_0010 dv_cache_0011
  have p0018 := @g_eqeq1 (.cv a) (.cv t) (syn_cun (.cv b) (syn_csn X))
  have p0019_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a t) (syn_wb (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))
          (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @g_rexbidv (.objEq a t) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))
      (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) b (syn_cpw A) dv_cache_0012
      p0019_e00_recanon
  have p0020 :=
    @g_ralab (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))
      (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))
      (.neg (.classMem (.cv t) (syn_cpw A))) t a dv_cache_0013 dv_cache_0014 p0019
  have p0021 :=
    @g_ralcom4
      (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
        (.neg (.classMem (.cv t) (syn_cpw A))))
      b t (syn_cpw A) dv_cache_0010 dv_cache_0015
  have p0022 := @g_vex b
  have p0023 := @g_snex X
  have p0024 := @g_unex (.cv b) (syn_csn X) p0022 p0023
  have p0025 := @g_eleq1 (.cv t) (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)
  have p0026 :=
    @g_notbid (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
      (.classMem (.cv t) (syn_cpw A))
      (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)) p0025
  have p0027 :=
    @g_ceqsalv (.neg (.classMem (.cv t) (syn_cpw A)))
      (.neg (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A))) t
      (syn_cun (.cv b) (syn_csn X)) dv_cache_0016 dv_cache_0017 p0024 p0026
  have p0028 := @g_elpw (syn_cun (.cv b) (syn_csn X)) A p0024
  have p0029 := @g_unss (.cv b) (syn_csn X) A
  have p0030 :=
    @g_bitr4i (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A))
      (syn_wss (syn_cun (.cv b) (syn_csn X)) A)
      (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)) p0028 p0029
  have p0031 :=
    @g_xchbinx
      (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
          (.neg (.classMem (.cv t) (syn_cpw A)))))
      (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A))
      (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)) p0027 p0030
  have p0032 :=
    @g_ralbii
      (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
          (.neg (.classMem (.cv t) (syn_cpw A)))))
      (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))) b (syn_cpw A) p0031
  have p0033 :=
    @g_r19_23v (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
      (.neg (.classMem (.cv t) (syn_cpw A))) b (syn_cpw A) dv_cache_0018
  have p0034 :=
    @g_albii
      (syn_wral b (syn_cpw A) (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
          (.neg (.classMem (.cv t) (syn_cpw A)))))
      (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))
        (.neg (.classMem (.cv t) (syn_cpw A))))
      t p0033
  have p0035 :=
    @g_n_3bitr3ri
      (syn_wral b (syn_cpw A) (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
            (.neg (.classMem (.cv t) (syn_cpw A))))))
      (.all t (syn_wral b (syn_cpw A) (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))
            (.neg (.classMem (.cv t) (syn_cpw A))))))
      (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))))
      (.all t (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))
          (.neg (.classMem (.cv t) (syn_cpw A)))))
      p0021 p0032 p0034
  have p0036 :=
    @g_n_3bitri
      (.classEq (syn_cin (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
        (syn_c0))
      (syn_wral t
        (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))
        (.neg (.classMem (.cv t) (syn_cpw A))))
      (.all t (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))
          (.neg (.classMem (.cv t) (syn_cpw A)))))
      (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))))
      p0017 p0020 p0035
  have p0037 :=
    @g_sylibr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))))
      (.classEq (syn_cin (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
        (syn_c0))
      p0016 p0036
  have p0038 :=
    @g_eladdci (syn_cpw A)
      (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N
      N
  have p0039 :=
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (.classMem (syn_cpw A) N)
      (.classMem
        (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N)
      (.classEq (syn_cin (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
        (syn_c0))
      (.classMem (syn_cun (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
        (syn_cplc N N))
      p0001 p0008 p0037 p0038
  have p0040 :=
    @g_syl5eqel
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))
      (syn_cpw (syn_cun A (syn_csn X)))
      (syn_cun (syn_cpw A) (.cab a
          (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
      (syn_cplc N N) p0000 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end
