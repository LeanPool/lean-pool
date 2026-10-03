/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block006

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part017. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_tfinnn (x : Var) (A : Class) (N : Class) (a : Var) (dv_A_a : a ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (_dv_N_a : a ∉ N.fv) (_dv_N_x : x ∉ N.fv) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem N (syn_cnnc)) (syn_wss A (syn_cnnc)) (.classMem A N))
        (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin N))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ N.fv ∪ ({ a } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_a : k ≠ a := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_k : y ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_y : k ≠ y := Ne.symm fresh_y_ne_k
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_z : n ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_z : k ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_k : z ≠ k := Ne.symm fresh_k_ne_z
  have fresh_k_ne_b : k ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_k : b ≠ k := Ne.symm fresh_k_ne_b
  have fresh_k_ne_w : k ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_w_ne_k : w ≠ k := Ne.symm fresh_k_ne_w
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have dv_cache_0001 : a ≠ n := by exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact dv_a_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0005 : n ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ y from (by exact fresh_n_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_n, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Wff.classEq (.cv y) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 :
    y ∉
      ((Wff.imp (syn_wss (syn_c0) (syn_cnnc)) (.all a
            (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_k, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((Wff.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_a,
          fresh_z_ne_x, fresh_z_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0020 :
    y ∉
      ((Wff.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 : y ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_N, not_false_eq_true])
  have dv_cache_0022 : b ∉ ((Class.cv z)).fv :=
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
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0023 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0024 : b ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_k, not_false_eq_true])
  have dv_cache_0025 : b ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show b ≠ w from (by exact fresh_b_ne_w))
  have dv_cache_0026 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((Wff.objEq y b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_b, or_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0029 :
    y ∉
      ((Wff.imp (syn_wss (.cv b) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_b, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0030 :
    x ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
            (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
          (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_b,
          fresh_x_ne_w, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((Wff.classEq (.cv a) (syn_ctfin (.cv w)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_ctfin (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_w,
          not_false_eq_true])
  have dv_cache_0033 :
    a ∉ ((syn_wrex x (.cv b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_w, dv_a_x,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((syn_cun (.cv b) (syn_csn (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_b, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0035 :
    a ∉ ((Wff.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_b, fresh_a_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0036 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0037 : w ∉ ((Class.cv k)).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_k, not_false_eq_true])
  have dv_cache_0038 :
    b ∉
      ((Wff.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_a,
          fresh_b_ne_x, fresh_b_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0039 :
    w ∉
      ((Wff.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_a,
          fresh_w_ne_x, fresh_w_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0040 :
    b ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
            (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_k, fresh_b_ne_y,
          fresh_b_ne_a, fresh_b_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0041 :
    w ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
            (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k))))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_k, fresh_w_ne_y,
          fresh_w_ne_a, fresh_w_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0042 :
    z ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
            (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_k, fresh_z_ne_y,
          fresh_z_ne_a, fresh_z_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0043 : n ∉ (N).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0044 :
    n ∉
      ((syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k)))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0045 :
    k ∉
      ((syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv n)))))).fv :=
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
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_n, fresh_k_ne_y,
          fresh_k_ne_a, fresh_k_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0046 :
    n ∉
      ((Wff.imp (syn_wss (syn_c0) (syn_cnnc)) (.all a
            (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0047 :
    n ∉
      ((syn_wral y N (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin N))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_N, fresh_n_ne_y,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0048 :
    n ∉
      ((syn_wral z (syn_cplc (.cv k) (syn_c1c)) (.imp (syn_wss (.cv z) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_z,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0049 : n ≠ k :=
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
    exact (show n ≠ k from (by exact fresh_n_ne_k))
  have dv_cache_0050 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0051 : a ∉ ((Wff.classEq (.cv y) A)).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, dv_A_a, or_false, not_false_eq_true])
  have dv_cache_0052 : y ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0053 :
    y ∉
      ((Wff.imp (syn_wss A (syn_cnnc))
          (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin N)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_not_N, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_tfinnnlem1 x y n a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_tfineq (.cv n) (syn_c0c)
  have p0002 := @g_tfin0c
  have p0003 :=
    @g_syl6eq (.classEq (.cv n) (syn_c0c)) (syn_ctfin (.cv n)) (syn_ctfin (syn_c0c))
      (syn_c0c) p0001 p0002
  have p0004 :=
    @g_eleq2d (.classEq (.cv n) (syn_c0c)) (syn_ctfin (.cv n)) (syn_c0c)
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0003
  have p0005 :=
    @g_imbi2d (.classEq (.cv n) (syn_c0c))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv n)))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_c0c))
      (syn_wss (.cv y) (syn_cnnc)) p0004
  have p0006 :=
    @g_raleqbi1dv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv n))))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_c0c)))
      y (.cv n) (syn_c0c) dv_cache_0007 dv_cache_0008 p0005
  have p0007 :=
    (Nominal.biimpRefl (syn_wral y (syn_c0c) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_c0c)))))
  have p0008 := @g_el0c (.cv y)
  have p0009 :=
    @g_el0c (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
  have p0010 := @g_ab0 (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))) a
  have p0011 :=
    @g_bitri
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_c0c))
      (.classEq (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_c0))
      (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))) p0009
      p0010
  have p0012 :=
    @g_imbi2i
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_c0c))
      (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_wss (.cv y) (syn_cnnc)) p0011
  have p0013 :=
    @g_imbi12i (.classMem (.cv y) (syn_c0c)) (.classEq (.cv y) (syn_c0))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_c0c)))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0008 p0012
  have p0014 :=
    @g_albii
      (.imp (.classMem (.cv y) (syn_c0c)) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_c0c))))
      (.imp (.classEq (.cv y) (syn_c0)) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))))
      y p0013
  have p0015 := @g_n_0ex
  have p0016 := @g_sseq1 (.cv y) (syn_c0) (syn_cnnc)
  have p0017 :=
    @g_rexeq (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv y) (syn_c0) dv_cache_0009
      dv_cache_0010
  have p0018 :=
    @g_notbid (.classEq (.cv y) (syn_c0))
      (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0017
  have p0019 :=
    @g_albidv (.classEq (.cv y) (syn_c0))
      (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x))))) a dv_cache_0011
      p0018
  have p0020 :=
    @g_imbi12d (.classEq (.cv y) (syn_c0)) (syn_wss (.cv y) (syn_cnnc))
      (syn_wss (syn_c0) (syn_cnnc))
      (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))) p0016
      p0019
  have p0021 :=
    @g_ceqsalv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      (.imp (syn_wss (syn_c0) (syn_cnnc))
        (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      y (syn_c0) dv_cache_0012 dv_cache_0013 p0015 p0020
  have p0022 :=
    @g_n_3bitri
      (syn_wral y (syn_c0c) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_c0c))))
      (.all y (.imp (.classMem (.cv y) (syn_c0c)) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_c0c)))))
      (.all y (.imp (.classEq (.cv y) (syn_c0)) (.imp (syn_wss (.cv y) (syn_cnnc))
            (.all a (.neg (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))))))
      (.imp (syn_wss (syn_c0) (syn_cnnc))
        (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0007 p0014 p0021
  have p0023 :=
    @g_syl6bb (.classEq (.cv n) (syn_c0c))
      (syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv n)))))
      (syn_wral y (syn_c0c) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_c0c))))
      (.imp (syn_wss (syn_c0) (syn_cnnc))
        (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0006 p0022
  have p0024 := @g_tfineq (.cv n) (.cv k)
  have p0025_e00_recanon :
    Nominal.NPrf (.imp (.objEq n k) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0025 :=
    @g_eleq2d (.objEq n k) (syn_ctfin (.cv n)) (syn_ctfin (.cv k))
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      p0025_e00_recanon
  have p0026 :=
    @g_imbi2d (.objEq n k)
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv n)))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      (syn_wss (.cv y) (syn_cnnc)) p0025
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv k)) (syn_wb (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv n)))) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cnnc
          syn_cint syn_wrex syn_wex syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cvv
          syn_cio syn_cuni syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @g_raleqbi1dv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv n))))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      y (.cv n) (.cv k) dv_cache_0007 dv_cache_0014 p0027_e00_recanon
  have p0028 := @g_tfineq (.cv n) (syn_cplc (.cv k) (syn_c1c))
  have p0029 :=
    @g_eleq2d (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c))) (syn_ctfin (.cv n))
      (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0028
  have p0030 :=
    @g_imbi2d (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv n)))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))
      (syn_wss (.cv y) (syn_cnnc)) p0029
  have p0031 :=
    @g_raleqbi1dv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv n))))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))
      y (.cv n) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0007 dv_cache_0015 p0030
  have p0032 := @g_sseq1 (.cv y) (.cv z) (syn_cnnc)
  have p0033 :=
    @g_rexeq (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv y) (.cv z) dv_cache_0009
      dv_cache_0016
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ctfin, syn_cif, syn_wo, syn_c0,
          syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_cvv, syn_cio, syn_cuni,
          syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @g_abbidv (.objEq y z) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))) a dv_cache_0017
      p0034_e00_recanon
  have p0035 :=
    @g_eleq1d (.objEq y z)
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_ctfin (syn_cplc (.cv k) (syn_c1c))) p0034
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wss (.cv y) (syn_cnnc)) (syn_wss (.cv z) (syn_cnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cnnc
          syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0036 :=
    @g_imbi12d (.objEq y z) (syn_wss (.cv y) (syn_cnnc)) (syn_wss (.cv z) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))
      (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))
      p0036_e00_recanon p0035
  have p0037 :=
    @g_cbvralv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))
      (.imp (syn_wss (.cv z) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))
      y z (syn_cplc (.cv k) (syn_c1c)) dv_cache_0015 dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0036
  have p0038 :=
    @g_syl6bb (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv n)))))
      (syn_wral y (syn_cplc (.cv k) (syn_c1c)) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))))
      (syn_wral z (syn_cplc (.cv k) (syn_c1c)) (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))))
      p0031 p0037
  have p0039 := @g_tfineq (.cv n) N
  have p0040 :=
    @g_eleq2d (.classEq (.cv n) N) (syn_ctfin (.cv n)) (syn_ctfin N)
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0039
  have p0041 :=
    @g_imbi2d (.classEq (.cv n) N)
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv n)))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin N))
      (syn_wss (.cv y) (syn_cnnc)) p0040
  have p0042 :=
    @g_raleqbi1dv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv n))))
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin N)))
      y (.cv n) N dv_cache_0007 dv_cache_0021 p0041
  have p0043 := @g_rex0 (.classEq (.cv a) (syn_ctfin (.cv x))) x
  have p0044 := Nominal.gen p0043 a
  have p0045 :=
    @g_a1i (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_wss (syn_c0) (syn_cnnc)) p0044
  have p0046 :=
    @g_elsuc w (.cv z) (.cv k) b dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
  have p0047 := @g_sseq1 (.cv y) (.cv b) (syn_cnnc)
  have p0048 :=
    @g_rexeq (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv y) (.cv b) dv_cache_0009
      dv_cache_0026
  have p0049_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (syn_wb (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ctfin, syn_cif, syn_wo, syn_c0,
          syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_cvv, syn_cio, syn_cuni,
          syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0049 :=
    @g_abbidv (.objEq y b) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))) a dv_cache_0027
      p0049_e00_recanon
  have p0050 :=
    @g_eleq1d (.objEq y b)
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_ctfin (.cv k)) p0049
  have p0051_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (syn_wb (syn_wss (.cv y) (syn_cnnc)) (syn_wss (.cv b) (syn_cnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cnnc
          syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0047
  have p0051 :=
    @g_imbi12d (.objEq y b) (syn_wss (.cv y) (syn_cnnc)) (syn_wss (.cv b) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      p0051_e00_recanon p0050
  have p0052_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv b)) (syn_wb (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k)))) (.imp (syn_wss (.cv b) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cnnc
          syn_cint syn_wrex syn_wex syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cvv
          syn_cio syn_cuni syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0051
  have p0052 :=
    @g_rspcv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (.imp (syn_wss (.cv b) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      y (.cv b) (.cv k) dv_cache_0028 dv_cache_0014 dv_cache_0029 p0052_e00_recanon
  have p0053_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem b k) (.imp (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
              (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k))))) (.imp (syn_wss (.cv b) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cnnc
          syn_cint syn_wrex syn_wex syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cvv
          syn_cio syn_cuni syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0052
  have p0053 :=
    @g_ad2antrl (.objMem b k)
      (.imp (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))) (.imp (syn_wss (.cv b) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv w) (syn_ccompl (.cv b)))
      p0053_e00_recanon
  have p0054 :=
    @g_simprl
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))
  have p0055 :=
    @g_simp3
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
  have p0056 :=
    @g_simplrr (.classMem (.cv k) (syn_cnnc)) (.objMem b k)
      (.classMem (.cv w) (syn_ccompl (.cv b)))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
  have p0057 := @g_vex w
  have p0058 := @g_elcompl (.cv w) (.cv b) p0057
  have p0059_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv w) (syn_ccompl (.cv b))) (.neg (.objMem w b))) :=
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
      p0058
  have p0059 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.classMem (.cv w) (syn_ccompl (.cv b))) (.neg (.objMem w b)) p0056
      p0059_e01_recanon
  have p0060 := @g_elequ1 w x b
  have p0061 := @g_notbid (.objEq w x) (.objMem w b) (.objMem x b) p0060
  have p0062 :=
    @g_syl5ibcom
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.neg (.objMem w b)) (.objEq w x) (.neg (.objMem x b)) p0059 p0061
  have p0063 :=
    @g_con2d
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.objEq w x) (.objMem x b) p0062
  have p0064 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.objMem x b) (.neg (.objEq w x)) p0063
  have p0065 :=
    @g_simpll
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.objMem x b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))
  have p0066 :=
    @g_simprr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
              (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
            (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
        (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.classMem (.cv w) (syn_cnnc)) p0065 p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
              (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
            (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
        (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (syn_wss (.cv b) (syn_cnnc)) p0065 p0054
  have p0069 :=
    @g_simplr
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.objMem x b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))
  have p0070_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
                (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
              (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
            (.objMem x b)) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
        (.classMem (.cv x) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0069
  have p0070 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
              (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
            (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
        (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
      (.cv b) (syn_cnnc) (.cv x) p0068 p0070_e01_recanon
  have p0071 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
            (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
          (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
      (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))
  have p0072 := @g_tfin11 (.cv w) (.cv x)
  have p0073_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
          (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))) (.objEq w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_ctfin syn_cif syn_wo syn_c0 syn_cdif
          syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0072
  have p0073 :=
    @g_syl3anc
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
              (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
            (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
        (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
      (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))) (.objEq w x) p0067 p0070 p0071
      p0073_e03_recanon
  have p0074 :=
    @g_mtand
      (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
            (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
          (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))) (.objMem x b))
      (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))) (.objEq w x) p0064 p0073
  have p0075_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
              (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
            (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
          (.classMem (.cv x) (.cv b)))
        (.neg (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0074
  have p0075 :=
    @g_nrexdv
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))) x (.cv b) dv_cache_0030
      p0075_e00_recanon
  have p0076 :=
    @g_n_3adant3
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.neg (syn_wrex x (.cv b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      p0075
  have p0077 := @g_tfinex (.cv w)
  have p0078 := @g_eqeq1 (.cv a) (syn_ctfin (.cv w)) (syn_ctfin (.cv x))
  have p0079 :=
    @g_rexbidv (.classEq (.cv a) (syn_ctfin (.cv w)))
      (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))) x (.cv b) dv_cache_0031 p0078
  have p0080 :=
    @g_elab (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (.cv b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x)))) a
      (syn_ctfin (.cv w)) dv_cache_0032 dv_cache_0033 p0077 p0079
  have p0081 :=
    @g_sylnibr
      (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (syn_wrex x (.cv b) (.classEq (syn_ctfin (.cv w)) (syn_ctfin (.cv x))))
      (.classMem (syn_ctfin (.cv w))
        (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      p0076 p0080
  have p0082 :=
    @g_elsuci (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_ctfin (.cv k)) (syn_ctfin (.cv w)) p0077
  have p0083 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      (.neg (.classMem (syn_ctfin (.cv w))
          (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      (.classMem (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0055 p0081 p0082
  have p0084 :=
    @g_n_3expia
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      (.classMem (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0083
  have p0085 :=
    @g_embantd
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))))
      (syn_wss (.cv b) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (.cv k)))
      (.classMem (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0054 p0084
  have p0086 :=
    @g_ex
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.imp (.imp (syn_wss (.cv b) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))) (.classMem
          (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      p0085
  have p0087 :=
    @g_com23
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.imp (syn_wss (.cv b) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (.classMem (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0086
  have p0088 := @g_sseq1 (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))) (syn_cnnc)
  have p0089 := @g_snss (.cv w) (syn_cnnc) p0057
  have p0090 :=
    @g_anbi2i (.classMem (.cv w) (syn_cnnc)) (syn_wss (syn_csn (.cv w)) (syn_cnnc))
      (syn_wss (.cv b) (syn_cnnc)) p0089
  have p0091 := @g_unss (.cv b) (syn_csn (.cv w)) (syn_cnnc)
  have p0092 :=
    @g_bitr2i (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (syn_wss (syn_csn (.cv w)) (syn_cnnc)))
      (syn_wss (syn_cun (.cv b) (syn_csn (.cv w))) (syn_cnnc)) p0090 p0091
  have p0093 :=
    @g_syl6bb (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (syn_wss (.cv z) (syn_cnnc))
      (syn_wss (syn_cun (.cv b) (syn_csn (.cv w))) (syn_cnnc))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))) p0088 p0092
  have p0094 :=
    @g_rexeq (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv z)
      (syn_cun (.cv b) (syn_csn (.cv w))) dv_cache_0016 dv_cache_0034
  have p0095 :=
    @g_rexun (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv b) (syn_csn (.cv w))
  have p0096 :=
    @g_syl6bb (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cun (.cv b) (syn_csn (.cv w))) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wo (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
        (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      p0094 p0095
  have p0097 :=
    @g_abbidv (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wo (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
        (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      a dv_cache_0035 p0096
  have p0098 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn a
      (syn_ctfin (.cv w)) dv_cache_0032
  have p0099 := @g_tfineq (.cv x) (.cv w)
  have p0100_e00_recanon :
    Nominal.NPrf (.imp (.objEq x w) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @g_eqeq2d (.objEq x w) (syn_ctfin (.cv x)) (syn_ctfin (.cv w)) (.cv a)
      p0100_e00_recanon
  have p0101_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w)) (syn_wb (.classEq (.cv a) (syn_ctfin (.cv x)))
          (.classEq (.cv a) (syn_ctfin (.cv w))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0100
  have p0101 :=
    @g_rexsn (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (.cv a) (syn_ctfin (.cv w)))
      x (.cv w) dv_cache_0036 dv_cache_0031 p0057 p0101_e01_recanon
  have p0102 :=
    @g_abbii (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (.classEq (.cv a) (syn_ctfin (.cv w))) a p0101
  have p0103 :=
    @g_eqtr4i (syn_csn (syn_ctfin (.cv w)))
      (.cab a (.classEq (.cv a) (syn_ctfin (.cv w))))
      (.cab a (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0098
      p0102
  have p0104 :=
    @g_uneq2i (syn_csn (syn_ctfin (.cv w)))
      (.cab a (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0103
  have p0105 :=
    @g_unab (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x)))) a
  have p0106 :=
    @g_eqtr2i
      (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_ctfin (.cv w))))
      (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (.cab a (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (.cab a (syn_wo (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      p0104 p0105
  have p0107 :=
    @g_syl6eq (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.cab a (syn_wo (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (syn_csn (.cv w)) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_ctfin (.cv w))))
      p0097 p0106
  have p0108 :=
    @g_eleq1d (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_ctfin (.cv w))))
      (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)) p0107
  have p0109 :=
    @g_imbi12d (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (syn_wss (.cv z) (syn_cnnc))
      (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc)))
      (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      (.classMem (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0093 p0108
  have p0110 :=
    @g_biimprcd (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (.imp (syn_wss (.cv z) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      (.imp (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))) (.classMem
          (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      p0109
  have p0111 :=
    @g_syl6
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (.imp (syn_wss (.cv b) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (.imp (syn_wa (syn_wss (.cv b) (syn_cnnc)) (.classMem (.cv w) (syn_cnnc))) (.classMem
          (syn_cun (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_ctfin (.cv w)))) (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      (.imp (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
        (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))))
      p0087 p0110
  have p0112 :=
    @g_syld
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (.imp (syn_wss (.cv b) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv b) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (.cv k))))
      (.imp (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
        (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))))
      p0053 p0111
  have p0113 :=
    @g_imp
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b)))))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (.imp (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
        (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))))
      p0112
  have p0114 :=
    @g_an32s (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem b k) (.classMem (.cv w) (syn_ccompl (.cv b))))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (.imp (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
        (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))))
      p0113
  have p0115_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
              (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                  (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                  (syn_ctfin (.cv k))))))
          (syn_wa (.classMem (.cv b) (.cv k)) (.classMem (.cv w) (syn_ccompl (.cv b)))))
        (.imp (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
          (.imp (syn_wss (.cv z) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_wss syn_cin
          syn_cnnc syn_cint syn_wrex syn_wex syn_ctfin syn_cif syn_wo syn_c0 syn_cdif
          syn_cvv syn_cio syn_cuni syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
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
      p0114
  have p0115 :=
    @g_rexlimdvva
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))
      (.imp (syn_wss (.cv z) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      b w (.cv k) (syn_ccompl (.cv b)) dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0040 dv_cache_0041 dv_cache_0025 p0115_e00_recanon
  have p0116 :=
    @g_syl5bi (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wrex b (.cv k) (syn_wrex w (syn_ccompl (.cv b))
          (.classEq (.cv z) (syn_cun (.cv b) (syn_csn (.cv w))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (.imp (syn_wss (.cv z) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_cplc (syn_ctfin (.cv k)) (syn_c1c))))
      p0046 p0115
  have p0117 :=
    @g_imp32
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv z) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0116
  have p0118 :=
    @g_simpll (.classMem (.cv k) (syn_cnnc))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (syn_wa (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv z) (syn_cnnc)))
  have p0119 := @g_ne0i (syn_cplc (.cv k) (syn_c1c)) (.cv z)
  have p0120 :=
    @g_ad2antrl (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (syn_wss (.cv z) (syn_cnnc)) p0119
  have p0121 := @g_tfinsuc (.cv k)
  have p0122 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
            (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k)))))) (syn_wa (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c)))
          (syn_wss (.cv z) (syn_cnnc))))
      (.classMem (.cv k) (syn_cnnc)) (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))
        (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)))
      p0118 p0120 p0121
  have p0123 :=
    @g_eleqtrrd
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
            (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k)))))) (syn_wa (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c)))
          (syn_wss (.cv z) (syn_cnnc))))
      (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cplc (syn_ctfin (.cv k)) (syn_c1c)) (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))
      p0117 p0122
  have p0124 :=
    @g_expr
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (.classMem (.cv z) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv z) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))
      p0123
  have p0125 :=
    @g_ralrimiva
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral y (.cv k)
          (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
              (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_ctfin (.cv k))))))
      (.imp (syn_wss (.cv z) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin (syn_cplc (.cv k) (syn_c1c)))))
      z (syn_cplc (.cv k) (syn_c1c)) dv_cache_0042 p0124
  have p0126 :=
    @g_ex (.classMem (.cv k) (syn_cnnc))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (syn_wral z (syn_cplc (.cv k) (syn_c1c)) (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))))
      p0125
  have p0127_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (syn_wb (syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc))
              (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv n))))) (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
              (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv k))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cnnc syn_cint syn_wrex syn_wex syn_ctfin syn_cif syn_wo syn_c0 syn_cdif
          syn_cvv syn_cio syn_cuni syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0127 :=
    @g_finds
      (syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv n)))))
      (.imp (syn_wss (syn_c0) (syn_cnnc))
        (.all a (.neg (syn_wrex x (syn_c0) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      (syn_wral y (.cv k) (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (.cv k)))))
      (syn_wral z (syn_cplc (.cv k) (syn_c1c)) (.imp (syn_wss (.cv z) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv z) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin (syn_cplc (.cv k) (syn_c1c))))))
      (syn_wral y N (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin N))))
      n k N dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 p0000 p0023 p0127_e02_recanon p0038 p0042 p0045 p0126
  have p0128 := @g_sseq1 (.cv y) A (syn_cnnc)
  have p0129 :=
    @g_rexeq (.classEq (.cv a) (syn_ctfin (.cv x))) x (.cv y) A dv_cache_0009
      dv_cache_0050
  have p0130 :=
    @g_abbidv (.classEq (.cv y) A)
      (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x)))) a dv_cache_0051 p0129
  have p0131 :=
    @g_eleq1d (.classEq (.cv y) A)
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin N) p0130
  have p0132 :=
    @g_imbi12d (.classEq (.cv y) A) (syn_wss (.cv y) (syn_cnnc)) (syn_wss A (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin N))
      (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin N))
      p0128 p0131
  have p0133 :=
    @g_rspccv
      (.imp (syn_wss (.cv y) (syn_cnnc))
        (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin N)))
      (.imp (syn_wss A (syn_cnnc))
        (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_ctfin N)))
      y A N dv_cache_0052 dv_cache_0021 dv_cache_0053 p0132
  have p0134 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wral y N (.imp (syn_wss (.cv y) (syn_cnnc))
          (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin N))))
      (.imp (.classMem A N) (.imp (syn_wss A (syn_cnnc))
          (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_ctfin N))))
      p0127 p0133
  have p0135 :=
    @g_com23 (.classMem N (syn_cnnc)) (.classMem A N) (syn_wss A (syn_cnnc))
      (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin N))
      p0134
  have p0136 :=
    @g_n_3imp (.classMem N (syn_cnnc)) (syn_wss A (syn_cnnc)) (.classMem A N)
      (.classMem (.cab a (syn_wrex x A (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin N))
      p0135
  exact p0136


end NFChoice.DirectNominalPrf.WPPReplay
