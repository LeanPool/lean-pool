/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpstrictnoreversendv (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.imp
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
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
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_x, fresh_z_ne_v, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0005 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0006 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 :
    y ∉
      ((syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_z,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_x, fresh_y_ne_v, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv v)).fv :=
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
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0013 :
    x ∉ ((Wff.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_v_x), (Ne.symm dv_u_x),
          dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0014 :
    x ∉
      ((syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv v) (syn_chwcn A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_u_x), (Ne.symm dv_v_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simp1
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0001 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
  have p0002 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0003 :=
    @g_simp2
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0004 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      p0002 p0003
  have p0005 := @g_hnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0006 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.neg (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0004 p0005
  have p0007 :=
    @g_simpl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0009 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
  have p0010 := @g_hwnisoer A
  have p0011 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0009
      p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0007 p0011
  have p0017 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (syn_chwcn A)) p0007 p0002
  have p0021 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0022 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) p0007 p0021
  have p0029 := @g_hnwcutcodeambientndv x v A dv_cache_0001
  have p0030 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwcn A))
      p0004 p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwcn A))
      p0007 p0030
  have p0032 :=
    @g_simpr
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0034 :=
    @g_simp3
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0035 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0007 p0034
  have p0036 :=
    @g_ertrd
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (syn_chwcn A) (syn_chwniso A) (.cv v) (.cv u)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      p0012 p0017 p0022 p0031 p0032 p0035
  have p0037 :=
    @g_expcom
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0036
  have p0038 :=
    @g_com12 (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0037
  have p0039 :=
    @g_mtod
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0006 p0038
  have p0040 :=
    @g_simpl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0044 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) p0040 p0021
  have p0045 :=
    @g_simpr
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0046 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
      p0044 p0045
  have p0047 := @g_hnwcutcodeselfnoisondv z u A dv_cache_0002
  have p0048 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (.neg (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0046 p0047
  have p0049 :=
    @g_nrexdv
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
      z (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0003 p0048
  have p0050 :=
    @g_simp1
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0053 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem A (syn_cvv)) p0050 p0009
  have p0058 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) p0050 p0021
  have p0063 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (syn_chwcn A)) p0050 p0002
  have p0064 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0058 p0063
  have p0070 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0064 p0058
  have p0071 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv u) (syn_chwcn A)))
      p0053 p0070
  have p0074 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0050 p0003
  have p0077 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0050 p0034
  have p0078 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0074 p0077
  have p0079 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv u) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0071 p0078
  have p0090 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0063 p0058
  have p0091 :=
    @g_simp2
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0092 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0090 p0091
  have p0093 :=
    @g_simp3
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0097 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0093 p0074
  have p0098 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      p0092 p0097
  have p0099 :=
    @g_hnwcutcodetransportintocutndv x y z u v A dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0100 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0098 p0099
  have p0101 :=
    @g_jca
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv u) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0079 p0100
  have p0102 :=
    @g_hnwcutcodestrictextendndv x z u v u A dv_cache_0002 dv_cache_0001 dv_cache_0002
      dv_cache_0004 dv_cache_0006 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0103 :=
    @g_syl
      (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv u) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv z)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0101 p0102
  have p0104 :=
    @g_n_3exp
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0103
  have p0105 :=
    @g_rexlimdv
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      y (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0008 dv_cache_0009 p0104
  have p0106 :=
    @g_mtod
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))
      p0049 p0105
  have p0107 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u)))
      (.neg (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0039 p0106
  have p0108 :=
    @g_ioran (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0109 :=
    @g_a1i
      (syn_wb (.neg (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
            (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y)))))) (syn_wa (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (.neg
            (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y)))))))
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0108
  have p0110 :=
    @g_mpbird
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.neg (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))))))
      (syn_wa (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (.neg
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))))))
      p0107 p0109
  have p0117 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0002 p0021
  have p0118 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0119 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
        (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))))))
      p0117 p0118
  have p0120 :=
    @g_biimpd
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0119
  have p0121 :=
    @g_mtod
      (syn_w3a (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0110 p0120
  have p0122 :=
    @g_n_3exp
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0121
  have p0123 :=
    @g_rexlimdv
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) x
      (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0013 dv_cache_0014 p0122
  exact p0123


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpkerptndv (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wb (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv :=
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
          fresh_y_ne_u, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0001 := @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0002 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0000 p0001
  have p0003 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0002
  have p0004 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0005 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      p0004 p0005
  have p0007 :=
    @g_mt2d
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0003 p0006
  have p0011 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0002
  have p0013 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0004
      p0013
  have p0015 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006
      dv_cache_0007
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0014 p0015
  have p0017 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0011 p0016
  have p0018 :=
    @g_orcomd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0017
  have p0019 :=
    @g_orcanai
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0018
  have p0020 :=
    @g_mpdan
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (.neg (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0007 p0019
  have p0021 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0022 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0021 p0022
  have p0024 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0024
      p0013
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0026 p0015
  have p0029 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0023 p0028
  have p0031 := @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      p0021 p0031
  have p0033 :=
    @g_orc (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0032 p0033
  have p0038 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0026
  have p0042 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0026
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0038 p0042
  have p0044 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
        (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))))))
      p0043 p0044
  have p0046 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0034 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0029 p0046
  have p0049 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0047 p0001
  have p0050 :=
    @g_impbida
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0020 p0049
  exact p0050

@[expose]
noncomputable def g_hncodecmplnkerndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv))
        (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_v_ne_x : v ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv :=
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
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_clnker (syn_chncodecmpset A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((syn_clnker (syn_chncodecmpset A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : v ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem A (syn_cvv))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0001 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0002 := @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0003 :=
    @g_sylib
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0001 p0002
  have p0004 :=
    @g_simpld
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0003
  have p0005 := @g_hncodecmpsetssxpndv A
  have p0006 :=
    @g_brel (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A) (syn_chncodecmpset A) p0005
  have p0007 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0004
      p0006
  have p0008 :=
    @g_jca
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
      p0007
  have p0010 :=
    @g_jca
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0008 p0001
  have p0011 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0013 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0011 p0002
  have p0014 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0013
  have p0015 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0016 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      p0015 p0016
  have p0018 :=
    @g_mt2d
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0014 p0017
  have p0022 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0013
  have p0024 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0015
      p0024
  have p0026 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006
      dv_cache_0007
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0025 p0026
  have p0028 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0022 p0027
  have p0029 :=
    @g_orcomd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0028
  have p0030 :=
    @g_orcanai
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0029
  have p0031 :=
    @g_mpdan
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (.neg (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0018 p0030
  have p0032 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0010 p0031
  have p0033 :=
    @g_ex (.classMem A (syn_cvv))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0032
  have p0034 := @g_simpl (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0035 := @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0036 := @g_breldm (.cv u) (.cv v) (syn_chwniso A)
  have p0037 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (.cv u) (syn_cdm (syn_chwniso A))) p0035 p0036
  have p0038 := @g_hwnisodm A
  have p0039 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A))
      (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0038
  have p0040 :=
    @g_eleqtrd (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.cv u) (syn_cdm (syn_chwniso A)) (syn_chwcn A) p0037 p0039
  have p0042 := @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0043 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      p0035 p0042
  have p0044 := @g_breldm (.cv v) (.cv u) (syn_chwniso A)
  have p0045 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (.classMem (.cv v) (syn_cdm (syn_chwniso A))) p0043 p0044
  have p0048 :=
    @g_eleqtrd (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.cv v) (syn_cdm (syn_chwniso A)) (syn_chwcn A) p0045 p0039
  have p0049 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0040 p0048
  have p0050 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0034
      p0049
  have p0052 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0050 p0035
  have p0053 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0054 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0053 p0054
  have p0056 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0056
      p0024
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0058 p0026
  have p0061 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0055 p0060
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      p0053 p0042
  have p0065 :=
    @g_orc (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0064 p0065
  have p0070 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0058
  have p0074 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0058
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0070 p0074
  have p0076 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
        (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))))))
      p0075 p0076
  have p0078 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0066 p0077
  have p0079 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0061 p0078
  have p0081 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0079 p0002
  have p0082 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0052 p0081
  have p0083 :=
    @g_ex (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0082
  have p0084 :=
    @g_impbid (.classMem A (syn_cvv))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0033 p0083
  have p0085 :=
    (Nominal.biimpRefl (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)))
  have p0086 :=
    @g_bicomi (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_clnker (syn_chncodecmpset A))) p0085
  have p0087 := (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
  have p0088 :=
    @g_bicomi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) p0087
  have p0089 :=
    @g_n_3bitr4g (.classMem A (syn_cvv))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_clnker (syn_chncodecmpset A)))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) p0084 p0086 p0088
  have p0090 :=
    @g_eqrelrdv (.classMem A (syn_cvv)) u v (syn_clnker (syn_chncodecmpset A))
      (syn_chwniso A) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0008 p0089
  exact p0090


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpstrictbrndv (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_v : u ≠ v)
    (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb
          (syn_wbr (.cv u)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_u_x), not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_v_x), not_false_eq_true])
  have dv_cache_0007 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0008 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show v ≠ x from (by exact dv_v_x))
  have p0000 :=
    @g_brdif (.cv u) (.cv v) (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))
  have p0001 := @g_brcnv (.cv u) (.cv v) (syn_chncodecmpset A)
  have p0002 :=
    @g_notbii (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0001
  have p0003 :=
    @g_anbi2i (.neg (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v)))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) p0002
  have p0004 :=
    @g_bitri
      (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      p0000 p0003
  have p0005 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      p0004
  have p0006 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0006
  have p0008 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0009 := @g_hncodecmpkerptndv v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wb (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      p0008 p0009
  have p0011 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0010
  have p0012 := @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0013 :=
    @g_biimpi (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0012
  have p0014 :=
    @g_syl6
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0011 p0013
  have p0015 :=
    @g_simpr (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
  have p0016 :=
    @g_syl6
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0014 p0015
  have p0017 :=
    @g_mtod
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0007 p0016
  have p0019 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0006
  have p0021 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0008
      p0021
  have p0023 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0022 p0023
  have p0025 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0019 p0024
  have p0026 :=
    @g_orcanai
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0025
  have p0027 :=
    @g_mpdan
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))))
      (.neg (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0017 p0026
  have p0028 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0029 :=
    @g_olc
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0028 p0029
  have p0031 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0031
      p0021
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0033 p0023
  have p0036 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0030 p0035
  have p0039 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0007 dv_cache_0008
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      p0031 p0039
  have p0041 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0028 p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0036 p0041
  have p0043 :=
    @g_impbida
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0027 p0042
  have p0044 :=
    @g_bitrd
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0005 p0043
  exact p0044

@[expose]
noncomputable def g_hncodecutfnex :
    Nominal.NPrf (.classMem (syn_chncodecutfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0001 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0002 := @g_lninteropex
  have p0003 := @g_n_1stex
  have p0005 := @g_coex (syn_c1st) (syn_c1st) p0003 p0003
  have p0006 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0007 := @g_crossex
  have p0008 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0010 := @g_n_2ndex
  have p0012 := @g_coex (syn_c2nd) (syn_c1st) p0010 p0003
  have p0013 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0014 := @g_lnimageopex
  have p0015 := @g_swapex
  have p0016 := @g_imageex (syn_cswap) p0015
  have p0017 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0018 := @g_lndifopex
  have p0022 := @g_vvex
  have p0023 := @g_snex (syn_cid)
  have p0024 := @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0022 p0023
  have p0025 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
      p0005 p0024
  have p0026 :=
    @g_coex (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0018 p0025
  have p0027 :=
    @g_eqeltri (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      (syn_cvv) p0017 p0026
  have p0028 := @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0016 p0027
  have p0030 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0028
      p0010
  have p0031 :=
    @g_coex (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0014 p0030
  have p0032 :=
    @g_eqeltri (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      (syn_cvv) p0013 p0031
  have p0033 := @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0012 p0032
  have p0034 :=
    @g_coex (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0002 p0033
  have p0035 :=
    @g_eqeltri (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      (syn_cvv) p0008 p0034
  have p0064 := @g_txpex (syn_chncodecarrierfn) (syn_chncodecarrierfn) p0035 p0035
  have p0065 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0007
      p0064
  have p0066 :=
    @g_eqeltri (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      (syn_cvv) p0006 p0065
  have p0067 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn) p0005 p0066
  have p0068 :=
    @g_coex (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0002 p0067
  have p0069 :=
    @g_eqeltri (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      (syn_cvv) p0001 p0068
  have p0098 := @g_txpex (syn_chncoderelfn) (syn_chncodecarrierfn) p0069 p0035
  have p0099 :=
    @g_eqeltri (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
      (syn_cvv) p0000 p0098
  exact p0099

@[expose]
noncomputable def g_hncodepredinputsexg (v : Var) (A : Class) (X : Class)
    (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
        (.classMem (syn_chncodepredinputs A X v) (syn_cvv))) :=
  by
  have p0000 := @g_snex (.cv v)
  have p0001 := @g_fvex (.cv v) (syn_c2nd)
  have p0002 := @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0001
  have p0003 :=
    @g_xpex (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0000 p0002
  have p0004 :=
    @g_a1i
      (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0003
  have p0005 := @g_hncodecutfnex
  have p0006 := @g_cnvexg (syn_chncodecutfn) (syn_cvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0007
  have p0009 := @g_simpl (.classMem A (syn_cvv)) (.classMem X (syn_cvv))
  have p0010 := @g_hwnisoexg A
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) p0009 p0010
  have p0012 := @g_simpr (.classMem A (syn_cvv)) (.classMem X (syn_cvv))
  have p0013 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_chwniso A) (syn_cvv)) (.classMem X (syn_cvv)) p0011 p0012
  have p0014 := @g_imaexg (syn_chwniso A) X (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv))
      (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv)) p0008 p0015
  have p0017 :=
    @g_imaexg (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X) (syn_cvv)
      (syn_cvv)
  have p0018 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv))
        (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
        (syn_cvv))
      p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
        (syn_cvv))
      p0004 p0018
  have p0020 :=
    @g_inexg (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)) (syn_cvv)
      (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cvv))
        (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
          (syn_cvv)))
      (.classMem (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cvv))
      p0019 p0020
  have p0022 := (Nominal.classEqRefl (syn_chncodepredinputs A X v))
  have p0023 :=
    @g_eleq1i (syn_chncodepredinputs A X v)
      (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (syn_cvv) p0022
  have p0024 :=
    @g_sylibr (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cvv))
      (.classMem (syn_chncodepredinputs A X v) (syn_cvv)) p0021 p0023
  exact p0024

@[expose]
noncomputable def g_hncodepredinputsssndv (v : Var) (A : Class) (X : Class)
    (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (syn_wss (syn_chncodepredinputs A X v)
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodepredinputs A X v))
  have p0001 :=
    @g_inss1 (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
  have p0002 :=
    @g_eqsstri (syn_chncodepredinputs A X v)
      (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hncodepredinputmemndv (x : Var) (v : Var) (u : Var) (A : Class)
    (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb
          (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))))) :=
  by
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_u_x, dv_u_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_u,
          not_false_eq_true])
  have dv_cache_0004 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chncodepredinputs A X v))
  have p0001 :=
    @g_eleq2i (syn_chncodepredinputs A X v)
      (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (syn_cop (.cv v) (syn_csn (.cv x))) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
        (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
            (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))))
      (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0003 :=
    @g_elin (syn_cop (.cv v) (syn_csn (.cv x)))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
            (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))) (syn_wa
          (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
            (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
          (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))))
      (.classMem (.cv v) (syn_chwcn A)) p0003
  have p0005 :=
    @g_opelxp (.cv v) (syn_csn (.cv x)) (syn_csn (.cv v))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0006 := @g_vex v
  have p0007 := @g_snid (.cv v) p0006
  have p0008 :=
    @g_biantrur (.classMem (.cv v) (syn_csn (.cv v)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0007
  have p0009 :=
    @g_bicomi (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv v) (syn_csn (.cv v)))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0008
  have p0010 :=
    @g_bitri
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (.cv v) (syn_csn (.cv v)))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0005 p0009
  have p0011 := @g_snelpw1 (.cv x) (syn_cfv (syn_c2nd) (.cv v))
  have p0012 :=
    @g_bitri
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0010 p0011
  have p0013 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv v) (syn_chwcn A)) p0012
  have p0014 := @g_hncodecutfnfn
  have p0015 :=
    @g_elpreima (syn_cvv) (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_chwniso A) X)
      (syn_chncodecutfn)
  have p0016 := Nominal.mp p0014 p0015
  have p0018 := @g_snex (.cv x)
  have p0019 := @g_opex (.cv v) (syn_csn (.cv x)) p0006 p0018
  have p0020 :=
    @g_biantrur (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv))
      (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
        (syn_cima (syn_chwniso A) X))
      p0019
  have p0021 :=
    @g_bicomi
      (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
        (syn_cima (syn_chwniso A) X))
      (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv))
        (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
          (syn_cima (syn_chwniso A) X)))
      p0020
  have p0022 :=
    @g_bitri
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv))
        (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
          (syn_cima (syn_chwniso A) X)))
      (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
        (syn_cima (syn_chwniso A) X))
      p0016 p0021
  have p0023 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
        (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
          (syn_cima (syn_chwniso A) X)))
      (.classMem (.cv v) (syn_chwcn A)) p0022
  have p0024 := @g_hncodecutfnvalhwcn x v A dv_cache_0001
  have p0025 :=
    @g_eleq1d (.classMem (.cv v) (syn_chwcn A))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cima (syn_chwniso A) X) p0024
  have p0026 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
        (syn_cima (syn_chwniso A) X))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_cima (syn_chwniso A) X))
      p0023 p0025
  have p0027 :=
    @g_elima u
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chwniso A) X dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0028 :=
    @g_a1i
      (syn_wb (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_cima (syn_chwniso A) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (syn_chwcn A)) p0027
  have p0029 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_cima (syn_chwniso A) X))
      (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0026 p0028
  have p0030 :=
    @g_anbi12d (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))
      (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0013 p0029
  have p0031 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))))
      (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
        (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0004 p0030
  have p0032 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x)))
        (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0002 p0031
  exact p0032

@[expose]
noncomputable def g_hncodepredendsexg (v : Var) (A : Class) (X : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
        (.classMem (syn_chncodepredends A X v) (syn_cvv))) :=
  by
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have p0000 := @g_n_2ndex
  have p0001 :=
    @g_a1i (.classMem (syn_c2nd) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0000
  have p0002 := @g_hncodepredinputsexg v A X dv_cache_0001
  have p0003 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chncodepredinputs A X v) (syn_cvv))
      p0001 p0002
  have p0004 := @g_imaexg (syn_c2nd) (syn_chncodepredinputs A X v) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (.classMem (syn_c2nd) (syn_cvv))
        (.classMem (syn_chncodepredinputs A X v) (syn_cvv)))
      (.classMem (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv)) p0003
      p0004
  have p0006 := @g_uniexg (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv))
      (.classMem (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv))
      p0005 p0006
  have p0008 := (Nominal.classEqRefl (syn_chncodepredends A X v))
  have p0009 :=
    @g_eleq1i (syn_chncodepredends A X v)
      (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv) p0008
  have p0010 :=
    @g_sylibr (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv))
      (.classMem (syn_chncodepredends A X v) (syn_cvv)) p0007 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodepredendsmemndv (x : Var) (v : Var) (u : Var) (A : Class)
    (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (syn_chwcn A))
        (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ X.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_X : p ∉ X.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((syn_chncodepredinputs A X v)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs,
          Finset.mem_union, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_X,
          fresh_p_ne_v, or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_c2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0006 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have dv_cache_0007 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0008 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0009 :
    p ∉
      ((syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v,
          fresh_p_not_X, fresh_p_ne_u, fresh_p_not_A, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_v, fresh_p_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cop (.cv v) (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_v, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((Wff.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chncodepredends A X v))
  have p0001 :=
    @g_eleq2i (syn_chncodepredends A X v)
      (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (.cv x) p0000
  have p0002 := @g_ln2ndfn
  have p0003 := @g_fnfun (syn_cvv) (syn_c2nd)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_eluniima p (syn_chncodepredinputs A X v) (.cv x) (syn_c2nd) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri (.classMem (.cv x) (syn_chncodepredends A X v))
      (.classMem (.cv x) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      p0001 p0006
  have p0008 :=
    @g_a1i
      (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v))
        (syn_wrex p (syn_chncodepredinputs A X v)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.classMem (.cv v) (syn_chwcn A)) p0007
  have p0009 :=
    @g_biimpd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      p0008
  have p0010 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
  have p0011 :=
    @g_simpld
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.classMem (.cv p) (syn_chncodepredinputs A X v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))) p0010
  have p0013 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0014 := @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0015 :=
    @g_sseli (syn_chncodepredinputs A X v)
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0014
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (.cv p) (syn_chncodepredinputs A X v))
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0013 p0015
  have p0017 :=
    @g_n_1st2nd2 (.cv p) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classEq (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))))
      p0016 p0017
  have p0029 :=
    @g_eleq1d
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0018
  have p0030 :=
    @g_mpbid
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0016 p0029
  have p0031 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv v))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0032 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))
          (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v)))
          (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      p0031
  have p0033 :=
    @g_mpbid
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v)))
        (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0030 p0032
  have p0034 :=
    @g_simpld
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v)))
      (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0033
  have p0035 := @g_elsni (syn_cfv (syn_c1st) (.cv p)) (.cv v)
  have p0036 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_c1st) (.cv p)) (.cv v)) p0034 p0035
  have p0052 :=
    @g_simprd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v)))
      (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0033
  have p0053 := @g_pw1argclcl (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv p))
  have p0054 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v)))
        (.classEq (syn_cfv (syn_c2nd) (.cv p))
          (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p))))))
      p0052 p0053
  have p0055 :=
    @g_simprd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v)))
      (.classEq (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))))
      p0054
  have p0056 :=
    @g_simpr (.classMem (.cv p) (syn_chncodepredinputs A X v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0076 :=
    @g_eleqtrd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.cv x) (syn_cfv (syn_c2nd) (.cv p))
      (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))) p0056 p0055
  have p0077 := @g_elsni (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))
  have p0078 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (.cv x) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))))
      (.classEq (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))) p0076 p0077
  have p0079 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) p0078
  have p0080 :=
    @g_sneqd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (.cv x) p0079
  have p0081 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p))))
      (syn_csn (.cv x)) p0055 p0080
  have p0082 :=
    @g_opeq12d
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (syn_cfv (syn_c1st) (.cv p)) (.cv v) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv x))
      p0036 p0081
  have p0083 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))
      (syn_cop (.cv v) (syn_csn (.cv x))) p0018 p0082
  have p0084 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x)))) p0010 p0083
  have p0085 :=
    @g_eleq1d
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v) p0084
  have p0086 :=
    @g_mpbid
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.classMem (.cv p) (syn_chncodepredinputs A X v))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) p0011
      p0085
  have p0087 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
  have p0088 :=
    @g_hncodepredinputmemndv x v u A X dv_cache_0005 dv_cache_0004 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0089 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0087 p0088
  have p0090 :=
    @g_mpbid
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0086 p0089
  have p0091 :=
    @g_rexlimdvaa (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p (syn_chncodepredinputs A X v) dv_cache_0009 dv_cache_0010 p0090
  have p0092 :=
    @g_syld (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0009 p0091
  have p0093 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
  have p0094 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
  have p0096 :=
    @g_biimprd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0088
  have p0097 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (.classMem (.cv v) (syn_chwcn A))
      (.imp (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))))
        (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)))
      p0094 p0096
  have p0098 :=
    @g_mpd
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) p0093
      p0097
  have p0099 := @g_vex x
  have p0100 := @g_snid (.cv x) p0099
  have p0101 := @g_vex v
  have p0102 := @g_snex (.cv x)
  have p0103 := @g_opfv2nd (.cv v) (syn_csn (.cv x)) p0101 p0102
  have p0104 :=
    @g_eleqtrri (.cv x) (syn_csn (.cv x))
      (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))) p0100 p0103
  have p0105 :=
    @g_a1i (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0104
  have p0106 :=
    @g_jca
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))) p0098
      p0105
  have p0107 := @g_id (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))))
  have p0108 :=
    @g_fveq2d (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x)))) (.cv p)
      (syn_cop (.cv v) (syn_csn (.cv x))) (syn_c2nd) p0107
  have p0109 :=
    @g_eleq2d (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (.cv p))
      (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))) (.cv x) p0108
  have p0110 :=
    @g_rspcev (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))) p
      (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v) dv_cache_0011
      dv_cache_0001 dv_cache_0012 p0109
  have p0111 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      p0106 p0110
  have p0120 :=
    @g_biimpri (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      p0007
  have p0121 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wrex p (syn_chncodepredinputs A X v)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
      (.classMem (.cv x) (syn_chncodepredends A X v)) p0111 p0120
  have p0122 :=
    @g_ex (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_chncodepredends A X v)) p0121
  have p0123 :=
    @g_impbid (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0092 p0122
  exact p0123

@[expose]
noncomputable def g_hncodepredendsssndv (v : Var) (A : Class) (X : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (syn_chwcn A))
        (syn_wss (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v)))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ A.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_X, not_false_eq_true])
  have dv_cache_0004 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0006 : x ∉ ((syn_chncodepredends A X v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X,
          fresh_x_ne_v, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @g_hncodepredendsmemndv x v u A X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_biimpd (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0000
  have p0002 :=
    @g_simpl (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0003 :=
    @g_syl6 (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0001 p0002
  have p0004 :=
    @g_ssrdv (.classMem (.cv v) (syn_chwcn A)) x (syn_chncodepredends A X v)
      (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutcodetransportintocutsegndv (x : Var) (y : Var) (z : Var)
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wrex z
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_ne_v : w ≠ v := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0004 :
    w ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0006 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0007 : Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ z } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show z ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show z ≠ v from (by exact Ne.symm dv_v_z)))))))),
                  (show Disjoint (({ z } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0008 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_z), (Ne.symm dv_y_z),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_u_z), fresh_z_ne_w,
          (Ne.symm dv_v_z), dv_A_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    w ∉
      ((syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_v, fresh_w_ne_y,
          fresh_w_ne_x, fresh_w_ne_u, fresh_w_ne_z, fresh_w_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_A, fresh_w_ne_v, fresh_w_ne_y,
          fresh_w_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0000
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0000
  have p0008 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))
      p0005 p0007
  have p0009 := @g_hnwcutcodeambientndv y v A dv_cache_0001
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv y)) (syn_chwcn A))
      p0008 p0009
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv y)) (syn_chwcn A))
      p0002 p0010
  have p0012 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0013 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0012
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0012
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
          (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0011 p0016
  have p0018 :=
    @g_hnwcutcodetransporttgtclndv x w u A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
            (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex w (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
      p0017 p0018
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv w) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0021 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv w) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0029 := @g_hnwcutcodepartsndv y v A dv_cache_0001
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      p0008 p0029
  have p0031 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0022 p0031
  have p0033 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
      (.cv w) p0032
  have p0034 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0021 p0033
  have p0036 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0046 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0030
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      p0022 p0046
  have p0059 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0047 p0032
  have p0060 :=
    @g_hnwcutcodeeq12ndv w
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)) (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv w)))
      p0059 p0060
  have p0066 := @g_hwcnweclndv A (.cv v)
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0005
      p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0022
      p0067
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0022 p0007
  have p0073 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0068 p0072
  have p0089 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0073 p0034
  have p0090 :=
    @g_hnwcutcodenestndv w y (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv w)
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv w))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0089 p0090
  have p0092 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.cv w))
      (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      p0061 p0091
  have p0093 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0092
  have p0094 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0036 p0093
  have p0095 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0034 p0094
  have p0096 :=
    @g_hnwcutcodeeq3 (.cv z) (.cv w) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) dv_cache_0007
  have p0097 :=
    @g_breq2d (.classEq (.cv z) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0096
  have p0098 :=
    @g_rspcev
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      z (.cv w)
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0097
  have p0099 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      p0095 p0098
  have p0100 :=
    @g_rexlimddv
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      w
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      dv_cache_0011 dv_cache_0012 p0019 p0099
  exact p0100


end NFChoice.DirectNominalPrf.WPPReplay

end
