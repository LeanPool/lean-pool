/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part047`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpstrictminndv (y : Var) (u : Var) (A : Class) (q : Var)
    (_dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_q_u : q ≠ u)
    (dv_q_y : q ≠ y) (dv_u_y : u ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
              (.classEq (.cv y) (.cv u)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ q } : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_q : v ≠ q := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : v ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_q, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_q_y), not_false_eq_true])
  have dv_cache_0005 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv u) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_y), fresh_y_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0007 : u ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_v, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_q_u), not_false_eq_true])
  have dv_cache_0009 :
    u ∉
      ((syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
            (.classEq (.cv y) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, (Ne.symm dv_q_u), dv_u_y, fresh_u_ne_v, dv_A_u, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0011 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0012 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0013 :
    v ∉
      ((syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
              (.classEq (.cv y) (.cv u)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_ne_q, fresh_v_ne_y, fresh_v_ne_u, fresh_v_not_A,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    v ∉
      ((syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0001 :=
    @g_simprd
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)) p0000
  have p0002 := @g_n0 v (.cv q) dv_cache_0001
  have p0003 :=
    @g_biimpi (syn_wne (.cv q) (syn_c0)) (syn_wex v (.classMem (.cv v) (.cv q))) p0002
  have p0004 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (syn_wne (.cv q) (syn_c0)) (syn_wex v (.classMem (.cv v) (.cv q))) p0001 p0003
  have p0005 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0006 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (.classMem (.cv v) (.cv q))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem (.cv v) (.cv q)) p0005 p0006
  have p0009 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (.classMem (.cv v) (.cv q))
  have p0010 :=
    @g_simpl (.classMem A (syn_cvv))
      (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (.classMem A (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem A (syn_cvv)) p0005 p0011
  have p0016 :=
    @g_simpld
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)) p0000
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (syn_wss (.cv q) (syn_chwcn A)) p0009 p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wss (.cv q) (syn_chwcn A)) p0005 p0017
  have p0022 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)) p0018 p0007
  have p0023 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))) p0012 p0022
  have p0024 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))))
      (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_hncodepredemptyminimalndv y v A (.cv q) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))))
        (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      p0025 p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (.classMem (.cv v) (.cv q))
      (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      p0007 p0027
  have p0029 :=
    @g_breq2 (.cv u) (.cv v) (.cv y)
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
  have p0030 := @g_eqeq2 (.cv u) (.cv v) (.cv y)
  have p0031 :=
    @g_imbi12d (.classEq (.cv u) (.cv v))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
      (.classEq (.cv y) (.cv u)) (.classEq (.cv y) (.cv v)) p0029 p0030
  have p0032 :=
    @g_ralbidv (.classEq (.cv u) (.cv v))
      (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)) (.classEq (.cv y) (.cv u)))
      (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)) (.classEq (.cv y) (.cv v)))
      y (.cv q) dv_cache_0006 p0031
  have p0033 :=
    @g_rspcev
      (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
          (.classEq (.cv y) (.cv u))))
      (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      u (.cv v) (.cv q) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (.classMem (.cv v) (.cv q)) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
            (.classEq (.cv y) (.cv v)))))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0028 p0033
  have p0035 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0034
  have p0036 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem A (syn_cvv)) p0036 p0011
  have p0041 := @g_vex q
  have p0042 :=
    @g_a1i (.classMem (.cv q) (syn_cvv))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      p0041
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv)) p0040 p0042
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wss (.cv q) (syn_chwcn A)) p0036 p0017
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem (.cv v) (.cv q)) p0036 p0006
  have p0053 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)) p0049 p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv)))
      (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))) p0043 p0053
  have p0055 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0056 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv)))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))))
      (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)) p0054 p0055
  have p0057 :=
    @g_hncodeprednonemptyminimalndv y v u A (.cv q) dv_cache_0010 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0011 dv_cache_0012 dv_cache_0005
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
          (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv)))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))))
        (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0056 p0057
  have p0059 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0058
  have p0060 :=
    @g_pm2_61dne
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (.classMem (.cv v) (.cv q)))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      (syn_chncodepredends A (.cv q) v) (syn_c0) p0035 p0059
  have p0061 :=
    @g_exlimddv
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
      (.classMem (.cv v) (.cv q))
      (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      v dv_cache_0013 dv_cache_0014 p0004 p0060
  exact p0061

@[expose]
noncomputable def g_hncodecmpstrictfrndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv))
        (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (syn_cfound) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_y : q ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0005 : q ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ y from (by exact fresh_q_ne_y))
  have dv_cache_0006 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0007 : q ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_y_not_A, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0010 :
    q ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_q_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0012 :
    u ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_q_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : y ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show y ≠ u from (by exact fresh_y_ne_u))
  have p0000 := @g_hncodecmpsetexg A
  have p0002 := @g_cnvexg (syn_chncodecmpset A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv)) p0000 p0003
  have p0005 :=
    @g_difexg (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv))
        (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv)))
      (.classMem (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cvv))
      p0004 p0005
  have p0007 := @g_hwcnexg A
  have p0008 :=
    @g_hncodecmpstrictminndv y u A q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))
        (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
              (.objEq y u))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin
          syn_wnan syn_ccompl syn_cdif syn_cin syn_chncodecmpset syn_ccnv syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0008
  have p0009 :=
    @g_frrd (.classMem A (syn_cvv)) q y u (syn_chwcn A)
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0005 dv_cache_0004 dv_cache_0014 p0006 p0007 p0009_e02_recanon
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmplnpwcndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_clnpwc (syn_chwcn A)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_r_ne_d : r ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have dv_cache_0001 : r ∉ ((syn_cop (syn_chncodecmpset A) (syn_chwcn A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_r_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 :
    r ∉ ((Wff.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels, Finset.mem_union,
          fresh_r_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    r ∉
      ((syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
            (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_r_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_d_not_A, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0007 : d ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_d_not_A, not_false_eq_true])
  have dv_cache_0008 :
    r ∉
      ((syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (syn_cfound) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_r_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    d ∉
      ((syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (syn_cfound) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_d_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : r ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ d from (by exact fresh_r_ne_d))
  have dv_cache_0011 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have p0000 := @g_hncodecmpsetrefndv A
  have p0001 := @g_hncodecmpsettransndv A
  have p0002 :=
    @g_jca (.classMem A (syn_cvv))
      (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0000 p0001
  have p0003 := @g_hncodecmpsetconnexndv A
  have p0004 :=
    @g_jca (.classMem A (syn_cvv))
      (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
        (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
      (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_clntp))
  have p0006 :=
    @g_breqi (syn_chncodecmpset A) (syn_chwcn A) (syn_clntp)
      (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) p0005
  have p0007 :=
    @g_brin (syn_chncodecmpset A) (syn_chwcn A) (syn_cin (syn_cref) (syn_ctrans))
      (syn_cconnex)
  have p0008 := @g_brin (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) (syn_ctrans)
  have p0009 :=
    @g_anbi1i
      (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cref) (syn_ctrans)) (syn_chwcn A))
      (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
        (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
      (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0008
  have p0010 :=
    @g_bitri
      (syn_wbr (syn_chncodecmpset A)
        (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) (syn_chwcn A))
      (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cref) (syn_ctrans)) (syn_chwcn A))
        (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)))
      (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
          (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)))
      p0007 p0009
  have p0011 :=
    @g_bitri (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A)
        (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) (syn_chwcn A))
      (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
          (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)))
      p0006 p0010
  have p0012 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (syn_wa
          (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
            (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
          (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))))
      (.classMem A (syn_cvv)) p0011
  have p0013 :=
    @g_mpbird (.classMem A (syn_cvv))
      (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A))
      (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
          (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)))
      p0004 p0012
  have p0014 :=
    (Nominal.biimpRefl (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)))
  have p0015 :=
    @g_biimpi (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) p0014
  have p0016 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) p0013 p0015
  have p0017 := @g_hncodecmpsetssxpndv A
  have p0018 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (.classMem A (syn_cvv)) p0017
  have p0019 := @g_hncodecmpsetexg A
  have p0020 := @g_hwcnexg A
  have p0021 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0019 p0020
  have p0022 := @g_opexg (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0023 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv)) p0021 p0022
  have p0024 :=
    @g_eleq1 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)
  have p0025 := @g_fveq2 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_c1st)
  have p0026 := @g_fveq2 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_c2nd)
  have p0028 :=
    @g_xpeq12d (.classEq (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
      (syn_cfv (syn_c2nd) (.cv r))
      (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
      (syn_cfv (syn_c2nd) (.cv r))
      (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) p0026 p0026
  have p0029 :=
    @g_sseq12d (.classEq (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
      (syn_cfv (syn_c1st) (.cv r))
      (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (.cv r)))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))))
      p0025 p0028
  have p0030 := @g_elhwrrels r
  have p0031 :=
    @g_vtoclbg (.classMem (.cv r) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (.cv r))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (.cv r))))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))))
      r (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0024 p0029 p0030
  have p0032 :=
    @g_syl (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))
        (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
            (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))))))
      p0023 p0031
  have p0036 := @g_opfvscl (syn_chncodecmpset A) (syn_chwcn A)
  have p0037 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_chncodecmpset A))
        (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_chwcn A)))
      p0021 p0036
  have p0038 :=
    @g_simpld (.classMem A (syn_cvv))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_chncodecmpset A))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_chwcn A))
      p0037
  have p0044 :=
    @g_simprd (.classMem A (syn_cvv))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_chncodecmpset A))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_chwcn A))
      p0037
  have p0051 :=
    @g_xpeq12d (.classMem A (syn_cvv))
      (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A)
      (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A)
      p0044 p0044
  have p0052 :=
    @g_sseq12d (.classMem A (syn_cvv))
      (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
      (syn_chncodecmpset A)
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))))
      (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0038 p0051
  have p0053 :=
    @g_bitrd (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))
          (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0032 p0052
  have p0054 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0018 p0053
  have p0055 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) p0016 p0054
  have p0056 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp) (syn_chwrels)
  have p0057 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cin (syn_clntp) (syn_chwrels)))
        (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp))
          (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))))
      (.classMem A (syn_cvv)) p0056
  have p0058 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cin (syn_clntp) (syn_chwrels)))
      (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp))
        (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)))
      p0055 p0057
  have p0061 := @g_snidg (syn_chwcn A) (syn_cvv)
  have p0062 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))) p0020 p0061
  have p0063 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))) p0019 p0062
  have p0064 :=
    @g_opelxp (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_csn (syn_chwcn A))
  have p0065 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))
        (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv))
          (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A)))))
      (.classMem A (syn_cvv)) p0064
  have p0066 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))
      (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv))
        (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))))
      p0063 p0065
  have p0067 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cin (syn_clntp) (syn_chwrels)))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))
      p0058 p0066
  have p0068 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
      (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))
  have p0069 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cin (syn_cin (syn_clntp) (syn_chwrels))
            (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))) (syn_wa
          (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
            (syn_cin (syn_clntp) (syn_chwrels)))
          (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
            (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))))
      (.classMem A (syn_cvv)) p0068
  have p0070 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cin (syn_cin (syn_clntp) (syn_chwrels))
          (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))))
      (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cin (syn_clntp) (syn_chwrels)))
        (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))))
      p0067 p0069
  have p0071 := (Nominal.classEqRefl (syn_clntpc (syn_chwcn A)))
  have p0072 :=
    @g_a1i
      (.classEq (syn_clntpc (syn_chwcn A)) (syn_cin (syn_cin (syn_clntp) (syn_chwrels))
          (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))))
      (.classMem A (syn_cvv)) p0071
  have p0073 :=
    @g_eleqtrrd (.classMem A (syn_cvv)) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
      (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))
      (syn_clntpc (syn_chwcn A)) p0070 p0072
  have p0074 := @g_hncodecmpstrictfrndv A
  have p0078 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))
  have p0080 :=
    @g_cnveqd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A)))
      (.cv r) (syn_chncodecmpset A) p0078
  have p0081 :=
    @g_difeq12d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A)))
      (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A))
      p0078 p0080
  have p0082 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))
  have p0083 :=
    @g_breq12d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A)))
      (syn_cdif (.cv r) (syn_ccnv (.cv r)))
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv d)
      (syn_chwcn A) (syn_cfound) p0081 p0082
  have p0084 :=
    @g_opelopabga (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      r d (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_cvv) dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0083
  have p0085 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
        (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (syn_cfound) (syn_chwcn A)))
      p0021 p0084
  have p0086 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d
          (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      p0074 p0085
  have p0087 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A)))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d
          (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
      p0073 p0086
  have p0088 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A))
      (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))
  have p0089 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d
              (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (syn_wa
          (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A)))
          (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d
              (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))))
      (.classMem A (syn_cvv)) p0088
  have p0090 :=
    @g_mpbird (.classMem A (syn_cvv))
      (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
        (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))
      (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_clntpc (syn_chwcn A))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
          (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))
      p0087 p0089
  have p0091 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnpwc (syn_chwcn A)
      r d dv_cache_0007 dv_cache_0006 dv_cache_0011
  have p0092 :=
    @g_a1i
      (.classEq (syn_clnpwc (syn_chwcn A)) (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))
      (.classMem A (syn_cvv)) p0091
  have p0093 :=
    @g_eleqtrrd (.classMem A (syn_cvv)) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))
      (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d
          (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
      (syn_clnpwc (syn_chwcn A)) p0090 p0092
  exact p0093

@[expose]
noncomputable def g_hnordlnquoeqimndv (A : Class) (r : Var) (_dv_A_r : r ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
        (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnquo (.cv r) (syn_chwcn A)))
  have p0001 :=
    @g_a1i
      (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0000
  have p0002 := @g_qseq2 (syn_clnker (.cv r)) (syn_chwniso A) (syn_chwcn A)
  have p0003 := (Nominal.classEqRefl (syn_chnord A))
  have p0004 := @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0003
  have p0005 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0004
  have p0006 :=
    @g_n_3eqtrd (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r)))
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0001 p0002 p0005
  exact p0006

@[expose]
noncomputable def g_hnordwendv (A : Class) (s : Var) (dv_A_s : s ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ s } : Finset Var)
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_ne_s : r ≠ s := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ ((syn_chncodecmpset A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_s, fresh_s_ne_r, or_false, not_false_eq_true])
  have dv_cache_0004 :
    s ∉ ((syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, dv_A_s, fresh_s_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    s ∉ ((syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, dv_A_s, fresh_s_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_ne_s, fresh_r_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_r_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_hncodecmpsetexg A
  have p0001 := @g_isset r (syn_chncodecmpset A) dv_cache_0001
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (syn_chncodecmpset A) (syn_cvv))
        (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))))
      (.classMem A (syn_cvv)) p0001
  have p0003 :=
    @g_biimpd (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0002
  have p0004 :=
    @g_mpd (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))
      (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0000 p0003
  have p0005 := @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0005 p0000
  have p0008 := @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_eleq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0008
  have p0010 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0007
      p0009
  have p0012 := @g_hwcnexg A
  have p0013 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0005 p0012
  have p0014 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0010 p0013
  have p0016 := @g_hncodecmpsetrefndv A
  have p0017 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0005 p0016
  have p0019 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0008
  have p0020 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0017 p0019
  have p0022 := @g_hncodecmpsettransndv A
  have p0023 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))
      p0005 p0022
  have p0025 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0008
  have p0026 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0023 p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0020 p0026
  have p0029 := @g_hncodecmpsetconnexndv A
  have p0030 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))
      p0005 p0029
  have p0032 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cconnex) p0008
  have p0033 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0030 p0032
  have p0034 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
        (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) p0027 p0033
  have p0035 := @g_hncodecmpsetssxpndv A
  have p0036 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) p0035
  have p0038 :=
    @g_sseq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0008
  have p0039 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0036 p0038
  have p0040 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
          (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0034 p0039
  have p0041 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
            (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
          (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
        (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      p0014 p0040
  have p0043 := @g_hncodecmpstrictfrndv A
  have p0044 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      p0005 p0043
  have p0047 :=
    @g_cnveqd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) p0008
  have p0048 :=
    @g_difeq12d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A))
      p0008 p0047
  have p0049 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_cdif (.cv r) (syn_ccnv (.cv r)))
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_chwcn A)
      (syn_cfound) p0048
  have p0050 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      p0044 p0049
  have p0051 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
              (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
            (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
          (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
      (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)) p0041
      p0050
  have p0052 := @g_lnqordwe (syn_chwcn A) (.cv r) dv_cache_0002
  have p0053 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
          (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
                (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
              (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
            (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
        (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A)))
      p0051 p0052
  have p0055 := @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0056 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0008 p0055
  have p0058 := @g_hncodecmplnkerndv A
  have p0059 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv))
      (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0005 p0058
  have p0060 :=
    @g_eqtrd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0056 p0059
  have p0061 := (Nominal.classEqRefl (syn_clnquo (.cv r) (syn_chwcn A)))
  have p0062 :=
    @g_a1i
      (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0061
  have p0063 := @g_qseq2 (syn_clnker (.cv r)) (syn_chwniso A) (syn_chwcn A)
  have p0064 := (Nominal.classEqRefl (syn_chnord A))
  have p0065 := @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0064
  have p0066 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0065
  have p0067 :=
    @g_n_3eqtrd (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r)))
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0062 p0063 p0066
  have p0068 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A)) p0060 p0067
  have p0069 :=
    @g_breq2d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A)
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) p0068
  have p0070 :=
    @g_mpbid (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0053 p0069
  have p0081 := @g_lnqordexg (syn_chwcn A) (.cv r) dv_cache_0002
  have p0082 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) p0014 p0081
  have p0083 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
  have p0084 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
      (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_chnord A) (syn_cwe) p0083
  have p0085 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0084
  have p0086 :=
    @g_spcimedv (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) s
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0082 p0085
  have p0087 :=
    @g_mpd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A))
      (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) p0070 p0086
  have p0088 :=
    @g_exlimddv (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) r dv_cache_0006 dv_cache_0007
      p0004 p0087
  exact p0088


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncardhwcardsndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncard A) (syn_chwcards (syn_cvv)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let s : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (h)
  have fresh_s_ne_t : s ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_s : t ≠ s := Ne.symm fresh_s_ne_t
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_t_ne_d : t ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_t : d ≠ t := Ne.symm fresh_t_ne_d
  have fresh_t_ne_k : t ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_t : k ≠ t := Ne.symm fresh_t_ne_k
  have fresh_d_ne_k : d ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_d : k ≠ d := Ne.symm fresh_d_ne_k
  have dv_cache_0001 : s ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_A, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_d_not_A, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_t_not_A, not_false_eq_true])
  have dv_cache_0004 : d ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_s, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_s, not_false_eq_true])
  have dv_cache_0006 :
    d ∉
      ((syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
          (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_s, fresh_d_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
          (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_s, fresh_t_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : d ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0009 :
    s ∉
      ((syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
              (.classEq (syn_chncard A) (syn_cnc (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_ne_t, fresh_s_ne_d,
          fresh_s_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Wff.classEq (.cv k) (syn_chncard A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_k, fresh_t_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (syn_chncard A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_k, fresh_d_not_A, or_false, not_false_eq_true])
  have dv_cache_0012 : d ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0013 : k ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show k ≠ t from (by exact fresh_k_ne_t))
  have dv_cache_0014 : k ∉ ((syn_chncard A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          fresh_k_not_A, not_false_eq_true])
  have dv_cache_0015 :
    k ∉
      ((syn_wb (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t
              (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
                (.classEq (syn_chncard A) (syn_cnc (.cv d)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_not_A, fresh_k_ne_t,
          fresh_k_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_hnordwendv A s dv_cache_0001
  have p0001 := @g_id (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
  have p0002 := (Nominal.classEqRefl (syn_chncard A))
  have p0003 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A)))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) p0002
  have p0004 :=
    @g_jca (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) p0001 p0003
  have p0005 := @g_brex (.cv s) (syn_chnord A) (syn_cwe)
  have p0006 :=
    @g_ancom (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv))
  have p0007 :=
    @g_sylibr (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv)))
      (syn_wa (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv))) p0005
      p0006
  have p0008 := @g_simpr (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))
  have p0009 := @g_simpl (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))
  have p0010 :=
    @g_breq12d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s)))
      (.cv t) (.cv s) (.cv d) (syn_chnord A) (syn_cwe) p0008 p0009
  have p0012 :=
    @g_nceqd (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))) (.cv d)
      (syn_chnord A) p0009
  have p0013 :=
    @g_eqeq2d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s)))
      (syn_cnc (.cv d)) (syn_cnc (syn_chnord A)) (syn_chncard A) p0012
  have p0014 :=
    @g_anbi12d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s)))
      (syn_wbr (.cv t) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (.classEq (syn_chncard A) (syn_cnc (.cv d)))
      (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) p0010 p0013
  have p0015 :=
    @g_spc2egv
      (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
        (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))
      d t (syn_chnord A) (.cv s) (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wa (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv)))
      (.imp (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
          (.classEq (syn_chncard A) (syn_cnc (syn_chnord A)))) (syn_wex d (syn_wex t
            (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
              (.classEq (syn_chncard A) (syn_cnc (.cv d)))))))
      p0007 p0015
  have p0017 :=
    @g_mpd (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
        (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (syn_chncard A) (syn_cnc (.cv d))))))
      p0004 p0016
  have p0018 :=
    @g_exlimiv (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (syn_chncard A) (syn_cnc (.cv d))))))
      s dv_cache_0009 p0017
  have p0019 := @g_hncardex A
  have p0020 := @g_id (.classEq (.cv k) (syn_chncard A))
  have p0021 :=
    @g_eleq1d (.classEq (.cv k) (syn_chncard A)) (.cv k) (syn_chncard A)
      (syn_chwcards (syn_cvv)) p0020
  have p0023 :=
    @g_eqeq1d (.classEq (.cv k) (syn_chncard A)) (.cv k) (syn_chncard A) (syn_cnc (.cv d))
      p0020
  have p0024 :=
    @g_anbi2d (.classEq (.cv k) (syn_chncard A)) (.classEq (.cv k) (syn_cnc (.cv d)))
      (.classEq (syn_chncard A) (syn_cnc (.cv d))) (syn_wbr (.cv t) (syn_cwe) (.cv d))
      p0023
  have p0025 :=
    @g_exbidv (.classEq (.cv k) (syn_chncard A))
      (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))
      t dv_cache_0010 p0024
  have p0026 :=
    @g_exbidv (.classEq (.cv k) (syn_chncard A))
      (syn_wex t
        (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))
      (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
          (.classEq (syn_chncard A) (syn_cnc (.cv d)))))
      d dv_cache_0011 p0025
  have p0027 :=
    @g_bibi12d (.classEq (.cv k) (syn_chncard A))
      (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (.classMem (syn_chncard A) (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (syn_chncard A) (syn_cnc (.cv d))))))
      p0021 p0026
  have p0028 := @g_elhwcardswev k t d dv_cache_0012 dv_cache_0008 dv_cache_0013
  have p0029 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t
            (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))))
      (syn_wb (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t
            (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
              (.classEq (syn_chncard A) (syn_cnc (.cv d)))))))
      k (syn_chncard A) (syn_cvv) dv_cache_0014 dv_cache_0015 p0027 p0028
  have p0030 := Nominal.mp p0019 p0029
  have p0031 :=
    @g_biimpri (.classMem (syn_chncard A) (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (syn_chncard A) (syn_cnc (.cv d))))))
      p0030
  have p0032 :=
    @g_syl (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
      (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d))
            (.classEq (syn_chncard A) (syn_cnc (.cv d))))))
      (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) p0018 p0031
  have p0033 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
      (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) p0000 p0032
  exact p0033

@[expose]
noncomputable def g_wppconcrete6canonicaltchomndv (X : Class)
    (hyp_wppconcrete6canonicaltchomndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))) :=
  by
  have p0000 := @g_wppconcrete6fnvalndv X hyp_wppconcrete6canonicaltchomndv_1
  have p0001 :=
    @g_tceq
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0004 := @g_pwex (syn_cpw X) p0003
  have p0005 := @g_hnordexg (syn_cpw (syn_cpw X))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_hncardtcshiftndv (syn_chnord (syn_cpw (syn_cpw X))) p0006
  have p0008 :=
    @g_eqtri
      (syn_ctc (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_ctc (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))))
      (syn_chncard (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))) p0002 p0007
  have p0013 := @g_pw1ex (syn_chnord (syn_cpw (syn_cpw X))) p0006
  have p0014 := @g_pw1ex X hyp_wppconcrete6canonicaltchomndv_1
  have p0015 := @g_pwex (syn_cpw1 X) p0014
  have p0016 := @g_pwex (syn_cpw (syn_cpw1 X)) p0015
  have p0017 := @g_hnordexg (syn_cpw (syn_cpw (syn_cpw1 X)))
  have p0018 := Nominal.mp p0016 p0017
  have p0021 := @g_hnordpw1shiftenndv (syn_cpw (syn_cpw X)) p0004
  have p0027 :=
    @g_eqnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))
      (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))) p0013
  have p0028 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))))
        (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))))
      (syn_wbr (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))) (syn_cen)
        (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))))
      p0021 p0027
  have p0029 := (Nominal.classEqRefl (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X)))))
  have p0030 :=
    @g_eqcomi (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X))))
      (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))) p0029
  have p0033 := @g_pw1ex (syn_cpw (syn_cpw X)) p0004
  have p0037 := @g_ncpw1pw2 X hyp_wppconcrete6canonicaltchomndv_1
  have p0038 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cpw (syn_cpw X))) (syn_cpw (syn_cpw (syn_cpw1 X)))
      p0033 p0016 p0037
  have p0039 := (Nominal.classEqRefl (syn_chncard (syn_cpw (syn_cpw (syn_cpw1 X)))))
  have p0040 :=
    @g_eqtri (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X))))
      (syn_chncard (syn_cpw (syn_cpw (syn_cpw1 X))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0038 p0039
  have p0041 :=
    @g_eqtri (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))))
      (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0030 p0040
  have p0042 :=
    @g_eqtri (syn_cnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))))
      (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0028 p0041
  have p0043 :=
    @g_hncardnceqndv (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))
      (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X)))) p0013 p0018 p0042
  have p0044 :=
    @g_eqtri
      (syn_ctc (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_chncard (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0008 p0043
  have p0045 := @g_tcnc X hyp_wppconcrete6canonicaltchomndv_1
  have p0046 := @g_eqcomi (syn_ctc (syn_cnc X)) (syn_cnc (syn_cpw1 X)) p0045
  have p0047 := @g_tceq (syn_cnc (syn_cpw1 X)) (syn_ctc (syn_cnc X))
  have p0048 := Nominal.mp p0046 p0047
  have p0049 := @g_tceq (syn_ctc (syn_cnc (syn_cpw1 X))) (syn_ctc (syn_ctc (syn_cnc X)))
  have p0050 := Nominal.mp p0048 p0049
  have p0051 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))
  have p0052 := Nominal.mp p0050 p0051
  have p0053 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))
  have p0056 := Nominal.mp p0054 p0055
  have p0057 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @g_fveq2i
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_cwppconcrete6fn) p0058
  have p0060 :=
    @g_eqcomi
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))))))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      p0059
  have p0062 := @g_wppconcrete6fnvalndv (syn_cpw1 X) p0014
  have p0063 :=
    @g_eqtri
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0060 p0062
  have p0064 :=
    @g_eqcomi
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0063
  have p0065 :=
    @g_eqtri
      (syn_ctc (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X)))))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      p0044 p0064
  exact p0065

@[expose]
noncomputable def g_hncardtc6oneeqndv :
    Nominal.NPrf
      (.classEq (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @g_pw1ex (syn_c1c) p0000
  have p0006 := @g_hncardtcshiftndv (syn_cpw1 (syn_c1c)) p0005
  have p0007 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_c1c))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0009 := Nominal.mp p0007 p0008
  have p0012 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0005
  have p0013 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0020 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0021 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0022 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0016 p0021
  have p0023 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0024 := Nominal.mp p0022 p0023
  have p0029 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0030 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0031 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0024
      p0030
  have p0032 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0033 := Nominal.mp p0031 p0032
  have p0039 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0040 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0039
  have p0041 :=
    @g_eqtri
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0033 p0040
  exact p0041

@[expose]
noncomputable def g_hncardtc7oneeqndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_chncard (syn_cpw1 (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @g_pw1ex (syn_c1c) p0000
  have p0006 := @g_hncardtcshiftndv (syn_cpw1 (syn_c1c)) p0005
  have p0007 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_c1c))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0009 := Nominal.mp p0007 p0008
  have p0012 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0005
  have p0013 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0020 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0021 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0022 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0016 p0021
  have p0023 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0024 := Nominal.mp p0022 p0023
  have p0029 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0030 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0031 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0024
      p0030
  have p0032 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0033 := Nominal.mp p0031 p0032
  have p0039 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0040 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0039
  have p0041 :=
    @g_eqtri
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0033 p0040
  have p0042 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0043 := Nominal.mp p0041 p0042
  have p0050 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0039
  have p0051 :=
    @g_hncardtcshiftndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0050
  have p0052 :=
    @g_eqtri
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_ctc (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0043 p0051
  exact p0052

@[expose]
noncomputable def g_wppconcrete6thresholdtclecndv :
    Nominal.NPrf
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) :=
  by
  have p0000 := @g_pw1ss1c (syn_c1c)
  have p0001 := @g_pw1ss (syn_cpw1 (syn_c1c)) (syn_c1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_c1c))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_n_1cex
  have p0014 := @g_pw1ex (syn_c1c) p0013
  have p0015 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0014
  have p0016 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0015
  have p0017 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0016
  have p0018 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0017
  have p0019 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0018
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0019
  have p0028 :=
    @g_hncardmono
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0012 p0020 p0019
  have p0029 := @g_hncardtc7oneeqndv
  have p0030 := @g_hncardtc6oneeqndv
  have p0031 :=
    @g_breq12i
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_clec) p0029 p0030
  have p0032 :=
    @g_mpbir
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_clec) (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0028 p0031
  exact p0032

@[expose]
noncomputable def g_hnwpw1argclcndv (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (.classMem C (syn_cpw1 D))
        (syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0003 :
    q ∉ ((syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_q_not_C, fresh_q_not_D, or_false, not_false_eq_true])
  have p0000 := @g_unieq (.cv q) C
  have p0001 := @g_eleq1d (.classEq (.cv q) C) (syn_cuni (.cv q)) (syn_cuni C) D p0000
  have p0002 := @g_id (.classEq (.cv q) C)
  have p0004 := @g_sneqd (.classEq (.cv q) C) (syn_cuni (.cv q)) (syn_cuni C) p0000
  have p0005 :=
    @g_eqeq12d (.classEq (.cv q) C) (.cv q) C (syn_csn (syn_cuni (.cv q)))
      (syn_csn (syn_cuni C)) p0002 p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv q) C) (.classMem (syn_cuni (.cv q)) D)
      (.classMem (syn_cuni C) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
      (.classEq C (syn_csn (syn_cuni C))) p0001 p0005
  have p0007 := @g_hnwpw1argcl D q
  have p0008 :=
    @g_vtoclga
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C)))) q C
      (syn_cpw1 D) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_wppsifnndv (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wfn (syn_csi F) (syn_cpw1 A))) :=
  by
  have p0000 := @g_fnfun A F
  have p0001 := @g_funsi F
  have p0002 := @g_syl (syn_wfn F A) (syn_wfun F) (syn_wfun (syn_csi F)) p0000 p0001
  have p0003 := @g_dmsi F
  have p0004 :=
    @g_a1i (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F))) (syn_wfn F A) p0003
  have p0005 := @g_fndm A F
  have p0006 := @g_pw1eq (syn_cdm F) A
  have p0007 :=
    @g_syl (syn_wfn F A) (.classEq (syn_cdm F) A)
      (.classEq (syn_cpw1 (syn_cdm F)) (syn_cpw1 A)) p0005 p0006
  have p0008 :=
    @g_eqtrd (syn_wfn F A) (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F)) (syn_cpw1 A) p0004
      p0007
  have p0009 :=
    @g_jca (syn_wfn F A) (syn_wfun (syn_csi F))
      (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 A)) p0002 p0008
  have p0010 := (Nominal.biimpRefl (syn_wfn (syn_csi F) (syn_cpw1 A)))
  have p0011 :=
    @g_sylibr (syn_wfn F A)
      (syn_wa (syn_wfun (syn_csi F)) (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 A)))
      (syn_wfn (syn_csi F) (syn_cpw1 A)) p0009 p0010
  exact p0011

@[expose]
noncomputable def g_wpptxpfnvalndv (x : Var) (A : Class) (F : Class) (G : Class)
    (_dv_A_x : x ∉ A.fv) (_dv_F_x : x ∉ F.fv) (_dv_G_x : x ∉ G.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
        (.classEq (syn_cfv (syn_ctxp F G) (.cv x))
          (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) :=
  by
  have p0000 := @g_eqid (syn_cfv F (.cv x))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) p0000
  have p0002 := @g_simpl (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0003 := @g_simpl (syn_wfn F A) (syn_wfn G A)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn F A) p0002 p0003
  have p0005 := @g_simpr (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0006 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wfn F A) (.classMem (.cv x) A) p0004 p0005
  have p0007 := @g_fnbrfvb A (.cv x) (syn_cfv F (.cv x)) F
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (syn_wb (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x)))
        (syn_wbr (.cv x) F (syn_cfv F (.cv x))))
      p0006 p0007
  have p0009 :=
    @g_mpbid (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x)))
      (syn_wbr (.cv x) F (syn_cfv F (.cv x))) p0001 p0008
  have p0010 := @g_eqid (syn_cfv G (.cv x))
  have p0011 :=
    @g_a1i (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) p0010
  have p0013 := @g_simpr (syn_wfn F A) (syn_wfn G A)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn G A) p0002 p0013
  have p0016 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wfn G A) (.classMem (.cv x) A) p0014 p0005
  have p0017 := @g_fnbrfvb A (.cv x) (syn_cfv G (.cv x)) G
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn G A) (.classMem (.cv x) A))
      (syn_wb (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x)))
        (syn_wbr (.cv x) G (syn_cfv G (.cv x))))
      p0016 p0017
  have p0019 :=
    @g_mpbid (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x)))
      (syn_wbr (.cv x) G (syn_cfv G (.cv x))) p0011 p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wbr (.cv x) F (syn_cfv F (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x)))
      p0009 p0019
  have p0021 := @g_trtxp (.cv x) (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) F G
  have p0022 :=
    @g_sylibr (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wbr (.cv x) F (syn_cfv F (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x))))
      (syn_wbr (.cv x) (syn_ctxp F G) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      p0020 p0021
  have p0024 := @g_fntxp A A F G
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn (syn_ctxp F G) (syn_cin A A)) p0002
      p0024
  have p0026 := @g_inidm A
  have p0027 := @g_fneq2i (syn_cin A A) A (syn_ctxp F G) p0026
  have p0028 :=
    @g_sylib (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wfn (syn_ctxp F G) (syn_cin A A)) (syn_wfn (syn_ctxp F G) A) p0025 p0027
  have p0030 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wfn (syn_ctxp F G) A) (.classMem (.cv x) A) p0028 p0005
  have p0031 :=
    @g_fnbrfvb A (.cv x) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) (syn_ctxp F G)
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wa (syn_wfn (syn_ctxp F G) A) (.classMem (.cv x) A))
      (syn_wb (.classEq (syn_cfv (syn_ctxp F G) (.cv x))
          (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wbr (.cv x) (syn_ctxp F G)
          (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))
      p0030 p0031
  have p0033 :=
    @g_mpbird (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (.classEq (syn_cfv (syn_ctxp F G) (.cv x))
        (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      (syn_wbr (.cv x) (syn_ctxp F G) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      p0022 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part050`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pw1xpshiftsetndv (A : Class) (B : Class) (p : Var) (dv_A_p : p ∉ A.fv)
    (dv_B_p : p ∉ B.fv) (hyp_pw1xpshiftsetndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_pw1xpshiftsetndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cmpt p (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : p ∉ ((syn_cpw1 (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_csi (syn_c1st))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_csi (syn_c2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cpw1 (syn_cxp A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, dv_A_p,
          dv_B_p, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_cxp A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    p ∉
      ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    p ∉
      ((syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
          (syn_cpw1 (syn_cxp A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, dv_A_p,
          dv_B_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    p ∉
      ((syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_p, dv_B_p, fresh_p_ne_q,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0001 :=
    @g_fvres (.cv p) (syn_cpw1 (syn_cxp A B))
      (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
  have p0002 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classEq (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
            (syn_cpw1 (syn_cxp A B))) (.cv p))
        (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p)))
      p0000 p0001
  have p0003 := @g_n_1stfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_wppsifnndv (syn_cvv) (syn_c1st)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_n_2ndfo
  have p0009 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_wppsifnndv (syn_cvv) (syn_c2nd)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
      (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) p0007 p0012
  have p0014 :=
    @g_a1i
      (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
        (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0013
  have p0016 := @g_ssv (syn_cxp A B)
  have p0017 := @g_pw1ss (syn_cxp A B) (syn_cvv)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_sseli (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv)) (.cv p) p0018
  have p0020 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0000 p0019
  have p0021 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
        (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))))
      (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0014 p0020
  have p0022 :=
    @g_wpptxpfnvalndv p (syn_cpw1 (syn_cvv)) (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0023 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
          (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))))
        (.classMem (.cv p) (syn_cpw1 (syn_cvv))))
      (.classEq (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p))
        (syn_cop (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_cfv (syn_csi (syn_c2nd)) (.cv p))))
      p0021 p0022
  have p0024 := @g_eqid (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0028 := @g_vex p
  have p0029 := @g_uniex (.cv p) p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
      p0005 p0029
  have p0031 :=
    @g_fnbrfvb (syn_cvv) (syn_cuni (.cv p)) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_c1st)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_wbr (syn_cuni (.cv p)) (syn_c1st) (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      p0024 p0032
  have p0036 := @g_fvex (syn_cuni (.cv p)) (syn_c1st)
  have p0037 :=
    @g_brsnsi (syn_cuni (.cv p)) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_c1st) p0029
      p0036
  have p0038 :=
    @g_mpbir
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st))
        (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      (syn_wbr (syn_cuni (.cv p)) (syn_c1st) (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      p0033 p0037
  have p0039 :=
    @g_a1i
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st))
        (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0038
  have p0040 := @g_hnwpw1argcl (syn_cxp A B) p
  have p0041 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0042 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0040 p0041
  have p0043 :=
    @g_breq1d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p)
      (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csi (syn_c1st)) p0042
  have p0044 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wbr (.cv p) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st))
        (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      p0039 p0043
  have p0050 :=
    @g_a1i (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0007
  have p0057 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
      (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0050 p0020
  have p0058 :=
    @g_fnbrfvb (syn_cpw1 (syn_cvv)) (.cv p)
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csi (syn_c1st))
  have p0059 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv)))
        (.classMem (.cv p) (syn_cpw1 (syn_cvv))))
      (syn_wb (.classEq (syn_cfv (syn_csi (syn_c1st)) (.cv p))
          (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
        (syn_wbr (.cv p) (syn_csi (syn_c1st))
          (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))))
      p0057 p0058
  have p0060 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classEq (syn_cfv (syn_csi (syn_c1st)) (.cv p))
        (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      (syn_wbr (.cv p) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      p0044 p0059
  have p0061 := @g_eqid (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0067 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
      p0010 p0029
  have p0068 :=
    @g_fnbrfvb (syn_cvv) (syn_cuni (.cv p)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
      (syn_c2nd)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_wbr (syn_cuni (.cv p)) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      p0061 p0069
  have p0073 := @g_fvex (syn_cuni (.cv p)) (syn_c2nd)
  have p0074 :=
    @g_brsnsi (syn_cuni (.cv p)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_c2nd) p0029
      p0073
  have p0075 :=
    @g_mpbir
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_wbr (syn_cuni (.cv p)) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      p0070 p0074
  have p0076 :=
    @g_a1i
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0075
  have p0080 :=
    @g_breq1d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p)
      (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_csi (syn_c2nd)) p0042
  have p0081 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wbr (.cv p) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0076 p0080
  have p0087 :=
    @g_a1i (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0012
  have p0094 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))
      (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0087 p0020
  have p0095 :=
    @g_fnbrfvb (syn_cpw1 (syn_cvv)) (.cv p)
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csi (syn_c2nd))
  have p0096 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))
        (.classMem (.cv p) (syn_cpw1 (syn_cvv))))
      (syn_wb (.classEq (syn_cfv (syn_csi (syn_c2nd)) (.cv p))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
        (syn_wbr (.cv p) (syn_csi (syn_c2nd))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0094 p0095
  have p0097 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classEq (syn_cfv (syn_csi (syn_c2nd)) (.cv p))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_wbr (.cv p) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0081 p0096
  have p0098 :=
    @g_opeq12d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cfv (syn_csi (syn_c1st)) (.cv p))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_cfv (syn_csi (syn_c2nd)) (.cv p))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0060 p0097
  have p0099 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p))
      (syn_cop (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_cfv (syn_csi (syn_c2nd)) (.cv p)))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0023 p0098
  have p0100 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
          (syn_cpw1 (syn_cxp A B))) (.cv p))
      (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0002 p0099
  have p0101 := @g_id (.classEq (.cv p) (.cv q))
  have p0102 := @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0101
  have p0103 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c1st)
      p0102
  have p0104 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0103
  have p0105 := @g_id (.classEq (.cv p) (.cv q))
  have p0106 := @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0105
  have p0107 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c2nd)
      p0106
  have p0108 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0107
  have p0109 :=
    @g_opeq12d (.classEq (.cv p) (.cv q))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0104 p0108
  have p0110_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_cfv syn_cio syn_cuni syn_wbr syn_c1st syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0110 :=
    @g_cbvmptv p q (syn_cpw1 (syn_cxp A B))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0110_e00_recanon
  have p0111 :=
    @g_fveq1i (.cv p)
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      (syn_cmpt q (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      p0110
  have p0112 :=
    @g_eqcomi
      (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p))
      (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p))
      p0111
  have p0113 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)) (syn_cfv
          (syn_cmpt p (syn_cpw1 (syn_cxp A B))
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0112
  have p0115 := @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0116 := @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0117 :=
    @g_opex (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0115 p0116
  have p0118 :=
    @g_a1i
      (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0117
  have p0119 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv))
      p0000 p0118
  have p0120 :=
    @g_eqid
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0121 :=
    @g_fvmpt2 p (syn_cpw1 (syn_cxp A B))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cvv)
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      dv_cache_0004 p0120
  have p0122 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv)))
      (.classEq (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B))
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0119 p0121
  have p0123 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p))
      (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0113 p0122
  have p0124 :=
    @g_eqtr4d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
          (syn_cpw1 (syn_cxp A B))) (.cv p))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p))
      p0100 p0123
  have p0125 :=
    @g_rgen
      (.classEq (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
            (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)))
      p (syn_cpw1 (syn_cxp A B)) p0124
  have p0137 :=
    @g_fntxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_c1st))
      (syn_csi (syn_c2nd))
  have p0138 := Nominal.mp p0013 p0137
  have p0139 := @g_inidm (syn_cpw1 (syn_cvv))
  have p0140 :=
    @g_fneq2i (syn_cin (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cvv))
      (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) p0139
  have p0141 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
        (syn_cin (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))))
      (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cvv)))
      p0138 p0140
  have p0145 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cvv)))
      (syn_wss (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv))) p0141 p0018
  have p0146 :=
    @g_fnssres (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cxp A B))
      (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
  have p0147 := Nominal.mp p0145 p0146
  have p0148 := @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
  have p0149 := @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
  have p0150 :=
    @g_opex (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0148 p0149
  have p0151 :=
    @g_eqid
      (syn_cmpt q (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
  have p0152 :=
    @g_fnmpti q (syn_cpw1 (syn_cxp A B))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_cmpt q (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      dv_cache_0005 p0150 p0151
  have p0153 :=
    @g_pm3_2i
      (syn_wfn (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
          (syn_cpw1 (syn_cxp A B))) (syn_cpw1 (syn_cxp A B)))
      (syn_wfn (syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cxp A B)))
      p0147 p0152
  have p0154 :=
    @g_eqfnfv p (syn_cpw1 (syn_cxp A B))
      (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B)))
      (syn_cmpt q (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      dv_cache_0004 dv_cache_0008 dv_cache_0009
  have p0155 := Nominal.mp p0153 p0154
  have p0156 :=
    @g_mpbir
      (.classEq (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
          (syn_cpw1 (syn_cxp A B))) (syn_cmpt q (syn_cpw1 (syn_cxp A B))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))))
      (syn_wral p (syn_cpw1 (syn_cxp A B)) (.classEq (syn_cfv
            (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
              (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B))
              (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p))))
      p0125 p0155
  have p0157 := @g_id (.classEq (.cv p) (.cv q))
  have p0158 := @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0157
  have p0159 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c1st)
      p0158
  have p0160 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0159
  have p0161 := @g_id (.classEq (.cv p) (.cv q))
  have p0162 := @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0161
  have p0163 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c2nd)
      p0162
  have p0164 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0163
  have p0165 :=
    @g_opeq12d (.classEq (.cv p) (.cv q))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0160 p0164
  have p0166_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_cfv syn_cio syn_cuni syn_wbr syn_c1st syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0165
  have p0166 :=
    @g_cbvmptv p q (syn_cpw1 (syn_cxp A B))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0166_e00_recanon
  have p0167 :=
    @g_eqtr4i
      (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B)))
      (syn_cmpt q (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0156 p0166
  have p0168 := @g_n_1stex
  have p0169 := @g_siex (syn_c1st) p0168
  have p0170 := @g_n_2ndex
  have p0171 := @g_siex (syn_c2nd) p0170
  have p0172 := @g_txpex (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)) p0169 p0171
  have p0173 := @g_xpex A B hyp_pw1xpshiftsetndv_1 hyp_pw1xpshiftsetndv_2
  have p0174 := @g_pw1ex (syn_cxp A B) p0173
  have p0175 :=
    @g_resex (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))
      p0172 p0174
  have p0176 :=
    @g_eqeltrri
      (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B)))
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      (syn_cvv) p0167 p0175
  exact p0176


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pw1xpshiftenndv (A : Class) (B : Class)
    (hyp_pw1xpshiftenndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_pw1xpshiftenndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cpw1 (syn_cxp A B)) (syn_cen) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((syn_cpw1 (syn_cxp A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cxp A B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cxp (syn_cpw1 A) (syn_cpw1 B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cxp (syn_cpw1 A) (syn_cpw1 B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    p ∉
      ((syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : p ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : q ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0010 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0011 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have p0000 := @g_tru
  have p0001 :=
    @g_eqid
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0002 := @g_simpr syn_wtru (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0003 := @g_hnwpw1argcl (syn_cxp A B) p
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0005 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) p0003 p0004
  have p0006 := @g_id (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
  have p0007 := @g_n_1st2nd2 (syn_cuni (.cv p)) A B
  have p0008 :=
    @g_eleq1d (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (syn_cuni (.cv p))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_cxp A B) p0007
  have p0009 :=
    @g_mpbid (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B))
      p0006 p0008
  have p0010 :=
    @g_opelxp (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) A B
  have p0011 :=
    @g_sylib (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
        (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B))
      p0009 p0010
  have p0012 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
        (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B))
      p0005 p0011
  have p0013 :=
    @g_simpl (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
      (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)
  have p0014 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
        (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B))
      (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) p0012 p0013
  have p0015 := @g_snelpw1 (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A
  have p0016 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
      (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A)) p0014
      p0015
  have p0027 :=
    @g_simpr (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
      (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)
  have p0028 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A)
        (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B))
      (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B) p0012 p0027
  have p0029 := @g_snelpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B
  have p0030 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)
      (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B)) p0028
      p0029
  have p0031 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A))
      (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B)) p0016
      p0030
  have p0032 :=
    @g_opelxp (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 A) (syn_cpw1 B)
  have p0033 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A))
        (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B)))
      (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
        (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      p0031 p0032
  have p0034 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
        (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      p0002 p0033
  have p0035 := @g_simpr syn_wtru (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0036 := @g_id (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0037 := @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0038 :=
    @g_eleq1d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q)
      (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)))
      (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) p0037
  have p0039 :=
    @g_mpbid (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)))
        (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      p0036 p0038
  have p0040 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 A)
      (syn_cpw1 B)
  have p0041 :=
    @g_sylib (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)))
        (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
        (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)))
      p0039 p0040
  have p0042 :=
    @g_simpl (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
      (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0043 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
        (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) p0041 p0042
  have p0044 := @g_hnwpw1argclcndv (syn_cfv (syn_c1st) (.cv q)) A
  have p0045 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
      (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))
  have p0046 :=
    @g_syl (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
        (.classEq (syn_cfv (syn_c1st) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))))
      (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) p0044 p0045
  have p0047 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
      (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) p0043 p0046
  have p0054 :=
    @g_simpr (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
      (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0055 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
        (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) p0041 p0054
  have p0056 := @g_hnwpw1argclcndv (syn_cfv (syn_c2nd) (.cv q)) B
  have p0057 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)
      (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
  have p0058 :=
    @g_syl (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)
        (.classEq (syn_cfv (syn_c2nd) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0056 p0057
  have p0059 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
      (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0055 p0058
  have p0060 :=
    @g_jca (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
      (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0047 p0059
  have p0061 :=
    @g_opelxp (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) A B
  have p0062 :=
    @g_sylibr (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
        (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B))
      (.classMem (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cxp A B))
      p0060 p0061
  have p0063 :=
    @g_snelpw1
      (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))
      (syn_cxp A B)
  have p0064 :=
    @g_sylibr (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cxp A B))
      (.classMem (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cpw1 (syn_cxp A B)))
      p0062 p0063
  have p0065 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cpw1 (syn_cxp A B)))
      p0035 p0064
  have p0066 :=
    @g_simpr
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
  have p0067 :=
    @g_unieqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (.cv p)
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      p0066
  have p0068 :=
    @g_fveq2d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cuni (.cv p))
      (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (syn_c1st) p0067
  have p0069 :=
    @g_sneqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      p0068
  have p0072 :=
    @g_fveq2d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cuni (.cv p))
      (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (syn_c2nd) p0067
  have p0073 :=
    @g_sneqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      p0072
  have p0074 :=
    @g_opeq12d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
              (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
              (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))
      p0069 p0073
  have p0075 :=
    @g_simpl
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
  have p0076 :=
    @g_simpr syn_wtru
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
        (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
  have p0077 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0078 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
        (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0076 p0077
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0075 p0078
  have p0080 := @g_fvex (.cv q) (syn_c1st)
  have p0081 := @g_uniex (syn_cfv (syn_c1st) (.cv q)) p0080
  have p0082 := @g_fvex (.cv q) (syn_c2nd)
  have p0083 := @g_uniex (syn_cfv (syn_c2nd) (.cv q)) p0082
  have p0084 :=
    @g_opex (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0081 p0083
  have p0085 :=
    @g_unisn
      (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))
      p0084
  have p0086 :=
    @g_fveq2i
      (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))
      (syn_c1st) p0085
  have p0091 :=
    @g_opfv1st (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0081 p0083
  have p0092 :=
    @g_eqtri
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cfv (syn_c1st) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (syn_cuni (syn_cfv (syn_c1st) (.cv q))) p0086 p0091
  have p0093 :=
    @g_sneqi
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cuni (syn_cfv (syn_c1st) (.cv q))) p0092
  have p0100 :=
    @g_fveq2i
      (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))
      (syn_c2nd) p0085
  have p0105 :=
    @g_opfv2nd (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0081 p0083
  have p0106 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0100 p0105
  have p0107 :=
    @g_sneqi
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0106
  have p0108 :=
    @g_opeq12i
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
              (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))
      (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
              (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))
      (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0093 p0107
  have p0109 :=
    @g_a1i
      (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                  (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                    (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd)
              (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                    (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))))
        (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
          (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0108
  have p0120 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
        (.classEq (syn_cfv (syn_c1st) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))))
      p0043 p0044
  have p0121 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
      (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))
  have p0122 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A)
        (.classEq (syn_cfv (syn_c1st) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))))
      (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))
      p0120 p0121
  have p0132 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)
        (.classEq (syn_cfv (syn_c2nd) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      p0055 p0056
  have p0133 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)
      (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
  have p0134 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)
        (.classEq (syn_cfv (syn_c2nd) (.cv q))
          (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      p0132 p0133
  have p0135 :=
    @g_opeq12d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
      (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0122
      p0134
  have p0136 :=
    @g_eqtrd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q)
      (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)))
      (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
        (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      p0037 p0135
  have p0137 :=
    @g_eqcomd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q)
      (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
        (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      p0136
  have p0138 :=
    @g_eqtrd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))))
      (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))
        (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (.cv q) p0109 p0137
  have p0139 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
      (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                  (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                    (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd)
              (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                    (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))) (.cv q))
      p0079 p0138
  have p0140 :=
    @g_eqtrd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))))
      (.cv q) p0074 p0139
  have p0141 :=
    @g_eqcomd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn
            (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (.cv q) p0140
  have p0142 :=
    @g_simpr
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0143 :=
    @g_fveq2d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (.cv q)
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_c1st) p0142
  have p0144 :=
    @g_unieqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cfv (syn_c1st) (.cv q))
      (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0143
  have p0146 :=
    @g_fveq2d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (.cv q)
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_c2nd) p0142
  have p0147 :=
    @g_unieqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cfv (syn_c2nd) (.cv q))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0146
  have p0148 :=
    @g_opeq12d
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
      (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))
      (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      p0144 p0147
  have p0149 :=
    @g_sneqd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))
      p0148
  have p0150 :=
    @g_simpl
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0152 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0153 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
        (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0076 p0152
  have p0154 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0150 p0153
  have p0155 := @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0156 := @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0157 :=
    @g_opfv1st (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0155 p0156
  have p0158 :=
    @g_unieqi
      (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) p0157
  have p0159 := @g_fvex (syn_cuni (.cv p)) (syn_c1st)
  have p0160 := @g_unisn (syn_cfv (syn_c1st) (syn_cuni (.cv p))) p0159
  have p0161 :=
    @g_eqtri
      (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cuni (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))
      (syn_cfv (syn_c1st) (syn_cuni (.cv p))) p0158 p0160
  have p0164 :=
    @g_opfv2nd (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0155 p0156
  have p0165 :=
    @g_unieqi
      (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0164
  have p0166 := @g_fvex (syn_cuni (.cv p)) (syn_c2nd)
  have p0167 := @g_unisn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0166
  have p0168 :=
    @g_eqtri
      (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cuni (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0165 p0167
  have p0169 :=
    @g_opeq12i
      (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
      (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0161 p0168
  have p0170 :=
    @g_a1i
      (.classEq (syn_cop (syn_cuni (syn_cfv (syn_c1st)
              (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni
            (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))
        (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0169
  have p0175 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classEq (syn_cuni (.cv p)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      p0005 p0007
  have p0176 :=
    @g_eqtr4d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))
      (syn_cuni (.cv p)) p0170 p0175
  have p0177 :=
    @g_sneqd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_cop (syn_cuni (syn_cfv (syn_c1st)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd)
            (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
              (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))
      (syn_cuni (.cv p)) p0176
  have p0179 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0180 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0003 p0179
  have p0181 :=
    @g_eqcomd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p)
      (syn_csn (syn_cuni (.cv p))) p0180
  have p0182 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st)
              (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni
            (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))))
      (syn_csn (syn_cuni (.cv p))) (.cv p) p0177 p0181
  have p0183 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
      (.classEq (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st)
                (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                  (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni
              (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                  (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))) (.cv p))
      p0154 p0182
  have p0184 :=
    @g_eqtrd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st)
              (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni
            (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
                (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))))
      (.cv p) p0149 p0183
  have p0185 :=
    @g_eqcomd
      (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
            (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q)
          (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
            (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (.cv p) p0184
  have p0186 :=
    @g_impbida
      (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
          (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))))
      (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
      (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0141 p0185
  have p0187 :=
    @g_f1o2d syn_wtru p q (syn_cpw1 (syn_cxp A B)) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))
      (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))
      (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0034 p0065 p0186
  have p0188 := Nominal.mp p0000 p0187
  have p0189 :=
    @g_pw1xpshiftsetndv A B p dv_cache_0010 dv_cache_0011 hyp_pw1xpshiftenndv_1
      hyp_pw1xpshiftenndv_2
  have p0190 :=
    @g_f1oen (syn_cpw1 (syn_cxp A B)) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))
      (syn_cmpt p (syn_cpw1 (syn_cxp A B))
        (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))
          (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
      p0189
  have p0191 := Nominal.mp p0188 p0190
  exact p0191

@[expose]
noncomputable def g_wppqkrelpw1shiftenndv (X : Class)
    (hyp_wppqkrelpw1shiftenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))) :=
  by
  have p0000 :=
    @g_wppqkrelrestypedenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0001 := @g_enpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cxpk X X)
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cxpk X X))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen)
        (syn_cpw1 (syn_cxpk X X)))
      p0000 p0001
  have p0003 :=
    @g_ensym (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cpw1 (syn_cxpk X X))
  have p0004 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen)
        (syn_cpw1 (syn_cxpk X X)))
      (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))))
      p0002 p0003
  have p0005 :=
    @g_pw1xpshiftenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0006 := @g_enpw1 (syn_cpw1 (syn_cxp X X)) (syn_cxp (syn_cpw1 X) (syn_cpw1 X))
  have p0007 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cxp X X)) (syn_cen) (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen)
        (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X))))
      p0005 p0006
  have p0008 :=
    @g_enpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))
      (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))
  have p0009 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen)
        (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X))))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen)
        (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))))
      p0007 p0008
  have p0010 := @g_pw1ex X hyp_wppqkrelpw1shiftenndv_1
  have p0012 := @g_wppqkrelrestypedenndv (syn_cpw1 X) (syn_cpw1 X) p0010 p0010
  have p0013 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen)
        (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))) (syn_cen)
        (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)))
      p0009 p0012
  have p0014 :=
    @g_entr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))))
      (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X))))
      (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen)
        (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)))
      p0004 p0015
  have p0017 :=
    @g_entr (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))))
      (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

@[expose]
noncomputable def g_wpplitshiftenndv (X : Class)
    (hyp_wpplitshiftenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc))) :=
  by
  have p0000 := @g_xpkex X X hyp_wpplitshiftenndv_1 hyp_wpplitshiftenndv_1
  have p0001 := @g_nncex
  have p0002 := @g_pw1xpshiftenndv (syn_cxpk X X) (syn_cnnc) p0000 p0001
  have p0003 := @g_wppqkrelpw1shiftenndv X hyp_wpplitshiftenndv_1
  have p0004 := @g_tcnnf1o
  have p0005 := @g_tcfnex
  have p0007 := @g_pw1ex (syn_cnnc) p0001
  have p0008 := @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0005 p0007
  have p0009 :=
    @g_f1oen (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))
      p0008
  have p0010 := Nominal.mp p0004 p0009
  have p0011 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)))
      (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc)) p0003 p0010
  have p0012 :=
    @g_xpen (syn_cpw1 (syn_cxpk X X)) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))
      (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc))))
      (syn_wbr (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc)))
      p0002 p0013
  have p0015 :=
    @g_entr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc)))
      (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc))
  have p0016 := Nominal.mp p0014 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6dmrepdndv (x : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (syn_wex z (.classEq (.cv x)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ z } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_q : z ≠ q := Ne.symm fresh_q_ne_z
  have dv_cache_0001 :
    q ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_x, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cwppcardt6fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    z ∉ ((syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_q,
          not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_z_ne_q, (Ne.symm dv_x_z),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_z, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_wppconcrete6fndmndv
  have p0001 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv x) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) p0001
  have p0003 := @g_wppcardt6fnmapndv
  have p0004 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_fvelrnb q
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.cv x)
      (syn_cwppcardt6fn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_biimpi (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn)))
      (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      p0007
  have p0009 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn)))
      (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      p0002 p0008
  have p0010 :=
    @g_simpl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
  have p0011 :=
    @g_id
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0012 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.cv q)
  have p0013 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (.cv q))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0011 p0012
  have p0014 :=
    @g_simpl
      (.classMem (syn_cuni (.cv q))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0015 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (.cv q))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0013 p0014
  have p0016 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cuni (.cv q))
  have p0017 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (.cv q))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q)))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
        (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0015 p0016
  have p0018 :=
    @g_simpl
      (.classMem (syn_cuni (syn_cuni (.cv q)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0019 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q)))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
        (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (.classMem (syn_cuni (syn_cuni (.cv q)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0017 p0018
  have p0020 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (syn_cuni (syn_cuni (.cv q)))
  have p0021 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (.cv q)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q)))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      p0019 p0020
  have p0022 :=
    @g_simpl
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classEq (syn_cuni (syn_cuni (.cv q)))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0023 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q)))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0021 p0022
  have p0024 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs)))
      (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0025 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
      p0023 p0024
  have p0026 :=
    @g_simpl
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0027 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0025 p0026
  have p0028 :=
    @g_pw1argclcl (syn_cpw1 (syn_cncs))
      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
  have p0029 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
          (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      p0027 p0028
  have p0030 :=
    @g_simpl
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
        (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0031 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
          (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
        (syn_cpw1 (syn_cncs)))
      p0029 p0030
  have p0032 :=
    @g_pw1argclcl (syn_cncs)
      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0033 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
        (syn_cpw1 (syn_cncs)))
      (syn_wa (.classMem
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs))
        (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      p0031 p0032
  have p0034 :=
    @g_simpl
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0035 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs))
        (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      p0033 p0034
  have p0036 :=
    @g_elncs z (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      dv_cache_0004
  have p0037 :=
    @g_biimpi
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      (syn_wex z (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      p0036
  have p0038 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      (syn_wex z (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      p0035 p0037
  have p0039 :=
    @g_syl
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wex z (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      p0010 p0038
  have p0040 :=
    @g_simpl
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cnc (.cv z)))
  have p0041 :=
    @g_simpr
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
  have p0042 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x) p0041
  have p0047 :=
    @g_simpr
      (.classMem (syn_cuni (.cv q))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0048 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (.cv q))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0013 p0047
  have p0056 :=
    @g_simpr
      (.classMem (syn_cuni (syn_cuni (.cv q)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0057 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q)))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
        (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0017 p0056
  have p0069 :=
    @g_simpr
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classEq (syn_cuni (syn_cuni (.cv q)))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0070 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q)))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      (.classEq (syn_cuni (syn_cuni (.cv q)))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
      p0021 p0069
  have p0086 :=
    @g_simpr
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0087 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      p0025 p0086
  have p0107 :=
    @g_simpr
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
        (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0108 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
          (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
      p0029 p0107
  have p0132 :=
    @g_simpr
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0133 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (.classMem
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs))
        (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      p0033 p0132
  have p0134 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0135 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_csn (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      p0133 p0134
  have p0136 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      (syn_csn (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      p0108 p0135
  have p0137 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_csn
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0138 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_csn
            (syn_csn (syn_cuni
                (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
      p0136 p0137
  have p0139 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_cuni (syn_cuni (syn_cuni (.cv q))))
      (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_csn (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      p0087 p0138
  have p0140 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
      (syn_csn (syn_csn (syn_csn
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
  have p0141 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_cuni
                (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
      (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
      p0139 p0140
  have p0142 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
      p0070 p0141
  have p0143 :=
    @g_sneq (syn_cuni (syn_cuni (.cv q)))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
  have p0144 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
      (.classEq (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      p0142 p0143
  have p0145 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
      p0057 p0144
  have p0146 :=
    @g_sneq (syn_cuni (.cv q))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
  have p0147 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cuni (.cv q)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      (.classEq (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_cuni (syn_cuni
                        (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      p0145 p0146
  have p0148 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.cv q) (syn_csn (syn_cuni (.cv q)))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      p0048 p0147
  have p0149 :=
    @g_fveq2 (.cv q)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      (syn_cwppcardt6fn)
  have p0150 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni
                      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_cfv (syn_cwppcardt6fn) (syn_csn
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni
                          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))))
      p0148 p0149
  have p0176 :=
    @g_wppcardt6fnvalsingndv
      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0177 :=
    @g_syl
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cncs))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_cuni (syn_cuni
                          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni
                        (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      p0035 p0176
  have p0178 :=
    @g_eqtrd
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_cfv (syn_cwppcardt6fn) (.cv q))
      (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_cuni (syn_cuni
                        (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      p0150 p0177
  have p0179 :=
    @g_syl
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_cuni (syn_cuni
                        (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      p0010 p0178
  have p0180 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.cv x) (syn_cfv (syn_cwppcardt6fn) (.cv q))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      p0042 p0179
  have p0181 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                      (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))
      p0040 p0180
  have p0182 :=
    @g_simpr
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cnc (.cv z)))
  have p0183 :=
    @g_tceq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cnc (.cv z))
  have p0184 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cnc (.cv z)))
      (.classEq (syn_ctc
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
        (syn_ctc (syn_cnc (.cv z))))
      p0182 p0183
  have p0185 :=
    @g_tceq
      (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
      (syn_ctc (syn_cnc (.cv z)))
  have p0186 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_ctc
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
        (syn_ctc (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
        (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
      p0184 p0185
  have p0187 :=
    @g_tceq
      (syn_ctc (syn_ctc
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
      (syn_ctc (syn_ctc (syn_cnc (.cv z))))
  have p0188 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
        (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc
              (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
      p0186 p0187
  have p0189 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc
            (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
  have p0190 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc
              (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
      p0188 p0189
  have p0191 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
  have p0192 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      p0190 p0191
  have p0193 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                  (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
  have p0194 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni
                        (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0192 p0193
  have p0195 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv q)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
          (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (.cv x)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni
                    (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0181
      p0194
  have p0196 :=
    @g_ex
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cnc (.cv z)))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0195
  have p0197 :=
    @g_eximdv
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
        (syn_cnc (.cv z)))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      z dv_cache_0005 p0196
  have p0198 :=
    @g_mpd
      (syn_wa (.classMem (.cv q)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (syn_wex z (.classEq
          (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
          (syn_cnc (.cv z))))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0039 p0197
  have p0199 :=
    @g_ex
      (.classMem (.cv q)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0198
  have p0200 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      dv_cache_0006 p0199
  have p0201 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0009 p0200
  exact p0201


end NFChoice.DirectNominalPrf.WPPReplay

end
