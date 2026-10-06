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

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpstrictminndv`. -/
@[expose]
noncomputable def gHncodecmpstrictminndv (y : Var) (u : Var) (A : Class) (q : Var)
    (_dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_q_u : q ≠ u)
    (dv_q_y : q ≠ y) (dv_u_y : u ≠ y) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
                (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
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
      ((synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
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
      ((synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
                (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
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
      ((synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))).fv :=
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
    @gSimpr (.classMem A (synCvv))
      (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0)))
  have p0001 :=
    @gSimprd
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0)) p0000
  have p0002 := @gN0 v (.cv q) dv_cache_0001
  have p0003 :=
    @gBiimpi (synWne (.cv q) (synC0)) (synWex v (.classMem (.cv v) (.cv q))) p0002
  have p0004 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (synWne (.cv q) (synC0)) (synWex v (.classMem (.cv v) (.cv q))) p0001 p0003
  have p0005 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (synChncodepredends A (.cv q) v) (synC0))
  have p0006 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (.classMem (.cv v) (.cv q))
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem (.cv v) (.cv q)) p0005 p0006
  have p0009 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (.classMem (.cv v) (.cv q))
  have p0010 :=
    @gSimpl (.classMem A (synCvv))
      (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0)))
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (.classMem A (synCvv)) p0009 p0010
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem A (synCvv)) p0005 p0011
  have p0016 :=
    @gSimpld
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0)) p0000
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (synWss (.cv q) (synChwcn A)) p0009 p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWss (.cv q) (synChwcn A)) p0005 p0017
  have p0022 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q)) p0018 p0007
  have p0023 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (.classMem A (synCvv))
      (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))) p0012 p0022
  have p0024 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (synChncodepredends A (.cv q) v) (synC0))
  have p0025 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))))
      (.classEq (synChncodepredends A (.cv q) v) (synC0)) p0023 p0024
  have p0026 :=
    @gHncodepredemptyminimalndv y v A (.cv q) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))))
        (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWral y (.cv q) (.imp (synWbr (.cv y)
            (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      p0025 p0026
  have p0028 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (.classMem (.cv v) (.cv q))
      (synWral y (.cv q) (.imp (synWbr (.cv y)
            (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      p0007 p0027
  have p0029 :=
    @gBreq2 (.cv u) (.cv v) (.cv y)
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
  have p0030 := @gEqeq2 (.cv u) (.cv v) (.cv y)
  have p0031 :=
    @gImbi12d (.classEq (.cv u) (.cv v))
      (synWbr (.cv y) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv u))
      (synWbr (.cv y) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv v))
      (.classEq (.cv y) (.cv u)) (.classEq (.cv y) (.cv v)) p0029 p0030
  have p0032 :=
    @gRalbidv (.classEq (.cv u) (.cv v))
      (.imp (synWbr (.cv y) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv u)) (.classEq (.cv y) (.cv u)))
      (.imp (synWbr (.cv y) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv v)) (.classEq (.cv y) (.cv v)))
      y (.cv q) dv_cache_0006 p0031
  have p0033 :=
    @gRspcev
      (synWral y (.cv q) (.imp (synWbr (.cv y)
            (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
          (.classEq (.cv y) (.cv u))))
      (synWral y (.cv q) (.imp (synWbr (.cv y)
            (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
          (.classEq (.cv y) (.cv v))))
      u (.cv v) (.cv q) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (.classEq (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (.classMem (.cv v) (.cv q)) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
            (.classEq (.cv y) (.cv v)))))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0028 p0033
  have p0035 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classEq (synChncodepredends A (.cv q) v) (synC0))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0034
  have p0036 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWne (synChncodepredends A (.cv q) v) (synC0))
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem A (synCvv)) p0036 p0011
  have p0041 := @gVex q
  have p0042 :=
    @gA1i (.classMem (.cv q) (synCvv))
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      p0041
  have p0043 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (.classMem A (synCvv)) (.classMem (.cv q) (synCvv)) p0040 p0042
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWss (.cv q) (synChwcn A)) p0036 p0017
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (.classMem (.cv v) (.cv q)) p0036 p0006
  have p0053 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q)) p0049 p0052
  have p0054 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (.classMem A (synCvv)) (.classMem (.cv q) (synCvv)))
      (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))) p0043 p0053
  have p0055 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWne (synChncodepredends A (.cv q) v) (synC0))
  have p0056 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (.classMem A (synCvv)) (.classMem (.cv q) (synCvv)))
        (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))))
      (synWne (synChncodepredends A (.cv q) v) (synC0)) p0054 p0055
  have p0057 :=
    @gHncodeprednonemptyminimalndv y v u A (.cv q) dv_cache_0010 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0011 dv_cache_0012 dv_cache_0005
  have p0058 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv))
            (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
          (.classMem (.cv v) (.cv q))) (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (.classMem (.cv q) (synCvv)))
          (synWa (synWss (.cv q) (synChwcn A)) (.classMem (.cv v) (.cv q))))
        (synWne (synChncodepredends A (.cv q) v) (synC0)))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0056 p0057
  have p0059 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWne (synChncodepredends A (.cv q) v) (synC0))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      p0058
  have p0060 :=
    @gPm261dne
      (synWa (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (.classMem (.cv v) (.cv q)))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      (synChncodepredends A (.cv q) v) (synC0) p0035 p0059
  have p0061 :=
    @gExlimddv
      (synWa (.classMem A (synCvv))
        (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
      (.classMem (.cv v) (.cv q))
      (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
              (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u)))))
      v dv_cache_0013 dv_cache_0014 p0004 p0060
  exact p0061

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpstrictfrndv`. -/
@[expose]
noncomputable def gHncodecmpstrictfrndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv))
        (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (synCfound) (synChwcn A))) :=
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
  have dv_cache_0007 : q ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0008 : y ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0009 : u ∉ ((synChwcn A)).fv :=
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
    q ∉ ((synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))).fv :=
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
    y ∉ ((synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))).fv :=
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
    u ∉ ((synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))).fv :=
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
  have dv_cache_0013 : q ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have p0000 := @gHncodecmpsetexg A
  have p0002 := @gCnvexg (synChncodecmpset A) (synCvv)
  have p0003 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (.classMem (synCcnv (synChncodecmpset A)) (synCvv)) p0000 p0002
  have p0004 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (.classMem (synCcnv (synChncodecmpset A)) (synCvv)) p0000 p0003
  have p0005 :=
    @gDifexg (synChncodecmpset A) (synCcnv (synChncodecmpset A)) (synCvv) (synCvv)
  have p0006 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecmpset A) (synCvv))
        (.classMem (synCcnv (synChncodecmpset A)) (synCvv)))
      (.classMem (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (synCvv))
      p0004 p0005
  have p0007 := @gHwcnexg A
  have p0008 :=
    @gHncodecmpstrictminndv y u A q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (synWss (.cv q) (synChwcn A)) (synWne (.cv q) (synC0))))
        (synWrex u (.cv q) (synWral y (.cv q) (.imp (synWbr (.cv y)
                (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
              (.objEq y u))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCvv synWrex synWex synWral synWbr synCop synCun synCnin
          synWnan synCcompl synCdif synCin synChncodecmpset synCcnv synCopab
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
    @gFrrd (.classMem A (synCvv)) q y u (synChwcn A)
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) dv_cache_0007
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

/-- Checked nominal proof certificate identified upstream as `g_hncodecmplnpwcndv`. -/
@[expose]
noncomputable def gHncodecmplnpwcndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synClnpwc (synChwcn A)))) :=
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
  have dv_cache_0001 : r ∉ ((synCop (synChncodecmpset A) (synChwcn A))).fv := by
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
    r ∉ ((Wff.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))).fv :=
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
      ((synWss (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
          (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
            (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))))).fv :=
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
  have dv_cache_0004 : r ∉ ((synChncodecmpset A)).fv :=
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
  have dv_cache_0005 : d ∉ ((synChncodecmpset A)).fv :=
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
  have dv_cache_0006 : r ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0007 : d ∉ ((synChwcn A)).fv :=
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
      ((synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (synCfound) (synChwcn A))).fv :=
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
      ((synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (synCfound) (synChwcn A))).fv :=
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
  have p0000 := @gHncodecmpsetrefndv A
  have p0001 := @gHncodecmpsettransndv A
  have p0002 :=
    @gJca (.classMem A (synCvv))
      (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)) p0000 p0001
  have p0003 := @gHncodecmpsetconnexndv A
  have p0004 :=
    @gJca (.classMem A (synCvv))
      (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
        (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
      (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synClntp))
  have p0006 :=
    @gBreqi (synChncodecmpset A) (synChwcn A) (synClntp)
      (synCin (synCin (synCref) (synCtrans)) (synCconnex)) p0005
  have p0007 :=
    @gBrin (synChncodecmpset A) (synChwcn A) (synCin (synCref) (synCtrans))
      (synCconnex)
  have p0008 := @gBrin (synChncodecmpset A) (synChwcn A) (synCref) (synCtrans)
  have p0009 :=
    @gAnbi1i
      (synWbr (synChncodecmpset A) (synCin (synCref) (synCtrans)) (synChwcn A))
      (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
        (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
      (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)) p0008
  have p0010 :=
    @gBitri
      (synWbr (synChncodecmpset A)
        (synCin (synCin (synCref) (synCtrans)) (synCconnex)) (synChwcn A))
      (synWa (synWbr (synChncodecmpset A) (synCin (synCref) (synCtrans)) (synChwcn A))
        (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)))
      (synWa (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
          (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
        (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)))
      p0007 p0009
  have p0011 :=
    @gBitri (synWbr (synChncodecmpset A) (synClntp) (synChwcn A))
      (synWbr (synChncodecmpset A)
        (synCin (synCin (synCref) (synCtrans)) (synCconnex)) (synChwcn A))
      (synWa (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
          (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
        (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)))
      p0006 p0010
  have p0012 :=
    @gA1i
      (synWb (synWbr (synChncodecmpset A) (synClntp) (synChwcn A)) (synWa
          (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
            (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
          (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A))))
      (.classMem A (synCvv)) p0011
  have p0013 :=
    @gMpbird (.classMem A (synCvv))
      (synWbr (synChncodecmpset A) (synClntp) (synChwcn A))
      (synWa (synWa (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
          (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)))
        (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)))
      p0004 p0012
  have p0014 :=
    (Nominal.biimpRefl (synWbr (synChncodecmpset A) (synClntp) (synChwcn A)))
  have p0015 :=
    @gBiimpi (synWbr (synChncodecmpset A) (synClntp) (synChwcn A))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntp)) p0014
  have p0016 :=
    @gSyl (.classMem A (synCvv))
      (synWbr (synChncodecmpset A) (synClntp) (synChwcn A))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntp)) p0013 p0015
  have p0017 := @gHncodecmpsetssxpndv A
  have p0018 :=
    @gA1i (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)))
      (.classMem A (synCvv)) p0017
  have p0019 := @gHncodecmpsetexg A
  have p0020 := @gHwcnexg A
  have p0021 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0019 p0020
  have p0022 := @gOpexg (synChncodecmpset A) (synChwcn A) (synCvv) (synCvv)
  have p0023 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecmpset A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCvv)) p0021 p0022
  have p0024 :=
    @gEleq1 (.cv r) (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels)
  have p0025 := @gFveq2 (.cv r) (synCop (synChncodecmpset A) (synChwcn A)) (synC1st)
  have p0026 := @gFveq2 (.cv r) (synCop (synChncodecmpset A) (synChwcn A)) (synC2nd)
  have p0028 :=
    @gXpeq12d (.classEq (.cv r) (synCop (synChncodecmpset A) (synChwcn A)))
      (synCfv (synC2nd) (.cv r))
      (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
      (synCfv (synC2nd) (.cv r))
      (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))) p0026 p0026
  have p0029 :=
    @gSseq12d (.classEq (.cv r) (synCop (synChncodecmpset A) (synChwcn A)))
      (synCfv (synC1st) (.cv r))
      (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
      (synCxp (synCfv (synC2nd) (.cv r)) (synCfv (synC2nd) (.cv r)))
      (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
        (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))))
      p0025 p0028
  have p0030 := @gElhwrrels r
  have p0031 :=
    @gVtoclbg (.classMem (.cv r) (synChwrels))
      (synWss (synCfv (synC1st) (.cv r))
        (synCxp (synCfv (synC2nd) (.cv r)) (synCfv (synC2nd) (.cv r))))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))
      (synWss (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
        (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
          (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))))
      r (synCop (synChncodecmpset A) (synChwcn A)) (synCvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0024 p0029 p0030
  have p0032 :=
    @gSyl (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCvv))
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))
        (synWss (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
          (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
            (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))))))
      p0023 p0031
  have p0036 := @gOpfvscl (synChncodecmpset A) (synChwcn A)
  have p0037 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecmpset A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (synWa (.classEq (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
          (synChncodecmpset A))
        (.classEq (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
          (synChwcn A)))
      p0021 p0036
  have p0038 :=
    @gSimpld (.classMem A (synCvv))
      (.classEq (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
        (synChncodecmpset A))
      (.classEq (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
        (synChwcn A))
      p0037
  have p0044 :=
    @gSimprd (.classMem A (synCvv))
      (.classEq (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
        (synChncodecmpset A))
      (.classEq (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
        (synChwcn A))
      p0037
  have p0051 :=
    @gXpeq12d (.classMem A (synCvv))
      (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))) (synChwcn A)
      (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))) (synChwcn A)
      p0044 p0044
  have p0052 :=
    @gSseq12d (.classMem A (synCvv))
      (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
      (synChncodecmpset A)
      (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
        (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A))))
      (synCxp (synChwcn A) (synChwcn A)) p0038 p0051
  have p0053 :=
    @gBitrd (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))
      (synWss (synCfv (synC1st) (synCop (synChncodecmpset A) (synChwcn A)))
        (synCxp (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))
          (synCfv (synC2nd) (synCop (synChncodecmpset A) (synChwcn A)))))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0032 p0052
  have p0054 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0018 p0053
  have p0055 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntp))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels)) p0016 p0054
  have p0056 :=
    @gElin (synCop (synChncodecmpset A) (synChwcn A)) (synClntp) (synChwrels)
  have p0057 :=
    @gA1i
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCin (synClntp) (synChwrels)))
        (synWa (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntp))
          (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels))))
      (.classMem A (synCvv)) p0056
  have p0058 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCin (synClntp) (synChwrels)))
      (synWa (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntp))
        (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synChwrels)))
      p0055 p0057
  have p0061 := @gSnidg (synChwcn A) (synCvv)
  have p0062 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synChwcn A) (synCsn (synChwcn A))) p0020 p0061
  have p0063 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (.classMem (synChwcn A) (synCsn (synChwcn A))) p0019 p0062
  have p0064 :=
    @gOpelxp (synChncodecmpset A) (synChwcn A) (synCvv) (synCsn (synChwcn A))
  have p0065 :=
    @gA1i
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCxp (synCvv) (synCsn (synChwcn A))))
        (synWa (.classMem (synChncodecmpset A) (synCvv))
          (.classMem (synChwcn A) (synCsn (synChwcn A)))))
      (.classMem A (synCvv)) p0064
  have p0066 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCxp (synCvv) (synCsn (synChwcn A))))
      (synWa (.classMem (synChncodecmpset A) (synCvv))
        (.classMem (synChwcn A) (synCsn (synChwcn A))))
      p0063 p0065
  have p0067 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCin (synClntp) (synChwrels)))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCxp (synCvv) (synCsn (synChwcn A))))
      p0058 p0066
  have p0068 :=
    @gElin (synCop (synChncodecmpset A) (synChwcn A))
      (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn (synChwcn A)))
  have p0069 :=
    @gA1i
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCin (synCin (synClntp) (synChwrels))
            (synCxp (synCvv) (synCsn (synChwcn A))))) (synWa
          (.classMem (synCop (synChncodecmpset A) (synChwcn A))
            (synCin (synClntp) (synChwrels)))
          (.classMem (synCop (synChncodecmpset A) (synChwcn A))
            (synCxp (synCvv) (synCsn (synChwcn A))))))
      (.classMem A (synCvv)) p0068
  have p0070 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCin (synCin (synClntp) (synChwrels))
          (synCxp (synCvv) (synCsn (synChwcn A)))))
      (synWa (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCin (synClntp) (synChwrels)))
        (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCxp (synCvv) (synCsn (synChwcn A)))))
      p0067 p0069
  have p0071 := (Nominal.classEqRefl (synClntpc (synChwcn A)))
  have p0072 :=
    @gA1i
      (.classEq (synClntpc (synChwcn A)) (synCin (synCin (synClntp) (synChwrels))
          (synCxp (synCvv) (synCsn (synChwcn A)))))
      (.classMem A (synCvv)) p0071
  have p0073 :=
    @gEleqtrrd (.classMem A (synCvv)) (synCop (synChncodecmpset A) (synChwcn A))
      (synCin (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn (synChwcn A))))
      (synClntpc (synChwcn A)) p0070 p0072
  have p0074 := @gHncodecmpstrictfrndv A
  have p0078 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv d) (synChwcn A))
  have p0080 :=
    @gCnveqd
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv d) (synChwcn A)))
      (.cv r) (synChncodecmpset A) p0078
  have p0081 :=
    @gDifeq12d
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv d) (synChwcn A)))
      (.cv r) (synChncodecmpset A) (synCcnv (.cv r)) (synCcnv (synChncodecmpset A))
      p0078 p0080
  have p0082 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv d) (synChwcn A))
  have p0083 :=
    @gBreq12d
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv d) (synChwcn A)))
      (synCdif (.cv r) (synCcnv (.cv r)))
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv d)
      (synChwcn A) (synCfound) p0081 p0082
  have p0084 :=
    @gOpelopabga (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      r d (synChncodecmpset A) (synChwcn A) (synCvv) (synCvv) dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0083
  have p0085 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecmpset A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
        (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (synCfound) (synChwcn A)))
      p0021 p0084
  have p0086 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCopab r d
          (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      p0074 p0085
  have p0087 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntpc (synChwcn A)))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCopab r d
          (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
      p0073 p0086
  have p0088 :=
    @gElin (synCop (synChncodecmpset A) (synChwcn A)) (synClntpc (synChwcn A))
      (synCopab r d (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))
  have p0089 :=
    @gA1i
      (synWb (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCin (synClntpc (synChwcn A)) (synCopab r d
              (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))) (synWa
          (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synClntpc (synChwcn A)))
          (.classMem (synCop (synChncodecmpset A) (synChwcn A)) (synCopab r d
              (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))))
      (.classMem A (synCvv)) p0088
  have p0090 :=
    @gMpbird (.classMem A (synCvv))
      (.classMem (synCop (synChncodecmpset A) (synChwcn A))
        (synCin (synClntpc (synChwcn A)) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))))
      (synWa (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synClntpc (synChwcn A))) (.classMem (synCop (synChncodecmpset A) (synChwcn A))
          (synCopab r d (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))))
      p0087 p0089
  have p0091 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLnpwc (synChwcn A)
      r d dv_cache_0007 dv_cache_0006 dv_cache_0011
  have p0092 :=
    @gA1i
      (.classEq (synClnpwc (synChwcn A)) (synCin (synClntpc (synChwcn A)) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))))
      (.classMem A (synCvv)) p0091
  have p0093 :=
    @gEleqtrrd (.classMem A (synCvv)) (synCop (synChncodecmpset A) (synChwcn A))
      (synCin (synClntpc (synChwcn A)) (synCopab r d
          (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
      (synClnpwc (synChwcn A)) p0090 p0092
  exact p0093

/-- Checked nominal proof certificate identified upstream as `g_hnordlnquoeqimndv`. -/
@[expose]
noncomputable def gHnordlnquoeqimndv (A : Class) (r : Var) (_dv_A_r : r ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq (synClnker (.cv r)) (synChwniso A))
        (.classEq (synClnquo (.cv r) (synChwcn A)) (synChnord A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnquo (.cv r) (synChwcn A)))
  have p0001 :=
    @gA1i
      (.classEq (synClnquo (.cv r) (synChwcn A)) (synCqs (synChwcn A) (synClnker (.cv r))))
      (.classEq (synClnker (.cv r)) (synChwniso A)) p0000
  have p0002 := @gQseq2 (synClnker (.cv r)) (synChwniso A) (synChwcn A)
  have p0003 := (Nominal.classEqRefl (synChnord A))
  have p0004 := @gEqcomi (synChnord A) (synCqs (synChwcn A) (synChwniso A)) p0003
  have p0005 :=
    @gA1i (.classEq (synCqs (synChwcn A) (synChwniso A)) (synChnord A))
      (.classEq (synClnker (.cv r)) (synChwniso A)) p0004
  have p0006 :=
    @gN3eqtrd (.classEq (synClnker (.cv r)) (synChwniso A))
      (synClnquo (.cv r) (synChwcn A)) (synCqs (synChwcn A) (synClnker (.cv r)))
      (synCqs (synChwcn A) (synChwniso A)) (synChnord A) p0001 p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hnordwendv`. -/
@[expose]
noncomputable def gHnordwendv (A : Class) (s : Var) (dv_A_s : s ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (synWex s (synWbr (.cv s) (synCwe) (synChnord A)))) :=
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
  have dv_cache_0001 : r ∉ ((synChncodecmpset A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((synChwcn A)).fv ((Class.cv r)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synChwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((synClnqord (.cv r) (synChwcn A))).fv :=
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
    s ∉ ((synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A))).fv :=
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
    s ∉ ((synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))).fv :=
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
  have dv_cache_0006 : r ∉ ((synWex s (synWbr (.cv s) (synCwe) (synChnord A)))).fv :=
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
  have dv_cache_0007 : r ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have p0000 := @gHncodecmpsetexg A
  have p0001 := @gIsset r (synChncodecmpset A) dv_cache_0001
  have p0002 :=
    @gA1i
      (synWb (.classMem (synChncodecmpset A) (synCvv))
        (synWex r (.classEq (.cv r) (synChncodecmpset A))))
      (.classMem A (synCvv)) p0001
  have p0003 :=
    @gBiimpd (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (synWex r (.classEq (.cv r) (synChncodecmpset A))) p0002
  have p0004 :=
    @gMpd (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))
      (synWex r (.classEq (.cv r) (synChncodecmpset A))) p0000 p0003
  have p0005 := @gSimpl (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))
  have p0007 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0005 p0000
  have p0008 := @gSimpr (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))
  have p0009 :=
    @gEleq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCvv) p0008
  have p0010 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0007
      p0009
  have p0012 := @gHwcnexg A
  have p0013 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv)) p0005 p0012
  have p0014 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)) p0010 p0013
  have p0016 := @gHncodecmpsetrefndv A
  have p0017 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0005 p0016
  have p0019 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCref) p0008
  have p0020 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCref) (synChwcn A)) p0017 p0019
  have p0022 := @gHncodecmpsettransndv A
  have p0023 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A))
      p0005 p0022
  have p0025 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCtrans) p0008
  have p0026 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCtrans) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)) p0023 p0025
  have p0027 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (.cv r) (synCtrans) (synChwcn A)) p0020 p0026
  have p0029 := @gHncodecmpsetconnexndv A
  have p0030 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A))
      p0005 p0029
  have p0032 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCconnex) p0008
  have p0033 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCconnex) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)) p0030 p0032
  have p0034 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWbr (.cv r) (synCref) (synChwcn A))
        (synWbr (.cv r) (synCtrans) (synChwcn A)))
      (synWbr (.cv r) (synCconnex) (synChwcn A)) p0027 p0033
  have p0035 := @gHncodecmpsetssxpndv A
  have p0036 :=
    @gA1i (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))) p0035
  have p0038 :=
    @gSseq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)) p0008
  have p0039 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0036 p0038
  have p0040 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
          (synWbr (.cv r) (synCtrans) (synChwcn A)))
        (synWbr (.cv r) (synCconnex) (synChwcn A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))) p0034 p0039
  have p0041 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
            (synWbr (.cv r) (synCtrans) (synChwcn A)))
          (synWbr (.cv r) (synCconnex) (synChwcn A)))
        (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
      p0014 p0040
  have p0043 := @gHncodecmpstrictfrndv A
  have p0044 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      p0005 p0043
  have p0047 :=
    @gCnveqd (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) p0008
  have p0048 :=
    @gDifeq12d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCcnv (.cv r)) (synCcnv (synChncodecmpset A))
      p0008 p0047
  have p0049 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synCdif (.cv r) (synCcnv (.cv r)))
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (synChwcn A)
      (synCfound) p0048
  have p0050 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      p0044 p0049
  have p0051 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv))) (synWa
          (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
              (synWbr (.cv r) (synCtrans) (synChwcn A)))
            (synWbr (.cv r) (synCconnex) (synChwcn A)))
          (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
      (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A)) p0041
      p0050
  have p0052 := @gLnqordwe (synChwcn A) (.cv r) dv_cache_0002
  have p0053 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
          (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
                (synWbr (.cv r) (synCtrans) (synChwcn A)))
              (synWbr (.cv r) (synCconnex) (synChwcn A)))
            (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
        (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synClnquo (.cv r) (synChwcn A)))
      p0051 p0052
  have p0055 := @gLnkereq (.cv r) (synChncodecmpset A)
  have p0056 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (synClnker (.cv r)) (synClnker (synChncodecmpset A))) p0008 p0055
  have p0058 := @gHncodecmplnkerndv A
  have p0059 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv))
      (.classEq (synClnker (synChncodecmpset A)) (synChwniso A)) p0005 p0058
  have p0060 :=
    @gEqtrd (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synClnker (.cv r)) (synClnker (synChncodecmpset A)) (synChwniso A) p0056 p0059
  have p0061 := (Nominal.classEqRefl (synClnquo (.cv r) (synChwcn A)))
  have p0062 :=
    @gA1i
      (.classEq (synClnquo (.cv r) (synChwcn A)) (synCqs (synChwcn A) (synClnker (.cv r))))
      (.classEq (synClnker (.cv r)) (synChwniso A)) p0061
  have p0063 := @gQseq2 (synClnker (.cv r)) (synChwniso A) (synChwcn A)
  have p0064 := (Nominal.classEqRefl (synChnord A))
  have p0065 := @gEqcomi (synChnord A) (synCqs (synChwcn A) (synChwniso A)) p0064
  have p0066 :=
    @gA1i (.classEq (synCqs (synChwcn A) (synChwniso A)) (synChnord A))
      (.classEq (synClnker (.cv r)) (synChwniso A)) p0065
  have p0067 :=
    @gN3eqtrd (.classEq (synClnker (.cv r)) (synChwniso A))
      (synClnquo (.cv r) (synChwcn A)) (synCqs (synChwcn A) (synClnker (.cv r)))
      (synCqs (synChwcn A) (synChwniso A)) (synChnord A) p0062 p0063 p0066
  have p0068 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synClnquo (.cv r) (synChwcn A)) (synChnord A)) p0060 p0067
  have p0069 :=
    @gBreq2d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synClnquo (.cv r) (synChwcn A)) (synChnord A)
      (synClnqord (.cv r) (synChwcn A)) (synCwe) p0068
  have p0070 :=
    @gMpbid (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synClnquo (.cv r) (synChwcn A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) p0053 p0069
  have p0081 := @gLnqordexg (synChwcn A) (.cv r) dv_cache_0002
  have p0082 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv)) p0014 p0081
  have p0083 :=
    @gSimpr (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
  have p0084 :=
    @gBreq1d
      (synWa (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
      (.cv s) (synClnqord (.cv r) (synChwcn A)) (synChnord A) (synCwe) p0083
  have p0085 :=
    @gBiimprd
      (synWa (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
      (synWbr (.cv s) (synCwe) (synChnord A))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) p0084
  have p0086 :=
    @gSpcimedv (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv s) (synCwe) (synChnord A))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) s
      (synClnqord (.cv r) (synChwcn A)) (synCvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0082 p0085
  have p0087 :=
    @gMpd (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A))
      (synWex s (synWbr (.cv s) (synCwe) (synChnord A))) p0070 p0086
  have p0088 :=
    @gExlimddv (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))
      (synWex s (synWbr (.cv s) (synCwe) (synChnord A))) r dv_cache_0006 dv_cache_0007
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

/-- Checked nominal proof certificate identified upstream as `g_hncardhwcardsndv`. -/
@[expose]
noncomputable def gHncardhwcardsndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (.classMem (synChncard A) (synChwcards (synCvv)))) :=
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
  have dv_cache_0002 : d ∉ ((synChnord A)).fv :=
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
  have dv_cache_0003 : t ∉ ((synChnord A)).fv :=
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
      ((synWa (synWbr (.cv s) (synCwe) (synChnord A))
          (.classEq (synChncard A) (synCnc (synChnord A))))).fv :=
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
      ((synWa (synWbr (.cv s) (synCwe) (synChnord A))
          (.classEq (synChncard A) (synCnc (synChnord A))))).fv :=
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
      ((synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
              (.classEq (synChncard A) (synCnc (.cv d))))))).fv :=
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
  have dv_cache_0010 : t ∉ ((Wff.classEq (.cv k) (synChncard A))).fv :=
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
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (synChncard A))).fv :=
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
  have dv_cache_0014 : k ∉ ((synChncard A)).fv :=
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
      ((synWb (.classMem (synChncard A) (synChwcards (synCvv))) (synWex d (synWex t
              (synWa (synWbr (.cv t) (synCwe) (.cv d))
                (.classEq (synChncard A) (synCnc (.cv d)))))))).fv :=
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
  have p0000 := @gHnordwendv A s dv_cache_0001
  have p0001 := @gId (synWbr (.cv s) (synCwe) (synChnord A))
  have p0002 := (Nominal.classEqRefl (synChncard A))
  have p0003 :=
    @gA1i (.classEq (synChncard A) (synCnc (synChnord A)))
      (synWbr (.cv s) (synCwe) (synChnord A)) p0002
  have p0004 :=
    @gJca (synWbr (.cv s) (synCwe) (synChnord A))
      (synWbr (.cv s) (synCwe) (synChnord A))
      (.classEq (synChncard A) (synCnc (synChnord A))) p0001 p0003
  have p0005 := @gBrex (.cv s) (synChnord A) (synCwe)
  have p0006 :=
    @gAncom (.classMem (synChnord A) (synCvv)) (.classMem (.cv s) (synCvv))
  have p0007 :=
    @gSylibr (synWbr (.cv s) (synCwe) (synChnord A))
      (synWa (.classMem (.cv s) (synCvv)) (.classMem (synChnord A) (synCvv)))
      (synWa (.classMem (synChnord A) (synCvv)) (.classMem (.cv s) (synCvv))) p0005
      p0006
  have p0008 := @gSimpr (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s))
  have p0009 := @gSimpl (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s))
  have p0010 :=
    @gBreq12d (synWa (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s)))
      (.cv t) (.cv s) (.cv d) (synChnord A) (synCwe) p0008 p0009
  have p0012 :=
    @gNceqd (synWa (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s))) (.cv d)
      (synChnord A) p0009
  have p0013 :=
    @gEqeq2d (synWa (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s)))
      (synCnc (.cv d)) (synCnc (synChnord A)) (synChncard A) p0012
  have p0014 :=
    @gAnbi12d (synWa (.classEq (.cv d) (synChnord A)) (.classEq (.cv t) (.cv s)))
      (synWbr (.cv t) (synCwe) (.cv d)) (synWbr (.cv s) (synCwe) (synChnord A))
      (.classEq (synChncard A) (synCnc (.cv d)))
      (.classEq (synChncard A) (synCnc (synChnord A))) p0010 p0013
  have p0015 :=
    @gSpc2egv
      (synWa (synWbr (.cv t) (synCwe) (.cv d)) (.classEq (synChncard A) (synCnc (.cv d))))
      (synWa (synWbr (.cv s) (synCwe) (synChnord A))
        (.classEq (synChncard A) (synCnc (synChnord A))))
      d t (synChnord A) (.cv s) (synCvv) (synCvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @gSyl (synWbr (.cv s) (synCwe) (synChnord A))
      (synWa (.classMem (synChnord A) (synCvv)) (.classMem (.cv s) (synCvv)))
      (.imp (synWa (synWbr (.cv s) (synCwe) (synChnord A))
          (.classEq (synChncard A) (synCnc (synChnord A)))) (synWex d (synWex t
            (synWa (synWbr (.cv t) (synCwe) (.cv d))
              (.classEq (synChncard A) (synCnc (.cv d)))))))
      p0007 p0015
  have p0017 :=
    @gMpd (synWbr (.cv s) (synCwe) (synChnord A))
      (synWa (synWbr (.cv s) (synCwe) (synChnord A))
        (.classEq (synChncard A) (synCnc (synChnord A))))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (synChncard A) (synCnc (.cv d))))))
      p0004 p0016
  have p0018 :=
    @gExlimiv (synWbr (.cv s) (synCwe) (synChnord A))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (synChncard A) (synCnc (.cv d))))))
      s dv_cache_0009 p0017
  have p0019 := @gHncardex A
  have p0020 := @gId (.classEq (.cv k) (synChncard A))
  have p0021 :=
    @gEleq1d (.classEq (.cv k) (synChncard A)) (.cv k) (synChncard A)
      (synChwcards (synCvv)) p0020
  have p0023 :=
    @gEqeq1d (.classEq (.cv k) (synChncard A)) (.cv k) (synChncard A) (synCnc (.cv d))
      p0020
  have p0024 :=
    @gAnbi2d (.classEq (.cv k) (synChncard A)) (.classEq (.cv k) (synCnc (.cv d)))
      (.classEq (synChncard A) (synCnc (.cv d))) (synWbr (.cv t) (synCwe) (.cv d))
      p0023
  have p0025 :=
    @gExbidv (.classEq (.cv k) (synChncard A))
      (synWa (synWbr (.cv t) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWa (synWbr (.cv t) (synCwe) (.cv d)) (.classEq (synChncard A) (synCnc (.cv d))))
      t dv_cache_0010 p0024
  have p0026 :=
    @gExbidv (.classEq (.cv k) (synChncard A))
      (synWex t
        (synWa (synWbr (.cv t) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))))
      (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
          (.classEq (synChncard A) (synCnc (.cv d)))))
      d dv_cache_0011 p0025
  have p0027 :=
    @gBibi12d (.classEq (.cv k) (synChncard A))
      (.classMem (.cv k) (synChwcards (synCvv)))
      (.classMem (synChncard A) (synChwcards (synCvv)))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (synChncard A) (synCnc (.cv d))))))
      p0021 p0026
  have p0028 := @gElhwcardswev k t d dv_cache_0012 dv_cache_0008 dv_cache_0013
  have p0029 :=
    @gVtoclg
      (synWb (.classMem (.cv k) (synChwcards (synCvv))) (synWex d (synWex t
            (synWa (synWbr (.cv t) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))))))
      (synWb (.classMem (synChncard A) (synChwcards (synCvv))) (synWex d (synWex t
            (synWa (synWbr (.cv t) (synCwe) (.cv d))
              (.classEq (synChncard A) (synCnc (.cv d)))))))
      k (synChncard A) (synCvv) dv_cache_0014 dv_cache_0015 p0027 p0028
  have p0030 := Nominal.mp p0019 p0029
  have p0031 :=
    @gBiimpri (.classMem (synChncard A) (synChwcards (synCvv)))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (synChncard A) (synCnc (.cv d))))))
      p0030
  have p0032 :=
    @gSyl (synWex s (synWbr (.cv s) (synCwe) (synChnord A)))
      (synWex d (synWex t (synWa (synWbr (.cv t) (synCwe) (.cv d))
            (.classEq (synChncard A) (synCnc (.cv d))))))
      (.classMem (synChncard A) (synChwcards (synCvv))) p0018 p0031
  have p0033 :=
    @gSyl (.classMem A (synCvv)) (synWex s (synWbr (.cv s) (synCwe) (synChnord A)))
      (.classMem (synChncard A) (synChwcards (synCvv))) p0000 p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6canonicaltchomndv`. -/
@[expose]
noncomputable def gWppconcrete6canonicaltchomndv (X : Class)
    (hyp_wppconcrete6canonicaltchomndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCfv (synCwppconcrete6fn)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
        (synCfv (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))) :=
  by
  have p0000 := @gWppconcrete6fnvalndv X hyp_wppconcrete6canonicaltchomndv_1
  have p0001 :=
    @gTceq
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synChncard (synChnord (synCpw (synCpw X))))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0004 := @gPwex (synCpw X) p0003
  have p0005 := @gHnordexg (synCpw (synCpw X))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gHncardtcshiftndv (synChnord (synCpw (synCpw X))) p0006
  have p0008 :=
    @gEqtri
      (synCtc (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synCtc (synChncard (synChnord (synCpw (synCpw X)))))
      (synChncard (synCpw1 (synChnord (synCpw (synCpw X))))) p0002 p0007
  have p0013 := @gPw1ex (synChnord (synCpw (synCpw X))) p0006
  have p0014 := @gPw1ex X hyp_wppconcrete6canonicaltchomndv_1
  have p0015 := @gPwex (synCpw1 X) p0014
  have p0016 := @gPwex (synCpw (synCpw1 X)) p0015
  have p0017 := @gHnordexg (synCpw (synCpw (synCpw1 X)))
  have p0018 := Nominal.mp p0016 p0017
  have p0021 := @gHnordpw1shiftenndv (synCpw (synCpw X)) p0004
  have p0027 :=
    @gEqnc (synCpw1 (synChnord (synCpw (synCpw X))))
      (synChnord (synCpw1 (synCpw (synCpw X)))) p0013
  have p0028 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synChnord (synCpw (synCpw X)))))
        (synCnc (synChnord (synCpw1 (synCpw (synCpw X))))))
      (synWbr (synCpw1 (synChnord (synCpw (synCpw X)))) (synCen)
        (synChnord (synCpw1 (synCpw (synCpw X)))))
      p0021 p0027
  have p0029 := (Nominal.classEqRefl (synChncard (synCpw1 (synCpw (synCpw X)))))
  have p0030 :=
    @gEqcomi (synChncard (synCpw1 (synCpw (synCpw X))))
      (synCnc (synChnord (synCpw1 (synCpw (synCpw X))))) p0029
  have p0033 := @gPw1ex (synCpw (synCpw X)) p0004
  have p0037 := @gNcpw1pw2 X hyp_wppconcrete6canonicaltchomndv_1
  have p0038 :=
    @gHncardnceqndv (synCpw1 (synCpw (synCpw X))) (synCpw (synCpw (synCpw1 X)))
      p0033 p0016 p0037
  have p0039 := (Nominal.classEqRefl (synChncard (synCpw (synCpw (synCpw1 X)))))
  have p0040 :=
    @gEqtri (synChncard (synCpw1 (synCpw (synCpw X))))
      (synChncard (synCpw (synCpw (synCpw1 X))))
      (synCnc (synChnord (synCpw (synCpw (synCpw1 X))))) p0038 p0039
  have p0041 :=
    @gEqtri (synCnc (synChnord (synCpw1 (synCpw (synCpw X)))))
      (synChncard (synCpw1 (synCpw (synCpw X))))
      (synCnc (synChnord (synCpw (synCpw (synCpw1 X))))) p0030 p0040
  have p0042 :=
    @gEqtri (synCnc (synCpw1 (synChnord (synCpw (synCpw X)))))
      (synCnc (synChnord (synCpw1 (synCpw (synCpw X)))))
      (synCnc (synChnord (synCpw (synCpw (synCpw1 X))))) p0028 p0041
  have p0043 :=
    @gHncardnceqndv (synCpw1 (synChnord (synCpw (synCpw X))))
      (synChnord (synCpw (synCpw (synCpw1 X)))) p0013 p0018 p0042
  have p0044 :=
    @gEqtri
      (synCtc (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synChncard (synCpw1 (synChnord (synCpw (synCpw X)))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 X))))) p0008 p0043
  have p0045 := @gTcnc X hyp_wppconcrete6canonicaltchomndv_1
  have p0046 := @gEqcomi (synCtc (synCnc X)) (synCnc (synCpw1 X)) p0045
  have p0047 := @gTceq (synCnc (synCpw1 X)) (synCtc (synCnc X))
  have p0048 := Nominal.mp p0046 p0047
  have p0049 := @gTceq (synCtc (synCnc (synCpw1 X))) (synCtc (synCtc (synCnc X)))
  have p0050 := Nominal.mp p0048 p0049
  have p0051 :=
    @gTceq (synCtc (synCtc (synCnc (synCpw1 X))))
      (synCtc (synCtc (synCtc (synCnc X))))
  have p0052 := Nominal.mp p0050 p0051
  have p0053 :=
    @gTceq (synCtc (synCtc (synCtc (synCnc (synCpw1 X)))))
      (synCtc (synCtc (synCtc (synCtc (synCnc X)))))
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 X))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))
  have p0056 := Nominal.mp p0054 p0055
  have p0057 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 X)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @gFveq2i
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 X))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synCwppconcrete6fn) p0058
  have p0060 :=
    @gEqcomi
      (synCfv (synCwppconcrete6fn) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 X)))))))))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      p0059
  have p0062 := @gWppconcrete6fnvalndv (synCpw1 X) p0014
  have p0063 :=
    @gEqtri
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synCfv (synCwppconcrete6fn) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 X)))))))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 X))))) p0060 p0062
  have p0064 :=
    @gEqcomi
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 X))))) p0063
  have p0065 :=
    @gEqtri
      (synCtc (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 X)))))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      p0044 p0064
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_hncardtc6oneeqndv`. -/
@[expose]
noncomputable def gHncardtc6oneeqndv :
    Nominal.NPrf
      (.classEq (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gHncardtcshiftndv (synC1c) p0000
  have p0002 :=
    @gTceq (synCtc (synChncard (synC1c))) (synChncard (synCpw1 (synC1c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @gPw1ex (synC1c) p0000
  have p0006 := @gHncardtcshiftndv (synCpw1 (synC1c)) p0005
  have p0007 :=
    @gEqtri (synCtc (synCtc (synChncard (synC1c))))
      (synCtc (synChncard (synCpw1 (synC1c))))
      (synChncard (synCpw1 (synCpw1 (synC1c)))) p0003 p0006
  have p0008 :=
    @gTceq (synCtc (synCtc (synChncard (synC1c))))
      (synChncard (synCpw1 (synCpw1 (synC1c))))
  have p0009 := Nominal.mp p0007 p0008
  have p0012 := @gPw1ex (synCpw1 (synC1c)) p0005
  have p0013 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synC1c))) p0012
  have p0014 :=
    @gEqtri (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synC1c)))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0009 p0013
  have p0015 :=
    @gTceq (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0020 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0012
  have p0021 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0020
  have p0022 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0016 p0021
  have p0023 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  have p0024 := Nominal.mp p0022 p0023
  have p0029 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0020
  have p0030 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0029
  have p0031 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0024
      p0030
  have p0032 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0033 := Nominal.mp p0031 p0032
  have p0039 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0029
  have p0040 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0039
  have p0041 :=
    @gEqtri
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0033 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_hncardtc7oneeqndv`. -/
@[expose]
noncomputable def gHncardtc7oneeqndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synChncard (synCpw1 (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gHncardtcshiftndv (synC1c) p0000
  have p0002 :=
    @gTceq (synCtc (synChncard (synC1c))) (synChncard (synCpw1 (synC1c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @gPw1ex (synC1c) p0000
  have p0006 := @gHncardtcshiftndv (synCpw1 (synC1c)) p0005
  have p0007 :=
    @gEqtri (synCtc (synCtc (synChncard (synC1c))))
      (synCtc (synChncard (synCpw1 (synC1c))))
      (synChncard (synCpw1 (synCpw1 (synC1c)))) p0003 p0006
  have p0008 :=
    @gTceq (synCtc (synCtc (synChncard (synC1c))))
      (synChncard (synCpw1 (synCpw1 (synC1c))))
  have p0009 := Nominal.mp p0007 p0008
  have p0012 := @gPw1ex (synCpw1 (synC1c)) p0005
  have p0013 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synC1c))) p0012
  have p0014 :=
    @gEqtri (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synC1c)))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0009 p0013
  have p0015 :=
    @gTceq (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0020 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0012
  have p0021 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0020
  have p0022 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0016 p0021
  have p0023 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  have p0024 := Nominal.mp p0022 p0023
  have p0029 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0020
  have p0030 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0029
  have p0031 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0024
      p0030
  have p0032 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0033 := Nominal.mp p0031 p0032
  have p0039 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0029
  have p0040 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0039
  have p0041 :=
    @gEqtri
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0033 p0040
  have p0042 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  have p0043 := Nominal.mp p0041 p0042
  have p0050 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0039
  have p0051 :=
    @gHncardtcshiftndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0050
  have p0052 :=
    @gEqtri
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synCtc (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0043 p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6thresholdtclecndv`. -/
@[expose]
noncomputable def gWppconcrete6thresholdtclecndv :
    Nominal.NPrf
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) :=
  by
  have p0000 := @gPw1ss1c (synC1c)
  have p0001 := @gPw1ss (synCpw1 (synC1c)) (synC1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPw1ss (synCpw1 (synCpw1 (synC1c))) (synCpw1 (synC1c))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (synCpw1 (synCpw1 (synC1c)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gN1cex
  have p0014 := @gPw1ex (synC1c) p0013
  have p0015 := @gPw1ex (synCpw1 (synC1c)) p0014
  have p0016 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0015
  have p0017 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0016
  have p0018 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0017
  have p0019 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0018
  have p0020 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0019
  have p0028 :=
    @gHncardmono
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0012 p0020 p0019
  have p0029 := @gHncardtc7oneeqndv
  have p0030 := @gHncardtc6oneeqndv
  have p0031 :=
    @gBreq12i
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synClec) p0029 p0030
  have p0032 :=
    @gMpbir
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synClec) (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0028 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_hnwpw1argclcndv`. -/
@[expose]
noncomputable def gHnwpw1argclcndv (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (.classMem C (synCpw1 D))
        (synWa (.classMem (synCuni C) D) (.classEq C (synCsn (synCuni C))))) :=
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
  have dv_cache_0002 : q ∉ ((synCpw1 D)).fv :=
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
    q ∉ ((synWa (.classMem (synCuni C) D) (.classEq C (synCsn (synCuni C))))).fv :=
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
  have p0000 := @gUnieq (.cv q) C
  have p0001 := @gEleq1d (.classEq (.cv q) C) (synCuni (.cv q)) (synCuni C) D p0000
  have p0002 := @gId (.classEq (.cv q) C)
  have p0004 := @gSneqd (.classEq (.cv q) C) (synCuni (.cv q)) (synCuni C) p0000
  have p0005 :=
    @gEqeq12d (.classEq (.cv q) C) (.cv q) C (synCsn (synCuni (.cv q)))
      (synCsn (synCuni C)) p0002 p0004
  have p0006 :=
    @gAnbi12d (.classEq (.cv q) C) (.classMem (synCuni (.cv q)) D)
      (.classMem (synCuni C) D) (.classEq (.cv q) (synCsn (synCuni (.cv q))))
      (.classEq C (synCsn (synCuni C))) p0001 p0005
  have p0007 := @gHnwpw1argcl D q
  have p0008 :=
    @gVtoclga
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (synWa (.classMem (synCuni C) D) (.classEq C (synCsn (synCuni C)))) q C
      (synCpw1 D) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wppsifnndv`. -/
@[expose]
noncomputable def gWppsifnndv (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfn F A) (synWfn (synCsi F) (synCpw1 A))) :=
  by
  have p0000 := @gFnfun A F
  have p0001 := @gFunsi F
  have p0002 := @gSyl (synWfn F A) (synWfun F) (synWfun (synCsi F)) p0000 p0001
  have p0003 := @gDmsi F
  have p0004 :=
    @gA1i (.classEq (synCdm (synCsi F)) (synCpw1 (synCdm F))) (synWfn F A) p0003
  have p0005 := @gFndm A F
  have p0006 := @gPw1eq (synCdm F) A
  have p0007 :=
    @gSyl (synWfn F A) (.classEq (synCdm F) A)
      (.classEq (synCpw1 (synCdm F)) (synCpw1 A)) p0005 p0006
  have p0008 :=
    @gEqtrd (synWfn F A) (synCdm (synCsi F)) (synCpw1 (synCdm F)) (synCpw1 A) p0004
      p0007
  have p0009 :=
    @gJca (synWfn F A) (synWfun (synCsi F))
      (.classEq (synCdm (synCsi F)) (synCpw1 A)) p0002 p0008
  have p0010 := (Nominal.biimpRefl (synWfn (synCsi F) (synCpw1 A)))
  have p0011 :=
    @gSylibr (synWfn F A)
      (synWa (synWfun (synCsi F)) (.classEq (synCdm (synCsi F)) (synCpw1 A)))
      (synWfn (synCsi F) (synCpw1 A)) p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wpptxpfnvalndv`. -/
@[expose]
noncomputable def gWpptxpfnvalndv (x : Var) (A : Class) (F : Class) (G : Class)
    (_dv_A_x : x ∉ A.fv) (_dv_F_x : x ∉ F.fv) (_dv_G_x : x ∉ G.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
        (.classEq (synCfv (synCtxp F G) (.cv x))
          (synCop (synCfv F (.cv x)) (synCfv G (.cv x))))) :=
  by
  have p0000 := @gEqid (synCfv F (.cv x))
  have p0001 :=
    @gA1i (.classEq (synCfv F (.cv x)) (synCfv F (.cv x)))
      (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A)) p0000
  have p0002 := @gSimpl (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A)
  have p0003 := @gSimpl (synWfn F A) (synWfn G A)
  have p0004 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn F A) (synWfn G A)) (synWfn F A) p0002 p0003
  have p0005 := @gSimpr (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A)
  have p0006 :=
    @gJca (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWfn F A) (.classMem (.cv x) A) p0004 p0005
  have p0007 := @gFnbrfvb A (.cv x) (synCfv F (.cv x)) F
  have p0008 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn F A) (.classMem (.cv x) A))
      (synWb (.classEq (synCfv F (.cv x)) (synCfv F (.cv x)))
        (synWbr (.cv x) F (synCfv F (.cv x))))
      p0006 p0007
  have p0009 :=
    @gMpbid (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (.classEq (synCfv F (.cv x)) (synCfv F (.cv x)))
      (synWbr (.cv x) F (synCfv F (.cv x))) p0001 p0008
  have p0010 := @gEqid (synCfv G (.cv x))
  have p0011 :=
    @gA1i (.classEq (synCfv G (.cv x)) (synCfv G (.cv x)))
      (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A)) p0010
  have p0013 := @gSimpr (synWfn F A) (synWfn G A)
  have p0014 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn F A) (synWfn G A)) (synWfn G A) p0002 p0013
  have p0016 :=
    @gJca (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWfn G A) (.classMem (.cv x) A) p0014 p0005
  have p0017 := @gFnbrfvb A (.cv x) (synCfv G (.cv x)) G
  have p0018 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn G A) (.classMem (.cv x) A))
      (synWb (.classEq (synCfv G (.cv x)) (synCfv G (.cv x)))
        (synWbr (.cv x) G (synCfv G (.cv x))))
      p0016 p0017
  have p0019 :=
    @gMpbid (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (.classEq (synCfv G (.cv x)) (synCfv G (.cv x)))
      (synWbr (.cv x) G (synCfv G (.cv x))) p0011 p0018
  have p0020 :=
    @gJca (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWbr (.cv x) F (synCfv F (.cv x))) (synWbr (.cv x) G (synCfv G (.cv x)))
      p0009 p0019
  have p0021 := @gTrtxp (.cv x) (synCfv F (.cv x)) (synCfv G (.cv x)) F G
  have p0022 :=
    @gSylibr (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWbr (.cv x) F (synCfv F (.cv x))) (synWbr (.cv x) G (synCfv G (.cv x))))
      (synWbr (.cv x) (synCtxp F G) (synCop (synCfv F (.cv x)) (synCfv G (.cv x))))
      p0020 p0021
  have p0024 := @gFntxp A A F G
  have p0025 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn F A) (synWfn G A)) (synWfn (synCtxp F G) (synCin A A)) p0002
      p0024
  have p0026 := @gInidm A
  have p0027 := @gFneq2i (synCin A A) A (synCtxp F G) p0026
  have p0028 :=
    @gSylib (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWfn (synCtxp F G) (synCin A A)) (synWfn (synCtxp F G) A) p0025 p0027
  have p0030 :=
    @gJca (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWfn (synCtxp F G) A) (.classMem (.cv x) A) p0028 p0005
  have p0031 :=
    @gFnbrfvb A (.cv x) (synCop (synCfv F (.cv x)) (synCfv G (.cv x))) (synCtxp F G)
  have p0032 :=
    @gSyl (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWa (synWfn (synCtxp F G) A) (.classMem (.cv x) A))
      (synWb (.classEq (synCfv (synCtxp F G) (.cv x))
          (synCop (synCfv F (.cv x)) (synCfv G (.cv x)))) (synWbr (.cv x) (synCtxp F G)
          (synCop (synCfv F (.cv x)) (synCfv G (.cv x)))))
      p0030 p0031
  have p0033 :=
    @gMpbird (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (.classEq (synCfv (synCtxp F G) (.cv x))
        (synCop (synCfv F (.cv x)) (synCfv G (.cv x))))
      (synWbr (.cv x) (synCtxp F G) (synCop (synCfv F (.cv x)) (synCfv G (.cv x))))
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

/-- Checked nominal proof certificate identified upstream as `g_pw1xpshiftsetndv`. -/
@[expose]
noncomputable def gPw1xpshiftsetndv (A : Class) (B : Class) (p : Var) (dv_A_p : p ∉ A.fv)
    (dv_B_p : p ∉ B.fv) (hyp_pw1xpshiftsetndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_pw1xpshiftsetndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classMem (synCmpt p (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))) (synCvv)) :=
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
  have dv_cache_0001 : p ∉ ((synCpw1 (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((synCsi (synC1st))).fv :=
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
  have dv_cache_0003 : p ∉ ((synCsi (synC2nd))).fv :=
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
  have dv_cache_0004 : p ∉ ((synCpw1 (synCxp A B))).fv :=
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
  have dv_cache_0005 : q ∉ ((synCpw1 (synCxp A B))).fv :=
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
      ((synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))).fv :=
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
      ((synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))).fv :=
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
      ((synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
          (synCpw1 (synCxp A B)))).fv :=
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
      ((synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))).fv :=
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
  have p0000 := @gId (.classMem (.cv p) (synCpw1 (synCxp A B)))
  have p0001 :=
    @gFvres (.cv p) (synCpw1 (synCxp A B))
      (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
  have p0002 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classEq (synCfv (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
            (synCpw1 (synCxp A B))) (.cv p))
        (synCfv (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (.cv p)))
      p0000 p0001
  have p0003 := @gN1stfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gWppsifnndv (synCvv) (synC1st)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gN2ndfo
  have p0009 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gWppsifnndv (synCvv) (synC2nd)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gPm32i (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
      (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv))) p0007 p0012
  have p0014 :=
    @gA1i
      (synWa (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
        (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0013
  have p0016 := @gSsv (synCxp A B)
  have p0017 := @gPw1ss (synCxp A B) (synCvv)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gSseli (synCpw1 (synCxp A B)) (synCpw1 (synCvv)) (.cv p) p0018
  have p0020 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv p) (synCpw1 (synCvv))) p0000 p0019
  have p0021 :=
    @gJca (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
        (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv))))
      (.classMem (.cv p) (synCpw1 (synCvv))) p0014 p0020
  have p0022 :=
    @gWpptxpfnvalndv p (synCpw1 (synCvv)) (synCsi (synC1st)) (synCsi (synC2nd))
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0023 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (synWa (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
          (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv))))
        (.classMem (.cv p) (synCpw1 (synCvv))))
      (.classEq (synCfv (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (.cv p))
        (synCop (synCfv (synCsi (synC1st)) (.cv p)) (synCfv (synCsi (synC2nd)) (.cv p))))
      p0021 p0022
  have p0024 := @gEqid (synCfv (synC1st) (synCuni (.cv p)))
  have p0028 := @gVex p
  have p0029 := @gUniex (.cv p) p0028
  have p0030 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv))
      p0005 p0029
  have p0031 :=
    @gFnbrfvb (synCvv) (synCuni (.cv p)) (synCfv (synC1st) (synCuni (.cv p)))
      (synC1st)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gMpbi
      (.classEq (synCfv (synC1st) (synCuni (.cv p))) (synCfv (synC1st) (synCuni (.cv p))))
      (synWbr (synCuni (.cv p)) (synC1st) (synCfv (synC1st) (synCuni (.cv p))))
      p0024 p0032
  have p0036 := @gFvex (synCuni (.cv p)) (synC1st)
  have p0037 :=
    @gBrsnsi (synCuni (.cv p)) (synCfv (synC1st) (synCuni (.cv p))) (synC1st) p0029
      p0036
  have p0038 :=
    @gMpbir
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC1st))
        (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      (synWbr (synCuni (.cv p)) (synC1st) (synCfv (synC1st) (synCuni (.cv p))))
      p0033 p0037
  have p0039 :=
    @gA1i
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC1st))
        (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0038
  have p0040 := @gHnwpw1argcl (synCxp A B) p
  have p0041 :=
    @gSimpr (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0042 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCuni (.cv p)) (synCxp A B))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0040 p0041
  have p0043 :=
    @gBreq1d (.classMem (.cv p) (synCpw1 (synCxp A B))) (.cv p)
      (synCsn (synCuni (.cv p))) (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsi (synC1st)) p0042
  have p0044 :=
    @gMpbird (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWbr (.cv p) (synCsi (synC1st)) (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC1st))
        (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      p0039 p0043
  have p0050 :=
    @gA1i (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0007
  have p0057 :=
    @gJca (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
      (.classMem (.cv p) (synCpw1 (synCvv))) p0050 p0020
  have p0058 :=
    @gFnbrfvb (synCpw1 (synCvv)) (.cv p)
      (synCsn (synCfv (synC1st) (synCuni (.cv p)))) (synCsi (synC1st))
  have p0059 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (synWfn (synCsi (synC1st)) (synCpw1 (synCvv)))
        (.classMem (.cv p) (synCpw1 (synCvv))))
      (synWb (.classEq (synCfv (synCsi (synC1st)) (.cv p))
          (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
        (synWbr (.cv p) (synCsi (synC1st))
          (synCsn (synCfv (synC1st) (synCuni (.cv p))))))
      p0057 p0058
  have p0060 :=
    @gMpbird (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classEq (synCfv (synCsi (synC1st)) (.cv p))
        (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      (synWbr (.cv p) (synCsi (synC1st)) (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      p0044 p0059
  have p0061 := @gEqid (synCfv (synC2nd) (synCuni (.cv p)))
  have p0067 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv))
      p0010 p0029
  have p0068 :=
    @gFnbrfvb (synCvv) (synCuni (.cv p)) (synCfv (synC2nd) (synCuni (.cv p)))
      (synC2nd)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 :=
    @gMpbi
      (.classEq (synCfv (synC2nd) (synCuni (.cv p))) (synCfv (synC2nd) (synCuni (.cv p))))
      (synWbr (synCuni (.cv p)) (synC2nd) (synCfv (synC2nd) (synCuni (.cv p))))
      p0061 p0069
  have p0073 := @gFvex (synCuni (.cv p)) (synC2nd)
  have p0074 :=
    @gBrsnsi (synCuni (.cv p)) (synCfv (synC2nd) (synCuni (.cv p))) (synC2nd) p0029
      p0073
  have p0075 :=
    @gMpbir
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC2nd))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synWbr (synCuni (.cv p)) (synC2nd) (synCfv (synC2nd) (synCuni (.cv p))))
      p0070 p0074
  have p0076 :=
    @gA1i
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC2nd))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0075
  have p0080 :=
    @gBreq1d (.classMem (.cv p) (synCpw1 (synCxp A B))) (.cv p)
      (synCsn (synCuni (.cv p))) (synCsn (synCfv (synC2nd) (synCuni (.cv p))))
      (synCsi (synC2nd)) p0042
  have p0081 :=
    @gMpbird (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWbr (.cv p) (synCsi (synC2nd)) (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synWbr (synCsn (synCuni (.cv p))) (synCsi (synC2nd))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      p0076 p0080
  have p0087 :=
    @gA1i (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv)))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0012
  have p0094 :=
    @gJca (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv)))
      (.classMem (.cv p) (synCpw1 (synCvv))) p0087 p0020
  have p0095 :=
    @gFnbrfvb (synCpw1 (synCvv)) (.cv p)
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) (synCsi (synC2nd))
  have p0096 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (synWfn (synCsi (synC2nd)) (synCpw1 (synCvv)))
        (.classMem (.cv p) (synCpw1 (synCvv))))
      (synWb (.classEq (synCfv (synCsi (synC2nd)) (.cv p))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
        (synWbr (.cv p) (synCsi (synC2nd))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0094 p0095
  have p0097 :=
    @gMpbird (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classEq (synCfv (synCsi (synC2nd)) (.cv p))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synWbr (.cv p) (synCsi (synC2nd)) (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      p0081 p0096
  have p0098 :=
    @gOpeq12d (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCfv (synCsi (synC1st)) (.cv p))
      (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCfv (synCsi (synC2nd)) (.cv p))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) p0060 p0097
  have p0099 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCfv (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (.cv p))
      (synCop (synCfv (synCsi (synC1st)) (.cv p)) (synCfv (synCsi (synC2nd)) (.cv p)))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      p0023 p0098
  have p0100 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCfv (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
          (synCpw1 (synCxp A B))) (.cv p))
      (synCfv (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (.cv p))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      p0002 p0099
  have p0101 := @gId (.classEq (.cv p) (.cv q))
  have p0102 := @gUnieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0101
  have p0103 :=
    @gFveq2d (.classEq (.cv p) (.cv q)) (synCuni (.cv p)) (synCuni (.cv q)) (synC1st)
      p0102
  have p0104 :=
    @gSneqd (.classEq (.cv p) (.cv q)) (synCfv (synC1st) (synCuni (.cv p)))
      (synCfv (synC1st) (synCuni (.cv q))) p0103
  have p0105 := @gId (.classEq (.cv p) (.cv q))
  have p0106 := @gUnieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0105
  have p0107 :=
    @gFveq2d (.classEq (.cv p) (.cv q)) (synCuni (.cv p)) (synCuni (.cv q)) (synC2nd)
      p0106
  have p0108 :=
    @gSneqd (.classEq (.cv p) (.cv q)) (synCfv (synC2nd) (synCuni (.cv p)))
      (synCfv (synC2nd) (synCuni (.cv q))) p0107
  have p0109 :=
    @gOpeq12d (.classEq (.cv p) (.cv q))
      (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC1st) (synCuni (.cv q))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv q)))) p0104 p0108
  have p0110_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (.classEq (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCfv synCio synCuni synWbr synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0110 :=
    @gCbvmptv p q (synCpw1 (synCxp A B))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0110_e00_recanon
  have p0111 :=
    @gFveq1i (.cv p)
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      (synCmpt q (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))
      p0110
  have p0112 :=
    @gEqcomi
      (synCfv (synCmpt p (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))) (.cv p))
      (synCfv (synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p))
      p0111
  have p0113 :=
    @gA1i
      (.classEq (synCfv (synCmpt q (synCpw1 (synCxp A B))
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p)) (synCfv
          (synCmpt p (synCpw1 (synCxp A B))
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))) (.cv p)))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0112
  have p0115 := @gSnex (synCfv (synC1st) (synCuni (.cv p)))
  have p0116 := @gSnex (synCfv (synC2nd) (synCuni (.cv p)))
  have p0117 :=
    @gOpex (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) p0115 p0116
  have p0118 :=
    @gA1i
      (.classMem (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))) (synCvv))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0117
  have p0119 :=
    @gJca (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))) (synCvv))
      p0000 p0118
  have p0120 :=
    @gEqid
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
  have p0121 :=
    @gFvmpt2 p (synCpw1 (synCxp A B))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCvv)
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      dv_cache_0004 p0120
  have p0122 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (.cv p) (synCpw1 (synCxp A B))) (.classMem
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p))))) (synCvv)))
      (.classEq (synCfv (synCmpt p (synCpw1 (synCxp A B))
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))) (.cv p))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0119 p0121
  have p0123 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCfv (synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p))
      (synCfv (synCmpt p (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))) (.cv p))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      p0113 p0122
  have p0124 :=
    @gEqtr4d (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCfv (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
          (synCpw1 (synCxp A B))) (.cv p))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCfv (synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p))
      p0100 p0123
  have p0125 :=
    @gRgen
      (.classEq (synCfv (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
            (synCpw1 (synCxp A B))) (.cv p)) (synCfv (synCmpt q (synCpw1 (synCxp A B))
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p)))
      p (synCpw1 (synCxp A B)) p0124
  have p0137 :=
    @gFntxp (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsi (synC1st))
      (synCsi (synC2nd))
  have p0138 := Nominal.mp p0013 p0137
  have p0139 := @gInidm (synCpw1 (synCvv))
  have p0140 :=
    @gFneq2i (synCin (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCpw1 (synCvv))
      (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) p0139
  have p0141 :=
    @gMpbi
      (synWfn (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
        (synCin (synCpw1 (synCvv)) (synCpw1 (synCvv))))
      (synWfn (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCvv)))
      p0138 p0140
  have p0145 :=
    @gPm32i
      (synWfn (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCvv)))
      (synWss (synCpw1 (synCxp A B)) (synCpw1 (synCvv))) p0141 p0018
  have p0146 :=
    @gFnssres (synCpw1 (synCvv)) (synCpw1 (synCxp A B))
      (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
  have p0147 := Nominal.mp p0145 p0146
  have p0148 := @gSnex (synCfv (synC1st) (synCuni (.cv q)))
  have p0149 := @gSnex (synCfv (synC2nd) (synCuni (.cv q)))
  have p0150 :=
    @gOpex (synCsn (synCfv (synC1st) (synCuni (.cv q))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv q)))) p0148 p0149
  have p0151 :=
    @gEqid
      (synCmpt q (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))
  have p0152 :=
    @gFnmpti q (synCpw1 (synCxp A B))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))
      (synCmpt q (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))
      dv_cache_0005 p0150 p0151
  have p0153 :=
    @gPm32i
      (synWfn (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
          (synCpw1 (synCxp A B))) (synCpw1 (synCxp A B)))
      (synWfn (synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (synCpw1 (synCxp A B)))
      p0147 p0152
  have p0154 :=
    @gEqfnfv p (synCpw1 (synCxp A B))
      (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCxp A B)))
      (synCmpt q (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))
      dv_cache_0004 dv_cache_0008 dv_cache_0009
  have p0155 := Nominal.mp p0153 p0154
  have p0156 :=
    @gMpbir
      (.classEq (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
          (synCpw1 (synCxp A B))) (synCmpt q (synCpw1 (synCxp A B))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))))
      (synWral p (synCpw1 (synCxp A B)) (.classEq (synCfv
            (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd)))
              (synCpw1 (synCxp A B))) (.cv p)) (synCfv (synCmpt q (synCpw1 (synCxp A B))
              (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))) (.cv p))))
      p0125 p0155
  have p0157 := @gId (.classEq (.cv p) (.cv q))
  have p0158 := @gUnieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0157
  have p0159 :=
    @gFveq2d (.classEq (.cv p) (.cv q)) (synCuni (.cv p)) (synCuni (.cv q)) (synC1st)
      p0158
  have p0160 :=
    @gSneqd (.classEq (.cv p) (.cv q)) (synCfv (synC1st) (synCuni (.cv p)))
      (synCfv (synC1st) (synCuni (.cv q))) p0159
  have p0161 := @gId (.classEq (.cv p) (.cv q))
  have p0162 := @gUnieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0161
  have p0163 :=
    @gFveq2d (.classEq (.cv p) (.cv q)) (synCuni (.cv p)) (synCuni (.cv q)) (synC2nd)
      p0162
  have p0164 :=
    @gSneqd (.classEq (.cv p) (.cv q)) (synCfv (synC2nd) (synCuni (.cv p)))
      (synCfv (synC2nd) (synCuni (.cv q))) p0163
  have p0165 :=
    @gOpeq12d (.classEq (.cv p) (.cv q))
      (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC1st) (synCuni (.cv q))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv q)))) p0160 p0164
  have p0166_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (.classEq (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCfv synCio synCuni synWbr synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0165
  have p0166 :=
    @gCbvmptv p q (synCpw1 (synCxp A B))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv q)))))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0166_e00_recanon
  have p0167 :=
    @gEqtr4i
      (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCxp A B)))
      (synCmpt q (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv q))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv q))))))
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0156 p0166
  have p0168 := @gN1stex
  have p0169 := @gSiex (synC1st) p0168
  have p0170 := @gN2ndex
  have p0171 := @gSiex (synC2nd) p0170
  have p0172 := @gTxpex (synCsi (synC1st)) (synCsi (synC2nd)) p0169 p0171
  have p0173 := @gXpex A B hyp_pw1xpshiftsetndv_1 hyp_pw1xpshiftsetndv_2
  have p0174 := @gPw1ex (synCxp A B) p0173
  have p0175 :=
    @gResex (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCxp A B))
      p0172 p0174
  have p0176 :=
    @gEqeltrri
      (synCres (synCtxp (synCsi (synC1st)) (synCsi (synC2nd))) (synCpw1 (synCxp A B)))
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      (synCvv) p0167 p0175
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

/-- Checked nominal proof certificate identified upstream as `g_pw1xpshiftenndv`. -/
@[expose]
noncomputable def gPw1xpshiftenndv (A : Class) (B : Class)
    (hyp_pw1xpshiftenndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_pw1xpshiftenndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWbr (synCpw1 (synCxp A B)) (synCen) (synCxp (synCpw1 A) (synCpw1 B))) :=
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
  have dv_cache_0001 : p ∉ ((synCpw1 (synCxp A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCpw1 (synCxp A B))).fv :=
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
  have dv_cache_0003 : p ∉ ((synCxp (synCpw1 A) (synCpw1 B))).fv :=
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
  have dv_cache_0004 : q ∉ ((synCxp (synCpw1 A) (synCpw1 B))).fv :=
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
      ((synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))).fv :=
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
      ((synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q)))))).fv :=
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
  have dv_cache_0007 : p ∉ (synWtru).fv :=
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
  have dv_cache_0008 : q ∉ (synWtru).fv :=
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
  have p0000 := @gTru
  have p0001 :=
    @gEqid
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
  have p0002 := @gSimpr synWtru (.classMem (.cv p) (synCpw1 (synCxp A B)))
  have p0003 := @gHnwpw1argcl (synCxp A B) p
  have p0004 :=
    @gSimpl (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0005 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCuni (.cv p)) (synCxp A B))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classMem (synCuni (.cv p)) (synCxp A B)) p0003 p0004
  have p0006 := @gId (.classMem (synCuni (.cv p)) (synCxp A B))
  have p0007 := @gN1st2nd2 (synCuni (.cv p)) A B
  have p0008 :=
    @gEleq1d (.classMem (synCuni (.cv p)) (synCxp A B)) (synCuni (.cv p))
      (synCop (synCfv (synC1st) (synCuni (.cv p))) (synCfv (synC2nd) (synCuni (.cv p))))
      (synCxp A B) p0007
  have p0009 :=
    @gMpbid (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classMem (synCop (synCfv (synC1st) (synCuni (.cv p)))
          (synCfv (synC2nd) (synCuni (.cv p)))) (synCxp A B))
      p0006 p0008
  have p0010 :=
    @gOpelxp (synCfv (synC1st) (synCuni (.cv p)))
      (synCfv (synC2nd) (synCuni (.cv p))) A B
  have p0011 :=
    @gSylib (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classMem (synCop (synCfv (synC1st) (synCuni (.cv p)))
          (synCfv (synC2nd) (synCuni (.cv p)))) (synCxp A B))
      (synWa (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
        (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B))
      p0009 p0010
  have p0012 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCuni (.cv p)) (synCxp A B))
      (synWa (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
        (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B))
      p0005 p0011
  have p0013 :=
    @gSimpl (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
      (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B)
  have p0014 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
        (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B))
      (.classMem (synCfv (synC1st) (synCuni (.cv p))) A) p0012 p0013
  have p0015 := @gSnelpw1 (synCfv (synC1st) (synCuni (.cv p))) A
  have p0016 :=
    @gSylibr (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
      (.classMem (synCsn (synCfv (synC1st) (synCuni (.cv p)))) (synCpw1 A)) p0014
      p0015
  have p0027 :=
    @gSimpr (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
      (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B)
  have p0028 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCfv (synC1st) (synCuni (.cv p))) A)
        (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B))
      (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B) p0012 p0027
  have p0029 := @gSnelpw1 (synCfv (synC2nd) (synCuni (.cv p))) B
  have p0030 :=
    @gSylibr (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCfv (synC2nd) (synCuni (.cv p))) B)
      (.classMem (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) (synCpw1 B)) p0028
      p0029
  have p0031 :=
    @gJca (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCsn (synCfv (synC1st) (synCuni (.cv p)))) (synCpw1 A))
      (.classMem (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) (synCpw1 B)) p0016
      p0030
  have p0032 :=
    @gOpelxp (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) (synCpw1 A) (synCpw1 B)
  have p0033 :=
    @gSylibr (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCsn (synCfv (synC1st) (synCuni (.cv p)))) (synCpw1 A))
        (.classMem (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) (synCpw1 B)))
      (.classMem (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
        (synCxp (synCpw1 A) (synCpw1 B)))
      p0031 p0032
  have p0034 :=
    @gSyl (synWa synWtru (.classMem (.cv p) (synCpw1 (synCxp A B))))
      (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
        (synCxp (synCpw1 A) (synCpw1 B)))
      p0002 p0033
  have p0035 := @gSimpr synWtru (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
  have p0036 := @gId (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
  have p0037 := @gN1st2nd2 (.cv q) (synCpw1 A) (synCpw1 B)
  have p0038 :=
    @gEleq1d (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) (.cv q)
      (synCop (synCfv (synC1st) (.cv q)) (synCfv (synC2nd) (.cv q)))
      (synCxp (synCpw1 A) (synCpw1 B)) p0037
  have p0039 :=
    @gMpbid (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCop (synCfv (synC1st) (.cv q)) (synCfv (synC2nd) (.cv q)))
        (synCxp (synCpw1 A) (synCpw1 B)))
      p0036 p0038
  have p0040 :=
    @gOpelxp (synCfv (synC1st) (.cv q)) (synCfv (synC2nd) (.cv q)) (synCpw1 A)
      (synCpw1 B)
  have p0041 :=
    @gSylib (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCop (synCfv (synC1st) (.cv q)) (synCfv (synC2nd) (.cv q)))
        (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
        (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B)))
      p0039 p0040
  have p0042 :=
    @gSimpl (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
      (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B))
  have p0043 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
        (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B)))
      (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A)) p0041 p0042
  have p0044 := @gHnwpw1argclcndv (synCfv (synC1st) (.cv q)) A
  have p0045 :=
    @gSimpl (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
      (.classEq (synCfv (synC1st) (.cv q)) (synCsn (synCuni (synCfv (synC1st) (.cv q)))))
  have p0046 :=
    @gSyl (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
      (synWa (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
        (.classEq (synCfv (synC1st) (.cv q))
          (synCsn (synCuni (synCfv (synC1st) (.cv q))))))
      (.classMem (synCuni (synCfv (synC1st) (.cv q))) A) p0044 p0045
  have p0047 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
      (.classMem (synCuni (synCfv (synC1st) (.cv q))) A) p0043 p0046
  have p0054 :=
    @gSimpr (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
      (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B))
  have p0055 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
        (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B)))
      (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B)) p0041 p0054
  have p0056 := @gHnwpw1argclcndv (synCfv (synC2nd) (.cv q)) B
  have p0057 :=
    @gSimpl (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B)
      (.classEq (synCfv (synC2nd) (.cv q)) (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
  have p0058 :=
    @gSyl (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B))
      (synWa (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B)
        (.classEq (synCfv (synC2nd) (.cv q))
          (synCsn (synCuni (synCfv (synC2nd) (.cv q))))))
      (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B) p0056 p0057
  have p0059 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B))
      (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B) p0055 p0058
  have p0060 :=
    @gJca (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
      (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B) p0047 p0059
  have p0061 :=
    @gOpelxp (synCuni (synCfv (synC1st) (.cv q)))
      (synCuni (synCfv (synC2nd) (.cv q))) A B
  have p0062 :=
    @gSylibr (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
        (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B))
      (.classMem (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))) (synCxp A B))
      p0060 p0061
  have p0063 :=
    @gSnelpw1
      (synCop (synCuni (synCfv (synC1st) (.cv q))) (synCuni (synCfv (synC2nd) (.cv q))))
      (synCxp A B)
  have p0064 :=
    @gSylibr (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))) (synCxp A B))
      (.classMem (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))) (synCpw1 (synCxp A B)))
      p0062 p0063
  have p0065 :=
    @gSyl (synWa synWtru (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))) (synCpw1 (synCxp A B)))
      p0035 p0064
  have p0066 :=
    @gSimpr
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classEq (.cv p) (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
  have p0067 :=
    @gUnieqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (.cv p)
      (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      p0066
  have p0068 :=
    @gFveq2d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCuni (.cv p))
      (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
      (synC1st) p0067
  have p0069 :=
    @gSneqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCfv (synC1st) (synCuni (.cv p)))
      (synCfv (synC1st) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      p0068
  have p0072 :=
    @gFveq2d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCuni (.cv p))
      (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
      (synC2nd) p0067
  have p0073 :=
    @gSneqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCfv (synC2nd) (synCuni (.cv p)))
      (synCfv (synC2nd) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      p0072
  have p0074 :=
    @gOpeq12d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC1st) (synCuni (synCsn
              (synCop (synCuni (synCfv (synC1st) (.cv q)))
                (synCuni (synCfv (synC2nd) (.cv q))))))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (synCsn
              (synCop (synCuni (synCfv (synC1st) (.cv q)))
                (synCuni (synCfv (synC2nd) (.cv q))))))))
      p0069 p0073
  have p0075 :=
    @gSimpl
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classEq (.cv p) (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
  have p0076 :=
    @gSimpr synWtru
      (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
        (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))
  have p0077 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
  have p0078 :=
    @gSyl
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
        (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) p0076 p0077
  have p0079 :=
    @gSyl
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) p0075 p0078
  have p0080 := @gFvex (.cv q) (synC1st)
  have p0081 := @gUniex (synCfv (synC1st) (.cv q)) p0080
  have p0082 := @gFvex (.cv q) (synC2nd)
  have p0083 := @gUniex (synCfv (synC2nd) (.cv q)) p0082
  have p0084 :=
    @gOpex (synCuni (synCfv (synC1st) (.cv q)))
      (synCuni (synCfv (synC2nd) (.cv q))) p0081 p0083
  have p0085 :=
    @gUnisn
      (synCop (synCuni (synCfv (synC1st) (.cv q))) (synCuni (synCfv (synC2nd) (.cv q))))
      p0084
  have p0086 :=
    @gFveq2i
      (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
      (synCop (synCuni (synCfv (synC1st) (.cv q))) (synCuni (synCfv (synC2nd) (.cv q))))
      (synC1st) p0085
  have p0091 :=
    @gOpfv1st (synCuni (synCfv (synC1st) (.cv q)))
      (synCuni (synCfv (synC2nd) (.cv q))) p0081 p0083
  have p0092 :=
    @gEqtri
      (synCfv (synC1st) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCfv (synC1st) (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      (synCuni (synCfv (synC1st) (.cv q))) p0086 p0091
  have p0093 :=
    @gSneqi
      (synCfv (synC1st) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCuni (synCfv (synC1st) (.cv q))) p0092
  have p0100 :=
    @gFveq2i
      (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
      (synCop (synCuni (synCfv (synC1st) (.cv q))) (synCuni (synCfv (synC2nd) (.cv q))))
      (synC2nd) p0085
  have p0105 :=
    @gOpfv2nd (synCuni (synCfv (synC1st) (.cv q)))
      (synCuni (synCfv (synC2nd) (.cv q))) p0081 p0083
  have p0106 :=
    @gEqtri
      (synCfv (synC2nd) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCfv (synC2nd) (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      (synCuni (synCfv (synC2nd) (.cv q))) p0100 p0105
  have p0107 :=
    @gSneqi
      (synCfv (synC2nd) (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCuni (synCfv (synC2nd) (.cv q))) p0106
  have p0108 :=
    @gOpeq12i
      (synCsn (synCfv (synC1st) (synCuni (synCsn
              (synCop (synCuni (synCfv (synC1st) (.cv q)))
                (synCuni (synCfv (synC2nd) (.cv q))))))))
      (synCsn (synCuni (synCfv (synC1st) (.cv q))))
      (synCsn (synCfv (synC2nd) (synCuni (synCsn
              (synCop (synCuni (synCfv (synC1st) (.cv q)))
                (synCuni (synCfv (synC2nd) (.cv q))))))))
      (synCsn (synCuni (synCfv (synC2nd) (.cv q)))) p0093 p0107
  have p0109 :=
    @gA1i
      (.classEq (synCop (synCsn (synCfv (synC1st) (synCuni (synCsn
                  (synCop (synCuni (synCfv (synC1st) (.cv q)))
                    (synCuni (synCfv (synC2nd) (.cv q)))))))) (synCsn (synCfv (synC2nd)
              (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
                    (synCuni (synCfv (synC2nd) (.cv q)))))))))
        (synCop (synCsn (synCuni (synCfv (synC1st) (.cv q))))
          (synCsn (synCuni (synCfv (synC2nd) (.cv q))))))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) p0108
  have p0120 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCfv (synC1st) (.cv q)) (synCpw1 A))
      (synWa (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
        (.classEq (synCfv (synC1st) (.cv q))
          (synCsn (synCuni (synCfv (synC1st) (.cv q))))))
      p0043 p0044
  have p0121 :=
    @gSimpr (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
      (.classEq (synCfv (synC1st) (.cv q)) (synCsn (synCuni (synCfv (synC1st) (.cv q)))))
  have p0122 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCuni (synCfv (synC1st) (.cv q))) A)
        (.classEq (synCfv (synC1st) (.cv q))
          (synCsn (synCuni (synCfv (synC1st) (.cv q))))))
      (.classEq (synCfv (synC1st) (.cv q)) (synCsn (synCuni (synCfv (synC1st) (.cv q)))))
      p0120 p0121
  have p0132 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classMem (synCfv (synC2nd) (.cv q)) (synCpw1 B))
      (synWa (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B)
        (.classEq (synCfv (synC2nd) (.cv q))
          (synCsn (synCuni (synCfv (synC2nd) (.cv q))))))
      p0055 p0056
  have p0133 :=
    @gSimpr (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B)
      (.classEq (synCfv (synC2nd) (.cv q)) (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
  have p0134 :=
    @gSyl (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synWa (.classMem (synCuni (synCfv (synC2nd) (.cv q))) B)
        (.classEq (synCfv (synC2nd) (.cv q))
          (synCsn (synCuni (synCfv (synC2nd) (.cv q))))))
      (.classEq (synCfv (synC2nd) (.cv q)) (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
      p0132 p0133
  have p0135 :=
    @gOpeq12d (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synCfv (synC1st) (.cv q)) (synCsn (synCuni (synCfv (synC1st) (.cv q))))
      (synCfv (synC2nd) (.cv q)) (synCsn (synCuni (synCfv (synC2nd) (.cv q)))) p0122
      p0134
  have p0136 :=
    @gEqtrd (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) (.cv q)
      (synCop (synCfv (synC1st) (.cv q)) (synCfv (synC2nd) (.cv q)))
      (synCop (synCsn (synCuni (synCfv (synC1st) (.cv q))))
        (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
      p0037 p0135
  have p0137 :=
    @gEqcomd (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))) (.cv q)
      (synCop (synCsn (synCuni (synCfv (synC1st) (.cv q))))
        (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
      p0136
  have p0138 :=
    @gEqtrd (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (synCop (synCsn (synCfv (synC1st) (synCuni (synCsn
                (synCop (synCuni (synCfv (synC1st) (.cv q)))
                  (synCuni (synCfv (synC2nd) (.cv q)))))))) (synCsn (synCfv (synC2nd)
            (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
                  (synCuni (synCfv (synC2nd) (.cv q)))))))))
      (synCop (synCsn (synCuni (synCfv (synC1st) (.cv q))))
        (synCsn (synCuni (synCfv (synC2nd) (.cv q)))))
      (.cv q) p0109 p0137
  have p0139 :=
    @gSyl
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
      (.classEq (synCop (synCsn (synCfv (synC1st) (synCuni (synCsn
                  (synCop (synCuni (synCfv (synC1st) (.cv q)))
                    (synCuni (synCfv (synC2nd) (.cv q)))))))) (synCsn (synCfv (synC2nd)
              (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
                    (synCuni (synCfv (synC2nd) (.cv q))))))))) (.cv q))
      p0079 p0138
  have p0140 :=
    @gEqtrd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCop (synCsn (synCfv (synC1st) (synCuni (synCsn
                (synCop (synCuni (synCfv (synC1st) (.cv q)))
                  (synCuni (synCfv (synC2nd) (.cv q)))))))) (synCsn (synCfv (synC2nd)
            (synCuni (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
                  (synCuni (synCfv (synC2nd) (.cv q)))))))))
      (.cv q) p0074 p0139
  have p0141 :=
    @gEqcomd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv p) (synCsn
            (synCop (synCuni (synCfv (synC1st) (.cv q)))
              (synCuni (synCfv (synC2nd) (.cv q)))))))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (.cv q) p0140
  have p0142 :=
    @gSimpr
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classEq (.cv q) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
  have p0143 :=
    @gFveq2d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (.cv q)
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synC1st) p0142
  have p0144 :=
    @gUnieqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCfv (synC1st) (.cv q))
      (synCfv (synC1st) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0143
  have p0146 :=
    @gFveq2d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (.cv q)
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synC2nd) p0142
  have p0147 :=
    @gUnieqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCfv (synC2nd) (.cv q))
      (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0146
  have p0148 :=
    @gOpeq12d
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCuni (synCfv (synC1st) (.cv q)))
      (synCuni (synCfv (synC1st) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCuni (synCfv (synC2nd) (.cv q)))
      (synCuni (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      p0144 p0147
  have p0149 :=
    @gSneqd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCop (synCuni (synCfv (synC1st) (.cv q))) (synCuni (synCfv (synC2nd) (.cv q))))
      (synCop (synCuni (synCfv (synC1st)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni (synCfv (synC2nd)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))))
      p0148
  have p0150 :=
    @gSimpl
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classEq (.cv q) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
  have p0152 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))
  have p0153 :=
    @gSyl
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
        (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0076 p0152
  have p0154 :=
    @gSyl
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0150 p0153
  have p0155 := @gSnex (synCfv (synC1st) (synCuni (.cv p)))
  have p0156 := @gSnex (synCfv (synC2nd) (synCuni (.cv p)))
  have p0157 :=
    @gOpfv1st (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) p0155 p0156
  have p0158 :=
    @gUnieqi
      (synCfv (synC1st) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      (synCsn (synCfv (synC1st) (synCuni (.cv p)))) p0157
  have p0159 := @gFvex (synCuni (.cv p)) (synC1st)
  have p0160 := @gUnisn (synCfv (synC1st) (synCuni (.cv p))) p0159
  have p0161 :=
    @gEqtri
      (synCuni (synCfv (synC1st) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCuni (synCsn (synCfv (synC1st) (synCuni (.cv p)))))
      (synCfv (synC1st) (synCuni (.cv p))) p0158 p0160
  have p0164 :=
    @gOpfv2nd (synCsn (synCfv (synC1st) (synCuni (.cv p))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) p0155 p0156
  have p0165 :=
    @gUnieqi
      (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      (synCsn (synCfv (synC2nd) (synCuni (.cv p)))) p0164
  have p0166 := @gFvex (synCuni (.cv p)) (synC2nd)
  have p0167 := @gUnisn (synCfv (synC2nd) (synCuni (.cv p))) p0166
  have p0168 :=
    @gEqtri
      (synCuni (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCuni (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCfv (synC2nd) (synCuni (.cv p))) p0165 p0167
  have p0169 :=
    @gOpeq12i
      (synCuni (synCfv (synC1st) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCfv (synC1st) (synCuni (.cv p)))
      (synCuni (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCfv (synC2nd) (synCuni (.cv p))) p0161 p0168
  have p0170 :=
    @gA1i
      (.classEq (synCop (synCuni (synCfv (synC1st)
              (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni
            (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))))
        (synCop (synCfv (synC1st) (synCuni (.cv p)))
          (synCfv (synC2nd) (synCuni (.cv p)))))
      (.classMem (.cv p) (synCpw1 (synCxp A B))) p0169
  have p0175 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classEq (synCuni (.cv p)) (synCop (synCfv (synC1st) (synCuni (.cv p)))
          (synCfv (synC2nd) (synCuni (.cv p)))))
      p0005 p0007
  have p0176 :=
    @gEqtr4d (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCop (synCuni (synCfv (synC1st)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni (synCfv (synC2nd)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))))
      (synCop (synCfv (synC1st) (synCuni (.cv p))) (synCfv (synC2nd) (synCuni (.cv p))))
      (synCuni (.cv p)) p0170 p0175
  have p0177 :=
    @gSneqd (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCop (synCuni (synCfv (synC1st)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni (synCfv (synC2nd)
            (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
              (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))))
      (synCuni (.cv p)) p0176
  have p0179 :=
    @gSimpr (.classMem (synCuni (.cv p)) (synCxp A B))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0180 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synWa (.classMem (synCuni (.cv p)) (synCxp A B))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0003 p0179
  have p0181 :=
    @gEqcomd (.classMem (.cv p) (synCpw1 (synCxp A B))) (.cv p)
      (synCsn (synCuni (.cv p))) p0180
  have p0182 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (synCsn (synCop (synCuni (synCfv (synC1st)
              (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni
            (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))))
      (synCsn (synCuni (.cv p))) (.cv p) p0177 p0181
  have p0183 :=
    @gSyl
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (.classMem (.cv p) (synCpw1 (synCxp A B)))
      (.classEq (synCsn (synCop (synCuni (synCfv (synC1st)
                (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                  (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni
              (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                  (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))))) (.cv p))
      p0154 p0182
  have p0184 :=
    @gEqtrd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      (synCsn (synCop (synCuni (synCfv (synC1st)
              (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))) (synCuni
            (synCfv (synC2nd) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
                (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))))
      (.cv p) p0149 p0183
  have p0185 :=
    @gEqcomd
      (synWa (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
            (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B))))) (.classEq (.cv q)
          (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
            (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))))
      (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      (.cv p) p0184
  have p0186 :=
    @gImpbida
      (synWa synWtru (synWa (.classMem (.cv p) (synCpw1 (synCxp A B)))
          (.classMem (.cv q) (synCxp (synCpw1 A) (synCpw1 B)))))
      (.classEq (.cv p) (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
            (synCuni (synCfv (synC2nd) (.cv q))))))
      (.classEq (.cv q) (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0141 p0185
  have p0187 :=
    @gF1o2d synWtru p q (synCpw1 (synCxp A B)) (synCxp (synCpw1 A) (synCpw1 B))
      (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
        (synCsn (synCfv (synC2nd) (synCuni (.cv p)))))
      (synCsn (synCop (synCuni (synCfv (synC1st) (.cv q)))
          (synCuni (synCfv (synC2nd) (.cv q)))))
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0034 p0065 p0186
  have p0188 := Nominal.mp p0000 p0187
  have p0189 :=
    @gPw1xpshiftsetndv A B p dv_cache_0010 dv_cache_0011 hyp_pw1xpshiftenndv_1
      hyp_pw1xpshiftenndv_2
  have p0190 :=
    @gF1oen (synCpw1 (synCxp A B)) (synCxp (synCpw1 A) (synCpw1 B))
      (synCmpt p (synCpw1 (synCxp A B))
        (synCop (synCsn (synCfv (synC1st) (synCuni (.cv p))))
          (synCsn (synCfv (synC2nd) (synCuni (.cv p))))))
      p0189
  have p0191 := Nominal.mp p0188 p0190
  exact p0191

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelpw1shiftenndv`. -/
@[expose]
noncomputable def gWppqkrelpw1shiftenndv (X : Class)
    (hyp_wppqkrelpw1shiftenndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (synWbr (synCpw1 (synCxpk X X)) (synCen) (synCxpk (synCpw1 X) (synCpw1 X))) :=
  by
  have p0000 :=
    @gWppqkrelrestypedenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0001 := @gEnpw1 (synCpw1 (synCpw1 (synCxp X X))) (synCxpk X X)
  have p0002 :=
    @gMpbi (synWbr (synCpw1 (synCpw1 (synCxp X X))) (synCen) (synCxpk X X))
      (synWbr (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCen)
        (synCpw1 (synCxpk X X)))
      p0000 p0001
  have p0003 :=
    @gEnsym (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCpw1 (synCxpk X X))
  have p0004 :=
    @gMpbi
      (synWbr (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCen)
        (synCpw1 (synCxpk X X)))
      (synWbr (synCpw1 (synCxpk X X)) (synCen)
        (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))))
      p0002 p0003
  have p0005 :=
    @gPw1xpshiftenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0006 := @gEnpw1 (synCpw1 (synCxp X X)) (synCxp (synCpw1 X) (synCpw1 X))
  have p0007 :=
    @gMpbi
      (synWbr (synCpw1 (synCxp X X)) (synCen) (synCxp (synCpw1 X) (synCpw1 X)))
      (synWbr (synCpw1 (synCpw1 (synCxp X X))) (synCen)
        (synCpw1 (synCxp (synCpw1 X) (synCpw1 X))))
      p0005 p0006
  have p0008 :=
    @gEnpw1 (synCpw1 (synCpw1 (synCxp X X)))
      (synCpw1 (synCxp (synCpw1 X) (synCpw1 X)))
  have p0009 :=
    @gMpbi
      (synWbr (synCpw1 (synCpw1 (synCxp X X))) (synCen)
        (synCpw1 (synCxp (synCpw1 X) (synCpw1 X))))
      (synWbr (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCen)
        (synCpw1 (synCpw1 (synCxp (synCpw1 X) (synCpw1 X)))))
      p0007 p0008
  have p0010 := @gPw1ex X hyp_wppqkrelpw1shiftenndv_1
  have p0012 := @gWppqkrelrestypedenndv (synCpw1 X) (synCpw1 X) p0010 p0010
  have p0013 :=
    @gPm32i
      (synWbr (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCen)
        (synCpw1 (synCpw1 (synCxp (synCpw1 X) (synCpw1 X)))))
      (synWbr (synCpw1 (synCpw1 (synCxp (synCpw1 X) (synCpw1 X)))) (synCen)
        (synCxpk (synCpw1 X) (synCpw1 X)))
      p0009 p0012
  have p0014 :=
    @gEntr (synCpw1 (synCpw1 (synCpw1 (synCxp X X))))
      (synCpw1 (synCpw1 (synCxp (synCpw1 X) (synCpw1 X))))
      (synCxpk (synCpw1 X) (synCpw1 X))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gPm32i
      (synWbr (synCpw1 (synCxpk X X)) (synCen)
        (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))))
      (synWbr (synCpw1 (synCpw1 (synCpw1 (synCxp X X)))) (synCen)
        (synCxpk (synCpw1 X) (synCpw1 X)))
      p0004 p0015
  have p0017 :=
    @gEntr (synCpw1 (synCxpk X X)) (synCpw1 (synCpw1 (synCpw1 (synCxp X X))))
      (synCxpk (synCpw1 X) (synCpw1 X))
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_wpplitshiftenndv`. -/
@[expose]
noncomputable def gWpplitshiftenndv (X : Class)
    (hyp_wpplitshiftenndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (synWbr (synCpw1 (synCxp (synCxpk X X) (synCnnc))) (synCen)
        (synCxp (synCxpk (synCpw1 X) (synCpw1 X)) (synCnnc))) :=
  by
  have p0000 := @gXpkex X X hyp_wpplitshiftenndv_1 hyp_wpplitshiftenndv_1
  have p0001 := @gNncex
  have p0002 := @gPw1xpshiftenndv (synCxpk X X) (synCnnc) p0000 p0001
  have p0003 := @gWppqkrelpw1shiftenndv X hyp_wpplitshiftenndv_1
  have p0004 := @gTcnnf1o
  have p0005 := @gTcfnex
  have p0007 := @gPw1ex (synCnnc) p0001
  have p0008 := @gResex (synCtcfn) (synCpw1 (synCnnc)) p0005 p0007
  have p0009 :=
    @gF1oen (synCpw1 (synCnnc)) (synCnnc) (synCres (synCtcfn) (synCpw1 (synCnnc)))
      p0008
  have p0010 := Nominal.mp p0004 p0009
  have p0011 :=
    @gPm32i
      (synWbr (synCpw1 (synCxpk X X)) (synCen) (synCxpk (synCpw1 X) (synCpw1 X)))
      (synWbr (synCpw1 (synCnnc)) (synCen) (synCnnc)) p0003 p0010
  have p0012 :=
    @gXpen (synCpw1 (synCxpk X X)) (synCxpk (synCpw1 X) (synCpw1 X))
      (synCpw1 (synCnnc)) (synCnnc)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gPm32i
      (synWbr (synCpw1 (synCxp (synCxpk X X) (synCnnc))) (synCen)
        (synCxp (synCpw1 (synCxpk X X)) (synCpw1 (synCnnc))))
      (synWbr (synCxp (synCpw1 (synCxpk X X)) (synCpw1 (synCnnc))) (synCen)
        (synCxp (synCxpk (synCpw1 X) (synCpw1 X)) (synCnnc)))
      p0002 p0013
  have p0015 :=
    @gEntr (synCpw1 (synCxp (synCxpk X X) (synCnnc)))
      (synCxp (synCpw1 (synCxpk X X)) (synCpw1 (synCnnc)))
      (synCxp (synCxpk (synCpw1 X) (synCpw1 X)) (synCnnc))
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

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6dmrepdndv`. -/
@[expose]
noncomputable def gWppconcrete6dmrepdndv (x : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (synCdm (synCwppconcrete6fn))) (synWex z (.classEq (.cv x)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))) :=
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
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))).fv :=
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
  have dv_cache_0003 : q ∉ ((synCwppcardt6fn)).fv :=
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
    z ∉ ((synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))).fv :=
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
      ((synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))).fv :=
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
      ((synWex z (.classEq (.cv x) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))).fv :=
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
  have p0000 := @gWppconcrete6fndmndv
  have p0001 :=
    @gEleq2i (synCdm (synCwppconcrete6fn)) (synCrn (synCwppcardt6fn)) (.cv x) p0000
  have p0002 :=
    @gBiimpi (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv x) (synCrn (synCwppcardt6fn))) p0001
  have p0003 := @gWppcardt6fnmapndv
  have p0004 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gFvelrnb q
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (.cv x)
      (synCwppcardt6fn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gBiimpi (.classMem (.cv x) (synCrn (synCwppcardt6fn)))
      (synWrex q (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      p0007
  have p0009 :=
    @gSyl (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv x) (synCrn (synCwppcardt6fn)))
      (synWrex q (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      p0002 p0008
  have p0010 :=
    @gSimpl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))
  have p0011 :=
    @gId
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
  have p0012 :=
    @gPw1argclcl (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.cv q)
  have p0013 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (.cv q))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0011 p0012
  have p0014 :=
    @gSimpl
      (.classMem (synCuni (.cv q))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0015 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (.cv q))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0013 p0014
  have p0016 :=
    @gPw1argclcl (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCuni (.cv q))
  have p0017 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (.cv q))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synWa (.classMem (synCuni (synCuni (.cv q)))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
        (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))))
      p0015 p0016
  have p0018 :=
    @gSimpl
      (.classMem (synCuni (synCuni (.cv q)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q)))))
  have p0019 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (.cv q)))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
        (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))))
      (.classMem (synCuni (synCuni (.cv q)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0017 p0018
  have p0020 :=
    @gPw1argclcl (synCpw1 (synCpw1 (synCpw1 (synCncs))))
      (synCuni (synCuni (.cv q)))
  have p0021 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (.cv q)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (.cv q))))
          (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (.classEq (synCuni (synCuni (.cv q)))
          (synCsn (synCuni (synCuni (synCuni (.cv q)))))))
      p0019 p0020
  have p0022 :=
    @gSimpl
      (.classMem (synCuni (synCuni (synCuni (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classEq (synCuni (synCuni (.cv q)))
        (synCsn (synCuni (synCuni (synCuni (.cv q))))))
  have p0023 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (.cv q))))
          (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (.classEq (synCuni (synCuni (.cv q)))
          (synCsn (synCuni (synCuni (synCuni (.cv q)))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0021 p0022
  have p0024 :=
    @gPw1argclcl (synCpw1 (synCpw1 (synCncs)))
      (synCuni (synCuni (synCuni (.cv q))))
  have p0025 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCpw1 (synCpw1 (synCncs)))) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
      p0023 p0024
  have p0026 :=
    @gSimpl
      (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCpw1 (synCpw1 (synCncs))))
      (.classEq (synCuni (synCuni (synCuni (.cv q))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
  have p0027 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCpw1 (synCpw1 (synCncs)))) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCpw1 (synCpw1 (synCncs))))
      p0025 p0026
  have p0028 :=
    @gPw1argclcl (synCpw1 (synCncs))
      (synCuni (synCuni (synCuni (synCuni (.cv q)))))
  have p0029 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCpw1 (synCpw1 (synCncs))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
          (synCpw1 (synCncs))) (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      p0027 p0028
  have p0030 :=
    @gSimpl
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
        (synCpw1 (synCncs)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
  have p0031 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
          (synCpw1 (synCncs))) (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
        (synCpw1 (synCncs)))
      p0029 p0030
  have p0032 :=
    @gPw1argclcl (synCncs)
      (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
  have p0033 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
        (synCpw1 (synCncs)))
      (synWa (.classMem
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))) (synCncs))
        (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      p0031 p0032
  have p0034 :=
    @gSimpl
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
  have p0035 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))) (synCncs))
        (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      p0033 p0034
  have p0036 :=
    @gElncs z (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
      dv_cache_0004
  have p0037 :=
    @gBiimpi
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      (synWex z (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      p0036
  have p0038 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      (synWex z (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      p0035 p0037
  have p0039 :=
    @gSyl
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWex z (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      p0010 p0038
  have p0040 :=
    @gSimpl
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCnc (.cv z)))
  have p0041 :=
    @gSimpr
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))
  have p0042 :=
    @gEqcomd
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (synCfv (synCwppcardt6fn) (.cv q)) (.cv x) p0041
  have p0047 :=
    @gSimpr
      (.classMem (synCuni (.cv q))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0048 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (.cv q))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0013 p0047
  have p0056 :=
    @gSimpr
      (.classMem (synCuni (synCuni (.cv q)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q)))))
  have p0057 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (.cv q)))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
        (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))))
      (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))) p0017 p0056
  have p0069 :=
    @gSimpr
      (.classMem (synCuni (synCuni (synCuni (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classEq (synCuni (synCuni (.cv q)))
        (synCsn (synCuni (synCuni (synCuni (.cv q))))))
  have p0070 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (.cv q))))
          (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (.classEq (synCuni (synCuni (.cv q)))
          (synCsn (synCuni (synCuni (synCuni (.cv q)))))))
      (.classEq (synCuni (synCuni (.cv q)))
        (synCsn (synCuni (synCuni (synCuni (.cv q))))))
      p0021 p0069
  have p0086 :=
    @gSimpr
      (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCpw1 (synCpw1 (synCncs))))
      (.classEq (synCuni (synCuni (synCuni (.cv q))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
  have p0087 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCpw1 (synCpw1 (synCncs)))) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
      (.classEq (synCuni (synCuni (synCuni (.cv q))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
      p0025 p0086
  have p0107 :=
    @gSimpr
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
        (synCpw1 (synCncs)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
  have p0108 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
          (synCpw1 (synCncs))) (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
          (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
        (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
      p0029 p0107
  have p0132 :=
    @gSimpr
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
  have p0133 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (.classMem
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))) (synCncs))
        (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      p0033 p0132
  have p0134 :=
    @gSneq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))
      (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
  have p0135 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      (.classEq (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCsn (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      p0133 p0134
  have p0136 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synCuni (synCuni (synCuni (synCuni (.cv q)))))
      (synCsn (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
      (synCsn (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      p0108 p0135
  have p0137 :=
    @gSneq (synCuni (synCuni (synCuni (synCuni (.cv q)))))
      (synCsn (synCsn
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
  have p0138 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCuni (synCuni (synCuni (synCuni (.cv q))))) (synCsn (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      (.classEq (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q)))))) (synCsn (synCsn
            (synCsn (synCuni
                (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
      p0136 p0137
  have p0139 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synCuni (synCuni (synCuni (.cv q))))
      (synCsn (synCuni (synCuni (synCuni (synCuni (.cv q))))))
      (synCsn (synCsn (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      p0087 p0138
  have p0140 :=
    @gSneq (synCuni (synCuni (synCuni (.cv q))))
      (synCsn (synCsn (synCsn
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
  have p0141 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCuni (synCuni (synCuni (.cv q)))) (synCsn (synCsn (synCsn (synCuni
                (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
      (.classEq (synCsn (synCuni (synCuni (synCuni (.cv q))))) (synCsn (synCsn (synCsn
              (synCsn (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
      p0139 p0140
  have p0142 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synCuni (synCuni (.cv q))) (synCsn (synCuni (synCuni (synCuni (.cv q)))))
      (synCsn (synCsn (synCsn (synCsn (synCuni
                (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
      p0070 p0141
  have p0143 :=
    @gSneq (synCuni (synCuni (.cv q)))
      (synCsn (synCsn (synCsn (synCsn (synCuni
                (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
  have p0144 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCuni (synCuni (.cv q))) (synCsn (synCsn (synCsn (synCsn (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
      (.classEq (synCsn (synCuni (synCuni (.cv q)))) (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      p0142 p0143
  have p0145 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
      p0057 p0144
  have p0146 :=
    @gSneq (synCuni (.cv q))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
  have p0147 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCuni (.cv q)) (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      (.classEq (synCsn (synCuni (.cv q))) (synCsn (synCsn (synCsn (synCsn (synCsn
                  (synCsn (synCuni (synCuni
                        (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      p0145 p0146
  have p0148 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.cv q) (synCsn (synCuni (.cv q)))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      p0048 p0147
  have p0149 :=
    @gFveq2 (.cv q)
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      (synCwppcardt6fn)
  have p0150 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (.cv q) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni
                      (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (synCfv (synCwppcardt6fn) (synCsn
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCuni (synCuni
                          (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))))
      p0148 p0149
  have p0176 :=
    @gWppcardt6fnvalsingndv
      (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
  have p0177 :=
    @gSyl
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCncs))
      (.classEq (synCfv (synCwppcardt6fn) (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCuni (synCuni
                          (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni (synCuni
                        (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      p0035 p0176
  have p0178 :=
    @gEqtrd
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synCfv (synCwppcardt6fn) (.cv q))
      (synCfv (synCwppcardt6fn) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCuni (synCuni
                        (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      p0150 p0177
  have p0179 :=
    @gSyl
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCuni (synCuni
                        (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      p0010 p0178
  have p0180 :=
    @gEqtrd
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.cv x) (synCfv (synCwppcardt6fn) (.cv q))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      p0042 p0179
  have p0181 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (.cv x) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                      (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))))
      p0040 p0180
  have p0182 :=
    @gSimpr
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCnc (.cv z)))
  have p0183 :=
    @gTceq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
      (synCnc (.cv z))
  have p0184 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCnc (.cv z)))
      (.classEq (synCtc
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
        (synCtc (synCnc (.cv z))))
      p0182 p0183
  have p0185 :=
    @gTceq
      (synCtc (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
      (synCtc (synCnc (.cv z)))
  have p0186 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCtc
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))
        (synCtc (synCnc (.cv z))))
      (.classEq (synCtc (synCtc
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
        (synCtc (synCtc (synCnc (.cv z)))))
      p0184 p0185
  have p0187 :=
    @gTceq
      (synCtc (synCtc
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
      (synCtc (synCtc (synCnc (.cv z))))
  have p0188 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCtc (synCtc
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))
        (synCtc (synCtc (synCnc (.cv z)))))
      (.classEq (synCtc (synCtc (synCtc
              (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
        (synCtc (synCtc (synCtc (synCnc (.cv z))))))
      p0186 p0187
  have p0189 :=
    @gTceq
      (synCtc (synCtc (synCtc
            (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
      (synCtc (synCtc (synCtc (synCnc (.cv z)))))
  have p0190 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc
              (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))
        (synCtc (synCtc (synCtc (synCnc (.cv z))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
      p0188 p0189
  have p0191 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCuni
                (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))
  have p0192 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      p0190 p0191
  have p0193 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                  (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
  have p0194 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q))))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni (synCuni
                        (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0192 p0193
  have p0195 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv q)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
          (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))) (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (.cv x)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCuni
                    (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))) p0181
      p0194
  have p0196 :=
    @gEx
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCnc (.cv z)))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0195
  have p0197 :=
    @gEximdv
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (.classEq (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
        (synCnc (.cv z)))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      z dv_cache_0005 p0196
  have p0198 :=
    @gMpd
      (synWa (.classMem (.cv q)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (synWex z (.classEq
          (synCuni (synCuni (synCuni (synCuni (synCuni (synCuni (.cv q)))))))
          (synCnc (.cv z))))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0039 p0197
  have p0199 :=
    @gEx
      (.classMem (.cv q)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0198
  have p0200 :=
    @gRexlimiv (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      q (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      dv_cache_0006 p0199
  have p0201 :=
    @gSyl (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (synWrex q (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (.classEq (synCfv (synCwppcardt6fn) (.cv q)) (.cv x)))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0009 p0200
  exact p0201


end NFChoice.DirectNominalPrf.WPPReplay

end
