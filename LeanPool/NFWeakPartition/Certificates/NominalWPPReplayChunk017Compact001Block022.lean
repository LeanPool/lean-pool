/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk017Compact001Part090

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part091`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbwpphwcncarrierinjndv (C : Class) (k : Var) (X : Class)
    (dv_C_k : k ∉ C.fv) (dv_X_k : k ∉ X.fv)
    (hyp_cfbwpphwcncarrierinjndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbwpphwcncarrierinjndv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X))))
    (hyp_cfbwpphwcncarrierinjndv_3 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wex k
          (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
            (syn_cpw (syn_cpw (syn_chnord X)))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ ({ k } : Finset Var) ∪ X.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_r : k ≠ r := Ne.symm fresh_r_ne_k
  have fresh_r_not_X : r ∉ X.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 :
    k ∉
      ((syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
          (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_r, dv_C_k, fresh_k_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((Class.cv a)).fv ((Class.cv r)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv a)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (a),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (r)];
          exact
            (show Disjoint (({ a } : Finset Var)) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show a ∉ ({ r } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show a ≠ r from (by exact fresh_a_ne_r))))))))
  have dv_cache_0003 : Disjoint ((Class.cv a)).fv (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((Class.cv a)).fv (X).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ a } : Finset Var)) ((X).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show a ∉ (X).fv from (by exact fresh_a_not_X))))))
  have dv_cache_0004 : k ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_a, not_false_eq_true])
  have dv_cache_0005 : Disjoint ((Class.cv r)).fv (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint ((Class.cv r)).fv (X).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ r } : Finset Var)) ((X).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show r ∉ (X).fv from (by exact fresh_r_not_X))))))
  have dv_cache_0006 : k ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_r, not_false_eq_true])
  have dv_cache_0007 : k ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_k, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_cfv (syn_c1st) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_r_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cfv (syn_c1st) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_a_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_cfv (syn_c2nd) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_r_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cfv (syn_c2nd) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_a_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    r ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
            (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k
              (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
                (syn_cpw (syn_cpw (syn_chnord X)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_X,
          fresh_r_ne_k, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    a ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
            (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k
              (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
                (syn_cpw (syn_cpw (syn_chnord X)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_C, fresh_a_not_X,
          fresh_a_ne_k, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 := @g_hwcnweclndv (syn_cpw X) C
  have p0001 := @g_hwcnbaseclndv (syn_cpw X) C
  have p0002 :=
    @g_jca (.classMem C (syn_chwcn (syn_cpw X)))
      (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
      (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X)) p0000 p0001
  have p0003 := Nominal.mp hyp_cfbwpphwcncarrierinjndv_2 p0002
  have p0004 := @g_fvex C (syn_c1st)
  have p0005 := @g_fvex C (syn_c2nd)
  have p0006 :=
    @g_simpl (.classEq (.cv r) (syn_cfv (syn_c1st) C))
      (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0007 :=
    @g_simpr (.classEq (.cv r) (syn_cfv (syn_c1st) C))
      (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0008 :=
    @g_breq12d
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.cv r) (syn_cfv (syn_c1st) C) (.cv a) (syn_cfv (syn_c2nd) C) (syn_cwe) p0006 p0007
  have p0010 :=
    @g_sseq1d
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.cv a) (syn_cfv (syn_c2nd) C) (syn_cpw X) p0007
  have p0011 :=
    @g_anbi12d
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (syn_wbr (.cv r) (syn_cwe) (.cv a))
      (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
      (syn_wss (.cv a) (syn_cpw X)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X)) p0008
      p0010
  have p0013 := @g_pw1eq (.cv a) (syn_cfv (syn_c2nd) C)
  have p0014 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
      (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C))) p0007 p0013
  have p0015 := @g_pw1eq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C))
  have p0016 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C)))
      (.classEq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
      p0014 p0015
  have p0017 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))
  have p0018 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.classEq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
      p0016 p0017
  have p0019 :=
    @g_f1eq2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
      (syn_cpw (syn_cpw (syn_chnord X))) (.cv k)
  have p0020 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
      (syn_wb (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
          (syn_cpw (syn_cpw (syn_chnord X))))
        (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      p0018 p0019
  have p0021 :=
    @g_exbidv
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      k dv_cache_0001 p0020
  have p0022 :=
    @g_imbi2d
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wwpp) p0021
  have p0023 :=
    @g_imbi12d
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C))
        (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv a)) (syn_wss (.cv a) (syn_cpw X)))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
        (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X)))
      (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      (.imp (syn_wwpp) (syn_wex k
          (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      p0011 p0022
  have p0024 := @g_vex r
  have p0025 := @g_vex a
  have p0026 :=
    @g_cfbfdwppcarrierimpndv (.cv a) (.cv r) k X dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0024 p0025 hyp_cfbwpphwcncarrierinjndv_1
      hyp_cfbwpphwcncarrierinjndv_3
  have p0027 :=
    @g_vtocl2
      (.imp (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv a)) (syn_wss (.cv a) (syn_cpw X)))
        (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C))
          (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k
            (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      r a (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0004 p0005
      p0023 p0026
  have p0028 := Nominal.mp p0003 p0027
  exact p0028

@[expose]
noncomputable def g_cfbhnpw13genericraisedcodendv (C : Class) (X : Class)
    (_hyp_cfbhnpw13genericraisedcodendv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbhnpw13genericraisedcodendv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X)))) :
    Nominal.NPrf
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classEq
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))) :=
  by
  have p0000 := @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0001 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X))))
      (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0000
  have p0002 := @g_hnsicodemapfndv (syn_cpw X)
  have p0003 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X)))
      (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
      (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0006 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
        (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
        (syn_chwcn (syn_cpw1 (syn_cpw X))))
      p0004 p0005
  have p0007 := @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0008 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))
      (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
      (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0007
  have p0009 := Nominal.mp p0006 p0008
  have p0010 :=
    @g_snelpw1
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0011 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      p0009 p0010
  have p0012 := @g_hnsicodemapfndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
  have p0013 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0012
  have p0014 := Nominal.mp p0011 p0013
  have p0027 :=
    @g_hnsicodemapvalclndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
      (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
  have p0028 := Nominal.mp p0011 p0027
  have p0029 :=
    @g_fveq2i
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1
          (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))))
      (syn_c2nd) p0028
  have p0030 :=
    @g_fvex
      (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_c1st)
  have p0031 :=
    @g_siex
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      p0030
  have p0032 :=
    @g_fvex
      (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_c2nd)
  have p0033 :=
    @g_pw1ex
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      p0032
  have p0034 :=
    @g_opfv2nd
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
      p0031 p0033
  have p0035 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn
                  (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                    (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
                  (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                    (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
      p0029 p0034
  have p0046 :=
    @g_elex
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0047 := Nominal.mp p0009 p0046
  have p0048 :=
    @g_unisn
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      p0047
  have p0049 :=
    @g_fveq2i
      (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_c2nd) p0048
  have p0050 :=
    @g_pw1eq
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      p0035 p0051
  have p0060 :=
    @g_hnsicodemapvalclndv (syn_cpw1 (syn_cpw X))
      (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
  have p0061 := Nominal.mp p0006 p0060
  have p0062 :=
    @g_fveq2i
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_c2nd) p0061
  have p0063 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_c1st)
  have p0064 :=
    @g_siex
      (syn_cfv (syn_c1st)
        (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      p0063
  have p0065 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_c2nd)
  have p0066 :=
    @g_pw1ex
      (syn_cfv (syn_c2nd)
        (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      p0065
  have p0067 :=
    @g_opfv2nd
      (syn_csi (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cpw1 (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      p0064 p0066
  have p0068 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st)
              (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))
      (syn_cpw1 (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      p0062 p0067
  have p0074 :=
    @g_elex (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
      (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0075 := Nominal.mp p0004 p0074
  have p0076 := @g_unisn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0075
  have p0077 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_c2nd) p0076
  have p0078 :=
    @g_pw1eq
      (syn_cfv (syn_c2nd)
        (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_cpw1 (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      p0068 p0079
  have p0081 :=
    @g_pw1eq
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
  have p0082 := Nominal.mp p0080 p0081
  have p0083 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cpw1 (syn_cpw1
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      p0052 p0082
  have p0086 := @g_hnsicodemapvalclndv (syn_cpw X) (syn_csn C)
  have p0087 := Nominal.mp p0001 p0086
  have p0088 :=
    @g_fveq2i (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))))
      (syn_c2nd) p0087
  have p0089 := @g_fvex (syn_cuni (syn_csn C)) (syn_c1st)
  have p0090 := @g_siex (syn_cfv (syn_c1st) (syn_cuni (syn_csn C))) p0089
  have p0091 := @g_fvex (syn_cuni (syn_csn C)) (syn_c2nd)
  have p0092 := @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))) p0091
  have p0093 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))) p0090 p0092
  have p0094 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))) p0088 p0093
  have p0095 := @g_elex C (syn_chwcn (syn_cpw X))
  have p0096 := Nominal.mp hyp_cfbhnpw13genericraisedcodendv_2 p0095
  have p0097 := @g_unisn C p0096
  have p0098 := @g_fveq2i (syn_cuni (syn_csn C)) C (syn_c2nd) p0097
  have p0099 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))) (syn_cfv (syn_c2nd) C)
  have p0100 := Nominal.mp p0098 p0099
  have p0101 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))))
      (syn_cpw1 (syn_cfv (syn_c2nd) C)) p0094 p0100
  have p0102 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
      (syn_cpw1 (syn_cfv (syn_c2nd) C))
  have p0103 := Nominal.mp p0101 p0102
  have p0104 :=
    @g_pw1eq
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))
  have p0105 := Nominal.mp p0103 p0104
  have p0106 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cpw1 (syn_cpw1
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) p0083 p0105
  have p0107 :=
    @g_pm3_2i
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
      p0014 p0106
  exact p0107


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part092`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnpw13genericquotrepcohndv (C : Class) (Q : Class) (X : Class)
    (hyp_cfbhnpw13genericquotrepcohndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbhnpw13genericquotrepcohndv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X))))
    (hyp_cfbhnpw13genericquotrepcohndv_3 : Nominal.NPrf
        (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))))
    (hyp_cfbhnpw13genericquotrepcohndv_4 : Nominal.NPrf
        (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) :=
  by
  have p0000 := @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0001 := @g_pw1ex (syn_cpw X) p0000
  have p0002 := @g_hnsiquomapfndv (syn_cpw1 (syn_cpw X)) p0001
  have p0003 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
  have p0004 := Nominal.mp p0002 p0003
  have p0006 := @g_hnsiquomapfndv (syn_cpw X) p0000
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X)))
      (syn_chnsiquomap (syn_cpw X))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))
      (syn_csi (syn_chnsiquomap (syn_cpw X)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_pm3_2i
      (syn_wf (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (syn_wf (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))))
      p0004 p0010
  have p0012 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
      (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i
      (syn_wf (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0013
      hyp_cfbhnpw13genericquotrepcohndv_3
  have p0015 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))) Q
      (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
        (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 :=
    @g_pm3_2i
      (syn_wf (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))))
      (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0010
      hyp_cfbhnpw13genericquotrepcohndv_3
  have p0024 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) Q
      (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
      (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0027 := Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0026
  have p0028 :=
    @g_simpr (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (.classEq Q (syn_csn (syn_cuni Q)))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_fveq2i Q (syn_csn (syn_cuni Q)) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
      p0029
  have p0037 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (.classEq Q (syn_csn (syn_cuni Q)))
  have p0038 := Nominal.mp p0027 p0037
  have p0039 :=
    @g_pm3_2i
      (syn_wf (syn_csi (syn_chnsiquomap (syn_cpw X)))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
      (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0008 p0038
  have p0040 :=
    @g_sifvalimpclndv (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))
      (syn_csi (syn_chnsiquomap (syn_cpw X)))
  have p0041 := Nominal.mp p0039 p0040
  have p0046 := @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0047 := Nominal.mp p0038 p0046
  have p0048 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @g_fveq2i (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q)))
      (syn_csi (syn_chnsiquomap (syn_cpw X))) p0049
  have p0059 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0060 := Nominal.mp p0047 p0059
  have p0061 :=
    @g_pm3_2i
      (syn_wf (syn_chnsiquomap (syn_cpw X)) (syn_cpw1 (syn_chnord (syn_cpw X)))
        (syn_chnord (syn_cpw1 (syn_cpw X))))
      (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) p0006 p0060
  have p0062 :=
    @g_sifvalimpclndv (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))
      (syn_chnord (syn_cpw1 (syn_cpw X))) (syn_chnsiquomap (syn_cpw X))
  have p0063 := Nominal.mp p0061 p0062
  have p0064 :=
    @g_eqtri (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q))
      (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_csn (syn_cuni (syn_cuni Q))))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0050
      p0063
  have p0065 :=
    @g_sneqi (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0064
  have p0066 :=
    @g_eqtri
      (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_csn (syn_cuni Q)))
      (syn_csn (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q)))
      (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      p0041 p0065
  have p0067 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q)
      (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_csn (syn_cuni Q)))
      (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      p0030 p0066
  have p0068 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q)
      (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) p0067
  have p0080 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X)))
      (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))
      hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0081 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q)))
          (syn_cec C (syn_chwniso (syn_cpw X)))))
      p0060 p0080
  have p0083 := @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0000
  have p0084 := Nominal.mp p0081 p0083
  have p0085 := @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0086 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X))))
      (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0085
  have p0087 := @g_hnsicodemapfndv (syn_cpw X)
  have p0088 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X)))
      (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0087
  have p0089 := Nominal.mp p0086 p0088
  have p0092 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X))
      (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0001
  have p0093 := Nominal.mp p0089 p0092
  have p0094 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
        (syn_chwniso (syn_cpw1 (syn_cpw X))))
      (syn_chnord (syn_cpw1 (syn_cpw X))) p0084 p0093
  have p0095 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))
      (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0096 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
      (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))
        (syn_chnord (syn_cpw1 (syn_cpw X))))
      p0094 p0095
  have p0097 :=
    @g_pm3_2i
      (syn_wf (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
      p0002 p0096
  have p0098 :=
    @g_sifvalimpclndv
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @g_eqtri
      (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
        (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q))
      (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csn
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
      p0068 p0099
  have p0101 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q)
      (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
        (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
      p0025 p0100
  have p0102 :=
    @g_fveq2i
      (syn_cfv (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q)
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
      (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0101
  have p0103 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cfv
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q))
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
          (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))))
      p0016 p0102
  have p0157 :=
    @g_elex (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))
      (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0158 := Nominal.mp p0094 p0157
  have p0159 :=
    @g_unisn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) p0158
  have p0173 :=
    @g_eqtri
      (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
        (syn_chwniso (syn_cpw1 (syn_cpw X))))
      p0159 p0084
  have p0174 :=
    @g_pm3_2i
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
        (syn_chwcn (syn_cpw1 (syn_cpw X))))
      (.classEq (syn_cuni
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
        (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
          (syn_chwniso (syn_cpw1 (syn_cpw X)))))
      p0089 p0173
  have p0175 :=
    @g_pm3_2i
      (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
          (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
          (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
            (syn_chwniso (syn_cpw1 (syn_cpw X))))))
      p0096 p0174
  have p0178 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw X))
      (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0001
  have p0179 := Nominal.mp p0175 p0178
  have p0185 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
      (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0186 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
        (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))
        (syn_chwcn (syn_cpw1 (syn_cpw X))))
      p0089 p0185
  have p0187 := @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0188 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))
      (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
      (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0187
  have p0189 := Nominal.mp p0186 p0188
  have p0192 := @g_pw1ex (syn_cpw1 (syn_cpw X)) p0001
  have p0193 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw1 (syn_cpw X)))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      p0192
  have p0194 := Nominal.mp p0189 p0193
  have p0195 :=
    @g_eqeltri
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0179 p0194
  have p0196 :=
    @g_snelpw1
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0197 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      p0195 p0196
  have p0300 :=
    @g_elex
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0301 := Nominal.mp p0195 p0300
  have p0302 :=
    @g_unisn
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      p0301
  have p0379 :=
    @g_eqtri
      (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))))
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      p0302 p0179
  have p0380 :=
    @g_pm3_2i
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))))
        (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      p0189 p0379
  have p0381 :=
    @g_pm3_2i
      (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (.classEq (syn_cuni (syn_csn
              (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn
                  (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X)))))))
      p0197 p0380
  have p0385 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
        (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
      (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
          (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))
      p0192
  have p0386 := Nominal.mp p0381 p0385
  have p0387 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)
      (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
          (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      p0103 p0386
  exact p0387


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part093`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnpw13genericcodepointcoverndv (C : Class) (Q : Class) (X : Class)
    (hyp_cfbhnpw13genericcodepointcoverndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbhnpw13genericcodepointcoverndv_2 :
      Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X))))
    (hyp_cfbhnpw13genericcodepointcoverndv_3 : Nominal.NPrf
        (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))))
    (hyp_cfbhnpw13genericcodepointcoverndv_4 : Nominal.NPrf
        (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))))
    (hyp_cfbhnpw13genericcodepointcoverndv_5 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ Q.fv ∪ X.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_X : k ∉ X.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0002 : k ∉ (X).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_X, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_k_not_X,
          not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_cpw (syn_cpw (syn_chnord X)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_k_not_X,
          not_false_eq_true])
  have dv_cache_0005 :
    k ∉
      ((Wff.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
                  (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                    (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
              (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_X, or_false, not_false_eq_true])
  have p0000 :=
    @g_cfbwpphwcncarrierinjndv C k X dv_cache_0001 dv_cache_0002
      hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2
      hyp_cfbhnpw13genericcodepointcoverndv_5
  have p0001 :=
    @g_cfbhnpw13genericraisedcodendv C X hyp_cfbhnpw13genericcodepointcoverndv_1
      hyp_cfbhnpw13genericcodepointcoverndv_2
  have p0002 :=
    @g_simpr
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_f1eq2
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
      (syn_cpw (syn_cpw (syn_chnord X))) (.cv k)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_biimpri
      (syn_wf1 (.cv k) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      p0005
  have p0007 := @g_pwex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0008 := @g_pw1ex (syn_cpw X) p0007
  have p0009 := @g_pw1ex (syn_cpw1 (syn_cpw X)) p0008
  have p0010 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0009
  have p0011 := @g_hnordex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0012 := @g_pwex (syn_chnord X) p0011
  have p0013 := @g_pwex (syn_cpw (syn_chnord X)) p0012
  have p0015 :=
    @g_simpl
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
  have p0016 := Nominal.mp p0001 p0015
  have p0017 :=
    @g_cfbhnqinjcodecoverdclndv
      (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
            (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) k (syn_cpw (syn_cpw (syn_chnord X)))
      dv_cache_0003 dv_cache_0004 p0010 p0013 p0016
  have p0018 :=
    @g_syl
      (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv k) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0006 p0017
  have p0019 :=
    @g_exlimiv
      (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
        (syn_cpw (syn_cpw (syn_chnord X))))
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      k dv_cache_0005 p0018
  have p0020 :=
    @g_syl (syn_wwpp)
      (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0000 p0019
  have p0021 :=
    @g_cfbhnpw13genericquotrepcohndv C Q X hyp_cfbhnpw13genericcodepointcoverndv_1
      hyp_cfbhnpw13genericcodepointcoverndv_2 hyp_cfbhnpw13genericcodepointcoverndv_3
      hyp_cfbhnpw13genericcodepointcoverndv_4
  have p0022 :=
    @g_eqcomi
      (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      p0021
  have p0023 :=
    @g_fveq2i
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
              (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)
      (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      p0022
  have p0024 :=
    @g_eleq1i
      (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
              (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))))
      (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q))
      (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      p0023
  have p0025 :=
    @g_sylib (syn_wwpp)
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn
                (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X)))
                  (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0020 p0024
  have p0027 := @g_hnpw13quoshiftf1ondv (syn_cpw X) p0007
  have p0028 :=
    @g_f1of (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_pm3_2i
      (syn_wf (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0029
      hyp_cfbhnpw13genericcodepointcoverndv_3
  have p0031 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) Q
      (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_eleq1i
      (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q)
      (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q))
      (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      p0032
  have p0034 :=
    @g_sylibr (syn_wwpp)
      (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0025 p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part094`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnpw13pointcoverndv (X : Class) (q : Var)
    (hyp_cfbhnpw13pointcoverndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbhnpw13pointcoverndv_2 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
                (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X))))))))) :=
  by
  let proofSupport : Finset Var := X.fv ∪ ({ q } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ ((syn_cpw X)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_u_not_X,
          not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cuni (syn_cuni (syn_cuni (.cv q))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.classEq (.cv q) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_X, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 :
    u ∉
      ((Wff.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
                (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
                (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
                (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_X, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) (.cv q)
  have p0001 :=
    @g_simpld
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0000
  have p0002 := @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni (.cv q))
  have p0003 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_chnord (syn_cpw X))))
        (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0001 p0002
  have p0004 :=
    @g_simpld
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0003
  have p0005 := @g_pw1argclcl (syn_chnord (syn_cpw X)) (syn_cuni (syn_cuni (.cv q)))
  have p0006 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X)))
        (.classEq (syn_cuni (syn_cuni (.cv q)))
          (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @g_simpld
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X)))
      (.classEq (syn_cuni (syn_cuni (.cv q)))
        (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
      p0006
  have p0016 := @g_elex (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X))
  have p0017 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X)))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cvv)) p0007 p0016
  have p0018 :=
    @g_elhnordclndv u (syn_cpw X) (syn_cuni (syn_cuni (syn_cuni (.cv q)))) dv_cache_0001
      dv_cache_0002
  have p0019 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cvv))
      (syn_wb (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X)))
        (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
            (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))))
      p0017 p0018
  have p0020 :=
    @g_mpbid (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_chnord (syn_cpw X)))
      (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))))
      p0007 p0019
  have p0021 :=
    @g_id
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
  have p0022 :=
    @g_unieqd
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (.cv q)
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      p0021
  have p0023 :=
    @g_unieqd
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (.cv q))
      (syn_cuni (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      p0022
  have p0024 :=
    @g_unieqd
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (syn_cuni (.cv q)))
      (syn_cuni (syn_cuni (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X)))))))))
      p0023
  have p0025 :=
    @g_eqeq1d
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (syn_cuni (syn_cuni (.cv q))))
      (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
      (syn_cec (.cv u) (syn_chwniso (syn_cpw X))) p0024
  have p0026 :=
    @g_rexbidv
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
        (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
        (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))
      u (syn_chwcn (syn_cpw X)) dv_cache_0003 p0025
  have p0028 :=
    @g_fveq2d
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (.cv q)
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
      p0021
  have p0029 :=
    @g_eleq1d
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q))
      (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      p0028
  have p0030 :=
    @g_imbi2d
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X)))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (syn_wwpp) p0029
  have p0031 :=
    @g_imbi12d
      (.classEq (.cv q) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))))
      (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                  (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
                  (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
          (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
              (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
              (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      p0026 p0030
  have p0032 :=
    @g_eceq1 (.cv u)
      (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_chwniso (syn_cpw X))
  have p0033 :=
    @g_eqeq2d
      (.classEq (.cv u) (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
      p0032
  have p0034 :=
    @g_imbi1d
      (.classEq (.cv u) (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
        (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
              (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
              (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      p0033
  have p0035 :=
    @g_id
      (.classEq (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_cif (.classEq (syn_cuni
              (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
  have p0036 :=
    @g_fveq2d
      (.classEq (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_cif (.classEq (syn_cuni
              (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
      p0035
  have p0037 :=
    @g_eleq1d
      (.classEq (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_cif (.classEq (syn_cuni
              (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif (.classEq (syn_cuni
              (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      p0036
  have p0038 :=
    @g_imbi2d
      (.classEq (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_cif (.classEq (syn_cuni
              (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X)))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif (.classEq
              (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                      (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                                (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                  (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (syn_wwpp) p0037
  have p0039 := @g_eqid (syn_c0)
  have p0040 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem (.cv u) (syn_chwcn (syn_cpw X)))
  have p0041 := @g_hncodecmpdefaultcnndv (syn_cpw X)
  have p0042 :=
    @g_a1i
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn (syn_cpw X)))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem (.cv u) (syn_chwcn (syn_cpw X)))))
      p0041
  have p0043 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem (.cv u) (syn_chwcn (syn_cpw X)))
      (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn (syn_cpw X)) p0040 p0042
  have p0044 := Nominal.mp p0039 p0043
  have p0046 :=
    @g_simpr (.classEq (syn_c0) (syn_c0))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
  have p0048 := @g_pwex X hyp_cfbhnpw13pointcoverndv_1
  have p0049 :=
    @g_hwnisoclasselhnordcl (syn_cpw X)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      p0048
  have p0050 := Nominal.mp p0041 p0049
  have p0051 :=
    @g_snelpw1
      (syn_cec
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwniso (syn_cpw X)))
      (syn_chnord (syn_cpw X))
  have p0052 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cec
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
            (syn_chwniso (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (.classMem (syn_cec
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
          (syn_chwniso (syn_cpw X))) (syn_chnord (syn_cpw X)))
      p0050 p0051
  have p0053 :=
    @g_snelpw1
      (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)) (syn_chwniso (syn_cpw X))))
      (syn_cpw1 (syn_chnord (syn_cpw X)))
  have p0054 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_cec
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
              (syn_chwniso (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (.classMem (syn_csn (syn_cec
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
            (syn_chwniso (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      p0052 p0053
  have p0055 :=
    @g_snelpw1
      (syn_csn (syn_csn (syn_cec
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
            (syn_chwniso (syn_cpw X)))))
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))
  have p0056 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_csn (syn_csn (syn_cec
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
              (syn_chwniso (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      p0054 p0055
  have p0057 :=
    @g_a1i
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))))
      p0056
  have p0058 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.cv q)
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
              (syn_chwniso (syn_cpw X))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0046 p0057
  have p0059 := Nominal.mp p0039 p0058
  have p0067 :=
    @g_hwnisoclasselhnordcl (syn_cpw X)
      (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      p0048
  have p0068 := Nominal.mp p0044 p0067
  have p0069 :=
    @g_snelpw1
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      (syn_chnord (syn_cpw X))
  have p0070 :=
    @g_mpbir
      (.classMem (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      (.classMem (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))) (syn_chnord (syn_cpw X)))
      p0068 p0069
  have p0071 :=
    @g_snelpw1
      (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cpw1 (syn_chnord (syn_cpw X)))
  have p0072 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (.classMem (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw X))))
      p0070 p0071
  have p0073 :=
    @g_snelpw1
      (syn_csn (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))
  have p0074 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      p0072 p0073
  have p0075 :=
    @g_pm3_2i
      (.classMem (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      p0059 p0074
  have p0076 :=
    @g_ifcl
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
  have p0077 := Nominal.mp p0075 p0076
  have p0078 :=
    @g_iftrue
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
  have p0079 :=
    @g_unieqd
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      p0078
  have p0080 :=
    @g_unieqd
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))))
      p0079
  have p0081 :=
    @g_unieqd
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cuni (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                      (.classMem (.cv q)
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                      (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                                (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                  (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))))))))
      (syn_cuni (syn_cuni (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X)))))))))
      p0080
  have p0082 :=
    @g_id
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
  have p0083 :=
    @g_eqtrd
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                        (.classMem (.cv q)
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                        (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                  (syn_cin (syn_ckqrel (syn_clefin))
                                    (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                                (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                    (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0))) (syn_chwniso (syn_cpw X))))))))))
      (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      p0081 p0082
  have p0084 :=
    @g_iffalse
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
  have p0085 :=
    @g_unieqd
      (.neg (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
      p0084
  have p0086 :=
    @g_unieqd
      (.neg (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
            (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                    (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      p0085
  have p0087 :=
    @g_unieqd
      (.neg (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cuni (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                      (.classMem (.cv q)
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                      (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                                (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                  (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))))))))
      (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      p0086
  have p0088 :=
    @g_snex
      (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
  have p0089 :=
    @g_unisn
      (syn_csn (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      p0088
  have p0090 :=
    @g_unieqi
      (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      p0089
  have p0091 :=
    @g_snex
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
  have p0092 :=
    @g_unisn
      (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      p0091
  have p0093 :=
    @g_eqtri
      (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_cuni (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
      (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      p0090 p0092
  have p0094 :=
    @g_unieqi
      (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X))))))))
      (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      p0093
  have p0104 :=
    @g_elex
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      (syn_chnord (syn_cpw X))
  have p0105 := Nominal.mp p0068 p0104
  have p0106 :=
    @g_unisn
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      p0105
  have p0107 :=
    @g_eqtri
      (syn_cuni (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                    (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))))))))
      (syn_cuni (syn_csn (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      p0094 p0106
  have p0108 :=
    @g_a1i
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                      (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0))) (syn_chwniso (syn_cpw X))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (.neg (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      p0107
  have p0109 :=
    @g_eqtrd
      (.neg (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))))
      (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                        (.classMem (.cv q)
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                        (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                  (syn_cin (syn_ckqrel (syn_clefin))
                                    (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                                (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                    (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0))) (syn_chwniso (syn_cpw X))))))))))
      (syn_cuni (syn_cuni (syn_cuni (syn_csn (syn_csn (syn_csn (syn_cec
                    (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))))))))
      (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso (syn_cpw X)))
      p0087 p0108
  have p0110 :=
    @g_pm2_61i
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni
                        (syn_cif (.classMem (.cv q)
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                          (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                    (syn_cin (syn_ckqrel (syn_clefin))
                                      (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                                  (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                    (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                        (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0))) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      p0083 p0109
  have p0111 :=
    @g_cfbhnpw13genericcodepointcoverndv
      (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cif (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (syn_cif
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
          (syn_csn (syn_csn (syn_csn (syn_cec
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))) (syn_chwniso (syn_cpw X)))))))
      X hyp_cfbhnpw13pointcoverndv_1 p0044 p0077 p0110 hyp_cfbhnpw13pointcoverndv_2
  have p0112 :=
    @g_dedth
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))))) (syn_cec
          (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso (syn_cpw X))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
              (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
              (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif (.classEq
                (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                        (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                                  (syn_cin (syn_ckqrel (syn_clefin))
                                    (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                                (syn_chwniso (syn_cpw X)))))))))) (syn_cec
                  (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
                  (syn_chwniso (syn_cpw X)))) (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))) (syn_csn (syn_csn (syn_csn
                    (syn_cec (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0))) (syn_chwniso (syn_cpw X)))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)) (syn_chwniso (syn_cpw X)))))))
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))) (syn_chwniso (syn_cpw X))))))
      p0038 p0111
  have p0113 :=
    @g_dedth (.classMem (.cv u) (syn_chwcn (syn_cpw X)))
      (.imp (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X))))))))))
          (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))) (.imp (syn_wwpp) (.classMem (syn_cfv
              (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
                (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
                (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))))))
      (.imp (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                    (syn_csn (syn_csn (syn_cec (syn_cop (syn_cin (syn_ckqrel (syn_clefin))
                              (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
                          (syn_chwniso (syn_cpw X)))))))))) (syn_cec
            (syn_cif (.classMem (.cv u) (syn_chwcn (syn_cpw X))) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso (syn_cpw X)))) (.imp (syn_wwpp) (.classMem (syn_cfv
              (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
                (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
                (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))))))
      (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      p0034 p0112
  have p0114 :=
    @g_rexlimiv
      (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif (.classMem (.cv q)
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q) (syn_csn
                  (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
        (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
              (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
              (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      u (syn_chwcn (syn_cpw X)) dv_cache_0004 p0113
  have p0115 :=
    @g_dedth (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (.imp (syn_wrex u (syn_chwcn (syn_cpw X))
          (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
            (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))) (.imp (syn_wwpp) (.classMem (syn_cfv
              (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))))))
      (.imp (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cif
                    (.classMem (.cv q)
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (.cv q)
                    (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)) (syn_chwniso (syn_cpw X))))))))))
            (syn_cec (.cv u) (syn_chwniso (syn_cpw X))))) (.imp (syn_wwpp) (.classMem (syn_cfv
              (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cif
                (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
                (.cv q) (syn_csn (syn_csn (syn_csn (syn_cec (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)) (syn_chwniso (syn_cpw X)))))))) (syn_crn
              (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))))))
      (.cv q)
      (syn_csn (syn_csn (syn_csn (syn_cec
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
              (syn_chwniso (syn_cpw X))))))
      p0031 p0114
  have p0116 :=
    @g_mpd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (syn_wrex u (syn_chwcn (syn_cpw X)) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q))))
          (syn_cec (.cv u) (syn_chwniso (syn_cpw X)))))
      (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      p0020 p0115
  exact p0116


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part095`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbwppfixedblockhnqimagecoverndv (X : Class)
    (hyp_cfbwppfixedblockhnqimagecoverndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbwppfixedblockhnqimagecoverndv_2 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wss (syn_cima (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))))) :=
  by
  let proofSupport : Finset Var := X.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_X : q ∉ X.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ ((syn_wwpp)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    q ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_q_not_X,
          not_false_eq_true])
  have dv_cache_0003 :
    q ∉
      ((syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_q_not_X, or_false, not_false_eq_true])
  have dv_cache_0004 :
    q ∉
      ((syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          fresh_q_not_X, or_false, not_false_eq_true])
  have p0000 :=
    @g_cfbhnpw13pointcoverndv X q hyp_cfbwppfixedblockhnqimagecoverndv_1
      hyp_cfbwppfixedblockhnqimagecoverndv_2
  have p0001 :=
    @g_com12 (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (syn_wwpp)
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0000
  have p0002 :=
    @g_ralrimiv (syn_wwpp)
      (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) dv_cache_0001 p0001
  have p0003 :=
    @g_ssun1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_cpw (syn_cpw (syn_chnord X)))
  have p0004 := @g_pwexg X (syn_cvv)
  have p0005 := Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0004
  have p0006 := @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0020 := @g_hnordexg X
  have p0021 := Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0020
  have p0022 := @g_pwexg (syn_chnord X) (syn_cvv)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @g_pwexg (syn_cpw (syn_chnord X)) (syn_cvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_pm3_2i (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv)) p0011 p0025
  have p0027 :=
    @g_unexg (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv) (syn_cvv)
  have p0028 := Nominal.mp p0026 p0027
  have p0029 :=
    @g_hnqincfn
      (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0003 p0011 p0028
  have p0032 := @g_hnpw13quoshiftf1ondv (syn_cpw X) p0005
  have p0033 :=
    @g_f1of (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 :=
    @g_pm3_2i
      (syn_wfn (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      (syn_wf (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))
      p0029 p0034
  have p0036 :=
    @g_fnfco (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @g_fnfun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
  have p0039 := Nominal.mp p0037 p0038
  have p0075 :=
    @g_fndm (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
  have p0076 := Nominal.mp p0037 p0075
  have p0077 :=
    @g_eqcomi
      (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0076
  have p0078 :=
    @g_ssid
      (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
  have p0079 :=
    @g_eqsstri (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
      (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
      p0077 p0078
  have p0080 :=
    @g_pm3_2i
      (syn_wfun (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
      (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cdm (syn_ccom
            (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))))
      p0039 p0079
  have p0081 :=
    @g_funimass4 q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0082 := Nominal.mp p0080 p0081
  have p0083 :=
    @g_sylibr (syn_wwpp)
      (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classMem (syn_cfv
            (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn
            (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X))))))))
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      p0002 p0082
  exact p0083

@[expose]
noncomputable def g_cfbwppfixedblockhnqgraphinjndv (X : Class)
    (hyp_cfbwppfixedblockhnqgraphinjndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbwppfixedblockhnqgraphinjndv_2 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv
                (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
                (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))) :=
  by
  have p0000 :=
    @g_cfbwppfixedblockhnqimagecoverndv X hyp_cfbwppfixedblockhnqgraphinjndv_1
      hyp_cfbwppfixedblockhnqgraphinjndv_2
  have p0001 := @g_pwexg X (syn_cvv)
  have p0002 := Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0001
  have p0003 := @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_hnordexg X
  have p0010 := Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0009
  have p0011 := @g_pwexg (syn_chnord X) (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_pwexg (syn_cpw (syn_chnord X)) (syn_cvv)
  have p0014 := Nominal.mp p0012 p0013
  have p0017 := @g_hnpw13quoshiftf1ondv (syn_cpw X) p0002
  have p0018 :=
    @g_f1of1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_hnqcommonprecoverinjndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_cpw (syn_cpw (syn_chnord X)))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
      p0008 p0014 p0019
  have p0021 :=
    @g_syl (syn_wwpp)
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn
          (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))))
      (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))
      p0000 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end
