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

/-- Checked nominal proof certificate identified upstream as `g_cfbwpphwcncarrierinjndv`. -/
@[expose]
noncomputable def gCfbwpphwcncarrierinjndv (C : Class) (k : Var) (X : Class)
    (dv_C_k : k ∉ C.fv) (dv_X_k : k ∉ X.fv)
    (hyp_cfbwpphwcncarrierinjndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbwpphwcncarrierinjndv_2 : Nominal.NPrf (.classMem C (synChwcn (synCpw X))))
    (hyp_cfbwpphwcncarrierinjndv_3 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWex k
          (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
            (synCpw (synCpw (synChnord X)))))) :=
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
      ((synWa (.classEq (.cv r) (synCfv (synC1st) C))
          (.classEq (.cv a) (synCfv (synC2nd) C)))).fv :=
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
  have dv_cache_0008 : r ∉ ((synCfv (synC1st) C)).fv :=
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
  have dv_cache_0009 : a ∉ ((synCfv (synC1st) C)).fv :=
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
  have dv_cache_0010 : r ∉ ((synCfv (synC2nd) C)).fv :=
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
  have dv_cache_0011 : a ∉ ((synCfv (synC2nd) C)).fv :=
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
      ((Wff.imp (synWa (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
            (synWss (synCfv (synC2nd) C) (synCpw X))) (.imp (synWwpp) (synWex k
              (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
                (synCpw (synCpw (synChnord X)))))))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
            (synWss (synCfv (synC2nd) C) (synCpw X))) (.imp (synWwpp) (synWex k
              (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
                (synCpw (synCpw (synChnord X)))))))).fv :=
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
  have p0000 := @gHwcnweclndv (synCpw X) C
  have p0001 := @gHwcnbaseclndv (synCpw X) C
  have p0002 :=
    @gJca (.classMem C (synChwcn (synCpw X)))
      (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
      (synWss (synCfv (synC2nd) C) (synCpw X)) p0000 p0001
  have p0003 := Nominal.mp hyp_cfbwpphwcncarrierinjndv_2 p0002
  have p0004 := @gFvex C (synC1st)
  have p0005 := @gFvex C (synC2nd)
  have p0006 :=
    @gSimpl (.classEq (.cv r) (synCfv (synC1st) C))
      (.classEq (.cv a) (synCfv (synC2nd) C))
  have p0007 :=
    @gSimpr (.classEq (.cv r) (synCfv (synC1st) C))
      (.classEq (.cv a) (synCfv (synC2nd) C))
  have p0008 :=
    @gBreq12d
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.cv r) (synCfv (synC1st) C) (.cv a) (synCfv (synC2nd) C) (synCwe) p0006 p0007
  have p0010 :=
    @gSseq1d
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.cv a) (synCfv (synC2nd) C) (synCpw X) p0007
  have p0011 :=
    @gAnbi12d
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (synWbr (.cv r) (synCwe) (.cv a))
      (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
      (synWss (.cv a) (synCpw X)) (synWss (synCfv (synC2nd) C) (synCpw X)) p0008
      p0010
  have p0013 := @gPw1eq (.cv a) (synCfv (synC2nd) C)
  have p0014 :=
    @gSyl
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.classEq (.cv a) (synCfv (synC2nd) C))
      (.classEq (synCpw1 (.cv a)) (synCpw1 (synCfv (synC2nd) C))) p0007 p0013
  have p0015 := @gPw1eq (synCpw1 (.cv a)) (synCpw1 (synCfv (synC2nd) C))
  have p0016 :=
    @gSyl
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.classEq (synCpw1 (.cv a)) (synCpw1 (synCfv (synC2nd) C)))
      (.classEq (synCpw1 (synCpw1 (.cv a))) (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
      p0014 p0015
  have p0017 :=
    @gPw1eq (synCpw1 (synCpw1 (.cv a))) (synCpw1 (synCpw1 (synCfv (synC2nd) C)))
  have p0018 :=
    @gSyl
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.classEq (synCpw1 (synCpw1 (.cv a))) (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
      (.classEq (synCpw1 (synCpw1 (synCpw1 (.cv a))))
        (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))
      p0016 p0017
  have p0019 :=
    @gF1eq2 (synCpw1 (synCpw1 (synCpw1 (.cv a))))
      (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
      (synCpw (synCpw (synChnord X))) (.cv k)
  have p0020 :=
    @gSyl
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (.classEq (synCpw1 (synCpw1 (synCpw1 (.cv a))))
        (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))
      (synWb (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (.cv a))))
          (synCpw (synCpw (synChnord X))))
        (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
          (synCpw (synCpw (synChnord X)))))
      p0018 p0019
  have p0021 :=
    @gExbidv
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (.cv a))))
        (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
        (synCpw (synCpw (synChnord X))))
      k dv_cache_0001 p0020
  have p0022 :=
    @gImbi2d
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (.cv a))))
          (synCpw (synCpw (synChnord X)))))
      (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
          (synCpw (synCpw (synChnord X)))))
      (synWwpp) p0021
  have p0023 :=
    @gImbi12d
      (synWa (.classEq (.cv r) (synCfv (synC1st) C))
        (.classEq (.cv a) (synCfv (synC2nd) C)))
      (synWa (synWbr (.cv r) (synCwe) (.cv a)) (synWss (.cv a) (synCpw X)))
      (synWa (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
        (synWss (synCfv (synC2nd) C) (synCpw X)))
      (.imp (synWwpp) (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (.cv a))))
            (synCpw (synCpw (synChnord X))))))
      (.imp (synWwpp) (synWex k
          (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
            (synCpw (synCpw (synChnord X))))))
      p0011 p0022
  have p0024 := @gVex r
  have p0025 := @gVex a
  have p0026 :=
    @gCfbfdwppcarrierimpndv (.cv a) (.cv r) k X dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0024 p0025 hyp_cfbwpphwcncarrierinjndv_1
      hyp_cfbwpphwcncarrierinjndv_3
  have p0027 :=
    @gVtocl2
      (.imp (synWa (synWbr (.cv r) (synCwe) (.cv a)) (synWss (.cv a) (synCpw X)))
        (.imp (synWwpp) (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (.cv a))))
              (synCpw (synCpw (synChnord X)))))))
      (.imp (synWa (synWbr (synCfv (synC1st) C) (synCwe) (synCfv (synC2nd) C))
          (synWss (synCfv (synC2nd) C) (synCpw X))) (.imp (synWwpp) (synWex k
            (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
              (synCpw (synCpw (synChnord X)))))))
      r a (synCfv (synC1st) C) (synCfv (synC2nd) C) dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0004 p0005
      p0023 p0026
  have p0028 := Nominal.mp p0003 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_cfbhnpw13genericraisedcodendv`. -/
@[expose]
noncomputable def gCfbhnpw13genericraisedcodendv (C : Class) (X : Class)
    (_hyp_cfbhnpw13genericraisedcodendv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbhnpw13genericraisedcodendv_2 : Nominal.NPrf (.classMem C (synChwcn (synCpw X)))) :
    Nominal.NPrf
      (synWa (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
          (synChwcn (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))) (.classEq
          (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X))))
              (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))) :=
  by
  have p0000 := @gSnelpw1 C (synChwcn (synCpw X))
  have p0001 :=
    @gMpbir (.classMem (synCsn C) (synCpw1 (synChwcn (synCpw X))))
      (.classMem C (synChwcn (synCpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0000
  have p0002 := @gHnsicodemapfndv (synCpw X)
  have p0003 :=
    @gFfvelrni (synCpw1 (synChwcn (synCpw X))) (synChwcn (synCpw1 (synCpw X)))
      (synCsn C) (synChnsicodemap (synCpw X)) p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 :=
    @gSnelpw1 (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
      (synChwcn (synCpw1 (synCpw X)))
  have p0006 :=
    @gMpbir
      (.classMem (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
        (synCpw1 (synChwcn (synCpw1 (synCpw X)))))
      (.classMem (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
        (synChwcn (synCpw1 (synCpw X))))
      p0004 p0005
  have p0007 := @gHnsicodemapfndv (synCpw1 (synCpw X))
  have p0008 :=
    @gFfvelrni (synCpw1 (synChwcn (synCpw1 (synCpw X))))
      (synChwcn (synCpw1 (synCpw1 (synCpw X))))
      (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
      (synChnsicodemap (synCpw1 (synCpw X))) p0007
  have p0009 := Nominal.mp p0006 p0008
  have p0010 :=
    @gSnelpw1
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synChwcn (synCpw1 (synCpw1 (synCpw X))))
  have p0011 :=
    @gMpbir
      (.classMem (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
        (synCpw1 (synChwcn (synCpw1 (synCpw1 (synCpw X))))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
        (synChwcn (synCpw1 (synCpw1 (synCpw X)))))
      p0009 p0010
  have p0012 := @gHnsicodemapfndv (synCpw1 (synCpw1 (synCpw X)))
  have p0013 :=
    @gFfvelrni (synCpw1 (synChwcn (synCpw1 (synCpw1 (synCpw X)))))
      (synChwcn (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))
      (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) p0012
  have p0014 := Nominal.mp p0011 p0013
  have p0027 :=
    @gHnsicodemapvalclndv (synCpw1 (synCpw1 (synCpw X)))
      (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
  have p0028 := Nominal.mp p0011 p0027
  have p0029 :=
    @gFveq2i
      (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
          (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))) (synCpw1
          (synCfv (synC2nd) (synCuni (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))))
      (synC2nd) p0028
  have p0030 :=
    @gFvex
      (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synC1st)
  have p0031 :=
    @gSiex
      (synCfv (synC1st) (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      p0030
  have p0032 :=
    @gFvex
      (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synC2nd)
  have p0033 :=
    @gPw1ex
      (synCfv (synC2nd) (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      p0032
  have p0034 :=
    @gOpfv2nd
      (synCsi (synCfv (synC1st) (synCuni (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
      p0031 p0033
  have p0035 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn
                  (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                    (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
          (synCpw1 (synCfv (synC2nd) (synCuni (synCsn
                  (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                    (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
      p0029 p0034
  have p0046 :=
    @gElex
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synChwcn (synCpw1 (synCpw1 (synCpw X))))
  have p0047 := Nominal.mp p0009 p0046
  have p0048 :=
    @gUnisn
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      p0047
  have p0049 :=
    @gFveq2i
      (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synC2nd) p0048
  have p0050 :=
    @gPw1eq
      (synCfv (synC2nd) (synCuni (synCsn (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
      (synCpw1 (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      p0035 p0051
  have p0060 :=
    @gHnsicodemapvalclndv (synCpw1 (synCpw X))
      (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
  have p0061 := Nominal.mp p0006 p0060
  have p0062 :=
    @gFveq2i
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synCop (synCsi (synCfv (synC1st)
            (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synCpw1 (synCfv (synC2nd)
            (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synC2nd) p0061
  have p0063 :=
    @gFvex (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synC1st)
  have p0064 :=
    @gSiex
      (synCfv (synC1st)
        (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      p0063
  have p0065 :=
    @gFvex (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synC2nd)
  have p0066 :=
    @gPw1ex
      (synCfv (synC2nd)
        (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      p0065
  have p0067 :=
    @gOpfv2nd
      (synCsi (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCpw1 (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      p0064 p0066
  have p0068 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st)
              (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
          (synCpw1 (synCfv (synC2nd) (synCuni
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))))
      (synCpw1 (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      p0062 p0067
  have p0074 :=
    @gElex (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
      (synChwcn (synCpw1 (synCpw X)))
  have p0075 := Nominal.mp p0004 p0074
  have p0076 := @gUnisn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)) p0075
  have p0077 :=
    @gFveq2i (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synCfv (synChnsicodemap (synCpw X)) (synCsn C)) (synC2nd) p0076
  have p0078 :=
    @gPw1eq
      (synCfv (synC2nd)
        (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synCpw1 (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCpw1 (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      p0068 p0079
  have p0081 :=
    @gPw1eq
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synCpw1 (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
  have p0082 := Nominal.mp p0080 p0081
  have p0083 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCpw1 (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCpw1 (synCpw1
          (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      p0052 p0082
  have p0086 := @gHnsicodemapvalclndv (synCpw X) (synCsn C)
  have p0087 := Nominal.mp p0001 p0086
  have p0088 :=
    @gFveq2i (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
      (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn C))))
        (synCpw1 (synCfv (synC2nd) (synCuni (synCsn C)))))
      (synC2nd) p0087
  have p0089 := @gFvex (synCuni (synCsn C)) (synC1st)
  have p0090 := @gSiex (synCfv (synC1st) (synCuni (synCsn C))) p0089
  have p0091 := @gFvex (synCuni (synCsn C)) (synC2nd)
  have p0092 := @gPw1ex (synCfv (synC2nd) (synCuni (synCsn C))) p0091
  have p0093 :=
    @gOpfv2nd (synCsi (synCfv (synC1st) (synCuni (synCsn C))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn C)))) p0090 p0092
  have p0094 :=
    @gEqtri (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn C))))
          (synCpw1 (synCfv (synC2nd) (synCuni (synCsn C))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn C)))) p0088 p0093
  have p0095 := @gElex C (synChwcn (synCpw X))
  have p0096 := Nominal.mp hyp_cfbhnpw13genericraisedcodendv_2 p0095
  have p0097 := @gUnisn C p0096
  have p0098 := @gFveq2i (synCuni (synCsn C)) C (synC2nd) p0097
  have p0099 :=
    @gPw1eq (synCfv (synC2nd) (synCuni (synCsn C))) (synCfv (synC2nd) C)
  have p0100 := Nominal.mp p0098 p0099
  have p0101 :=
    @gEqtri (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn C))))
      (synCpw1 (synCfv (synC2nd) C)) p0094 p0100
  have p0102 :=
    @gPw1eq (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
      (synCpw1 (synCfv (synC2nd) C))
  have p0103 := Nominal.mp p0101 p0102
  have p0104 :=
    @gPw1eq
      (synCpw1 (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) C)))
  have p0105 := Nominal.mp p0103 p0104
  have p0106 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCpw1 (synCpw1
          (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))
      (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))) p0083 p0105
  have p0107 :=
    @gPm32i
      (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwcn (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (.classEq (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))
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

/-- Checked nominal proof certificate identified upstream as `g_cfbhnpw13genericquotrepcohndv`. -/
@[expose]
noncomputable def gCfbhnpw13genericquotrepcohndv (C : Class) (Q : Class) (X : Class)
    (hyp_cfbhnpw13genericquotrepcohndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbhnpw13genericquotrepcohndv_2 : Nominal.NPrf (.classMem C (synChwcn (synCpw X))))
    (hyp_cfbhnpw13genericquotrepcohndv_3 : Nominal.NPrf
        (.classMem Q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))))
    (hyp_cfbhnpw13genericquotrepcohndv_4 : Nominal.NPrf
        (.classEq (synCuni (synCuni (synCuni Q))) (synCec C (synChwniso (synCpw X))))) :
    Nominal.NPrf
      (.classEq (synCfv (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q) (synCec
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
          (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) :=
  by
  have p0000 := @gPwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0001 := @gPw1ex (synCpw X) p0000
  have p0002 := @gHnsiquomapfndv (synCpw1 (synCpw X)) p0001
  have p0003 :=
    @gSifmap (synCpw1 (synChnord (synCpw1 (synCpw X))))
      (synChnord (synCpw1 (synCpw1 (synCpw X))))
      (synChnsiquomap (synCpw1 (synCpw X)))
  have p0004 := Nominal.mp p0002 p0003
  have p0006 := @gHnsiquomapfndv (synCpw X) p0000
  have p0007 :=
    @gSifmap (synCpw1 (synChnord (synCpw X))) (synChnord (synCpw1 (synCpw X)))
      (synChnsiquomap (synCpw X))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gSifmap (synCpw1 (synCpw1 (synChnord (synCpw X))))
      (synCpw1 (synChnord (synCpw1 (synCpw X))))
      (synCsi (synChnsiquomap (synCpw X)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gPm32i
      (synWf (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
        (synCpw1 (synCpw1 (synChnord (synCpw1 (synCpw X)))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X))))))
      (synWf (synCsi (synCsi (synChnsiquomap (synCpw X))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synCpw1 (synCpw1 (synChnord (synCpw1 (synCpw X))))))
      p0004 p0010
  have p0012 :=
    @gFco (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCpw1 (synCpw1 (synChnord (synCpw1 (synCpw X)))))
      (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X)))))
      (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
      (synCsi (synCsi (synChnsiquomap (synCpw X))))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gPm32i
      (synWf (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X)))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X))))))
      (.classMem Q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) p0013
      hyp_cfbhnpw13genericquotrepcohndv_3
  have p0015 :=
    @gFvco3 (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X))))) Q
      (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
      (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
        (synCsi (synCsi (synChnsiquomap (synCpw X)))))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 :=
    @gPm32i
      (synWf (synCsi (synCsi (synChnsiquomap (synCpw X))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synCpw1 (synCpw1 (synChnord (synCpw1 (synCpw X))))))
      (.classMem Q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) p0010
      hyp_cfbhnpw13genericquotrepcohndv_3
  have p0024 :=
    @gFvco3 (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCpw1 (synCpw1 (synChnord (synCpw1 (synCpw X))))) Q
      (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
      (synCsi (synCsi (synChnsiquomap (synCpw X))))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gPw1argclcl (synCpw1 (synCpw1 (synChnord (synCpw X)))) Q
  have p0027 := Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0026
  have p0028 :=
    @gSimpr (.classMem (synCuni Q) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (.classEq Q (synCsn (synCuni Q)))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gFveq2i Q (synCsn (synCuni Q)) (synCsi (synCsi (synChnsiquomap (synCpw X))))
      p0029
  have p0037 :=
    @gSimpl (.classMem (synCuni Q) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (.classEq Q (synCsn (synCuni Q)))
  have p0038 := Nominal.mp p0027 p0037
  have p0039 :=
    @gPm32i
      (synWf (synCsi (synChnsiquomap (synCpw X)))
        (synCpw1 (synCpw1 (synChnord (synCpw X))))
        (synCpw1 (synChnord (synCpw1 (synCpw X)))))
      (.classMem (synCuni Q) (synCpw1 (synCpw1 (synChnord (synCpw X))))) p0008 p0038
  have p0040 :=
    @gSifvalimpclndv (synCuni Q) (synCpw1 (synCpw1 (synChnord (synCpw X))))
      (synCpw1 (synChnord (synCpw1 (synCpw X))))
      (synCsi (synChnsiquomap (synCpw X)))
  have p0041 := Nominal.mp p0039 p0040
  have p0046 := @gPw1argclcl (synCpw1 (synChnord (synCpw X))) (synCuni Q)
  have p0047 := Nominal.mp p0038 p0046
  have p0048 :=
    @gSimpr (.classMem (synCuni (synCuni Q)) (synCpw1 (synChnord (synCpw X))))
      (.classEq (synCuni Q) (synCsn (synCuni (synCuni Q))))
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @gFveq2i (synCuni Q) (synCsn (synCuni (synCuni Q)))
      (synCsi (synChnsiquomap (synCpw X))) p0049
  have p0059 :=
    @gSimpl (.classMem (synCuni (synCuni Q)) (synCpw1 (synChnord (synCpw X))))
      (.classEq (synCuni Q) (synCsn (synCuni (synCuni Q))))
  have p0060 := Nominal.mp p0047 p0059
  have p0061 :=
    @gPm32i
      (synWf (synChnsiquomap (synCpw X)) (synCpw1 (synChnord (synCpw X)))
        (synChnord (synCpw1 (synCpw X))))
      (.classMem (synCuni (synCuni Q)) (synCpw1 (synChnord (synCpw X)))) p0006 p0060
  have p0062 :=
    @gSifvalimpclndv (synCuni (synCuni Q)) (synCpw1 (synChnord (synCpw X)))
      (synChnord (synCpw1 (synCpw X))) (synChnsiquomap (synCpw X))
  have p0063 := Nominal.mp p0061 p0062
  have p0064 :=
    @gEqtri (synCfv (synCsi (synChnsiquomap (synCpw X))) (synCuni Q))
      (synCfv (synCsi (synChnsiquomap (synCpw X))) (synCsn (synCuni (synCuni Q))))
      (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))) p0050
      p0063
  have p0065 :=
    @gSneqi (synCfv (synCsi (synChnsiquomap (synCpw X))) (synCuni Q))
      (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))) p0064
  have p0066 :=
    @gEqtri
      (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) (synCsn (synCuni Q)))
      (synCsn (synCfv (synCsi (synChnsiquomap (synCpw X))) (synCuni Q)))
      (synCsn (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      p0041 p0065
  have p0067 :=
    @gEqtri (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) Q)
      (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) (synCsn (synCuni Q)))
      (synCsn (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      p0030 p0066
  have p0068 :=
    @gFveq2i (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) Q)
      (synCsn (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synCsi (synChnsiquomap (synCpw1 (synCpw X)))) p0067
  have p0080 :=
    @gPm32i (.classMem C (synChwcn (synCpw X)))
      (.classEq (synCuni (synCuni (synCuni Q))) (synCec C (synChwniso (synCpw X))))
      hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0081 :=
    @gPm32i (.classMem (synCuni (synCuni Q)) (synCpw1 (synChnord (synCpw X))))
      (synWa (.classMem C (synChwcn (synCpw X))) (.classEq (synCuni (synCuni (synCuni Q)))
          (synCec C (synChwniso (synCpw X)))))
      p0060 p0080
  have p0083 := @gHnsiquomaprepvalcl3ndv (synCpw X) C (synCuni (synCuni Q)) p0000
  have p0084 := Nominal.mp p0081 p0083
  have p0085 := @gSnelpw1 C (synChwcn (synCpw X))
  have p0086 :=
    @gMpbir (.classMem (synCsn C) (synCpw1 (synChwcn (synCpw X))))
      (.classMem C (synChwcn (synCpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0085
  have p0087 := @gHnsicodemapfndv (synCpw X)
  have p0088 :=
    @gFfvelrni (synCpw1 (synChwcn (synCpw X))) (synChwcn (synCpw1 (synCpw X)))
      (synCsn C) (synChnsicodemap (synCpw X)) p0087
  have p0089 := Nominal.mp p0086 p0088
  have p0092 :=
    @gHwnisoclasselhnordcl (synCpw1 (synCpw X))
      (synCfv (synChnsicodemap (synCpw X)) (synCsn C)) p0001
  have p0093 := Nominal.mp p0089 p0092
  have p0094 :=
    @gEqeltri (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))
      (synCec (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
        (synChwniso (synCpw1 (synCpw X))))
      (synChnord (synCpw1 (synCpw X))) p0084 p0093
  have p0095 :=
    @gSnelpw1 (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))
      (synChnord (synCpw1 (synCpw X)))
  have p0096 :=
    @gMpbir
      (.classMem (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))
        (synCpw1 (synChnord (synCpw1 (synCpw X)))))
      (.classMem (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))
        (synChnord (synCpw1 (synCpw X))))
      p0094 p0095
  have p0097 :=
    @gPm32i
      (synWf (synChnsiquomap (synCpw1 (synCpw X)))
        (synCpw1 (synChnord (synCpw1 (synCpw X))))
        (synChnord (synCpw1 (synCpw1 (synCpw X)))))
      (.classMem (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))
        (synCpw1 (synChnord (synCpw1 (synCpw X)))))
      p0002 p0096
  have p0098 :=
    @gSifvalimpclndv
      (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))
      (synCpw1 (synChnord (synCpw1 (synCpw X))))
      (synChnord (synCpw1 (synCpw1 (synCpw X))))
      (synChnsiquomap (synCpw1 (synCpw X)))
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @gEqtri
      (synCfv (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
        (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) Q))
      (synCfv (synCsi (synChnsiquomap (synCpw1 (synCpw X)))) (synCsn
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
      (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
      p0068 p0099
  have p0101 :=
    @gEqtri
      (synCfv (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))) Q)
      (synCfv (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
        (synCfv (synCsi (synCsi (synChnsiquomap (synCpw X)))) Q))
      (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
      p0025 p0100
  have p0102 :=
    @gFveq2i
      (synCfv (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))) Q)
      (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
      (synChnsiquomap (synCpw1 (synCpw1 (synCpw X)))) p0101
  have p0103 :=
    @gEqtri
      (synCfv (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)
      (synCfv (synChnsiquomap (synCpw1 (synCpw1 (synCpw X)))) (synCfv
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X))))) Q))
      (synCfv (synChnsiquomap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
          (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))))
      p0016 p0102
  have p0157 :=
    @gElex (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))
      (synChnord (synCpw1 (synCpw X)))
  have p0158 := Nominal.mp p0094 p0157
  have p0159 :=
    @gUnisn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))) p0158
  have p0173 :=
    @gEqtri
      (synCuni (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))
      (synCec (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
        (synChwniso (synCpw1 (synCpw X))))
      p0159 p0084
  have p0174 :=
    @gPm32i
      (.classMem (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
        (synChwcn (synCpw1 (synCpw X))))
      (.classEq (synCuni
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
        (synCec (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
          (synChwniso (synCpw1 (synCpw X)))))
      p0089 p0173
  have p0175 :=
    @gPm32i
      (.classMem (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))
        (synCpw1 (synChnord (synCpw1 (synCpw X)))))
      (synWa (.classMem (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
          (synChwcn (synCpw1 (synCpw X)))) (.classEq (synCuni
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
          (synCec (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
            (synChwniso (synCpw1 (synCpw X))))))
      p0096 p0174
  have p0178 :=
    @gHnsiquomaprepvalcl3ndv (synCpw1 (synCpw X))
      (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
      (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))) p0001
  have p0179 := Nominal.mp p0175 p0178
  have p0185 :=
    @gSnelpw1 (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
      (synChwcn (synCpw1 (synCpw X)))
  have p0186 :=
    @gMpbir
      (.classMem (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
        (synCpw1 (synChwcn (synCpw1 (synCpw X)))))
      (.classMem (synCfv (synChnsicodemap (synCpw X)) (synCsn C))
        (synChwcn (synCpw1 (synCpw X))))
      p0089 p0185
  have p0187 := @gHnsicodemapfndv (synCpw1 (synCpw X))
  have p0188 :=
    @gFfvelrni (synCpw1 (synChwcn (synCpw1 (synCpw X))))
      (synChwcn (synCpw1 (synCpw1 (synCpw X))))
      (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))
      (synChnsicodemap (synCpw1 (synCpw X))) p0187
  have p0189 := Nominal.mp p0186 p0188
  have p0192 := @gPw1ex (synCpw1 (synCpw X)) p0001
  have p0193 :=
    @gHwnisoclasselhnordcl (synCpw1 (synCpw1 (synCpw X)))
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      p0192
  have p0194 := Nominal.mp p0189 p0193
  have p0195 :=
    @gEqeltri
      (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
        (synChwniso (synCpw1 (synCpw1 (synCpw X)))))
      (synChnord (synCpw1 (synCpw1 (synCpw X)))) p0179 p0194
  have p0196 :=
    @gSnelpw1
      (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synChnord (synCpw1 (synCpw1 (synCpw X))))
  have p0197 :=
    @gMpbir
      (.classMem (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X))))))
      (.classMem (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
        (synChnord (synCpw1 (synCpw1 (synCpw X)))))
      p0195 p0196
  have p0300 :=
    @gElex
      (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synChnord (synCpw1 (synCpw1 (synCpw X))))
  have p0301 := Nominal.mp p0195 p0300
  have p0302 :=
    @gUnisn
      (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      p0301
  have p0379 :=
    @gEqtri
      (synCuni (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))))
      (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))
      (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
        (synChwniso (synCpw1 (synCpw1 (synCpw X)))))
      p0302 p0179
  have p0380 :=
    @gPm32i
      (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
        (synChwcn (synCpw1 (synCpw1 (synCpw X)))))
      (.classEq (synCuni (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))))
        (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
          (synChwniso (synCpw1 (synCpw1 (synCpw X))))))
      p0189 p0379
  have p0381 :=
    @gPm32i
      (.classMem (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 (synCpw X))))))
      (synWa (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
          (synChwcn (synCpw1 (synCpw1 (synCpw X))))) (.classEq (synCuni (synCsn
              (synCfv (synChnsiquomap (synCpw1 (synCpw X))) (synCsn
                  (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))) (synCec
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
            (synChwniso (synCpw1 (synCpw1 (synCpw X)))))))
      p0197 p0380
  have p0385 :=
    @gHnsiquomaprepvalcl3ndv (synCpw1 (synCpw1 (synCpw X)))
      (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
        (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))
      (synCsn (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
          (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q))))))
      p0192
  have p0386 := Nominal.mp p0381 p0385
  have p0387 :=
    @gEqtri
      (synCfv (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)
      (synCfv (synChnsiquomap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
          (synCfv (synChnsiquomap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsiquomap (synCpw X)) (synCuni (synCuni Q)))))))
      (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
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

/-- Checked nominal proof certificate identified upstream as
`g_cfbhnpw13genericcodepointcoverndv`.
-/
@[expose]
noncomputable def gCfbhnpw13genericcodepointcoverndv (C : Class) (Q : Class) (X : Class)
    (hyp_cfbhnpw13genericcodepointcoverndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbhnpw13genericcodepointcoverndv_2 :
      Nominal.NPrf (.classMem C (synChwcn (synCpw X))))
    (hyp_cfbhnpw13genericcodepointcoverndv_3 : Nominal.NPrf
        (.classMem Q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))))
    (hyp_cfbhnpw13genericcodepointcoverndv_4 : Nominal.NPrf
        (.classEq (synCuni (synCuni (synCuni Q))) (synCec C (synChwniso (synCpw X)))))
    (hyp_cfbhnpw13genericcodepointcoverndv_5 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) Q) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))))) :=
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
  have dv_cache_0003 : k ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw X))))).fv :=
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
  have dv_cache_0004 : k ∉ ((synCpw (synCpw (synChnord X)))).fv :=
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
      ((Wff.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))) (synCec
              (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
                  (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                    (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
              (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))))).fv :=
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
    @gCfbwpphwcncarrierinjndv C k X dv_cache_0001 dv_cache_0002
      hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2
      hyp_cfbhnpw13genericcodepointcoverndv_5
  have p0001 :=
    @gCfbhnpw13genericraisedcodendv C X hyp_cfbhnpw13genericcodepointcoverndv_1
      hyp_cfbhnpw13genericcodepointcoverndv_2
  have p0002 :=
    @gSimpr
      (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwcn (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (.classEq (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gF1eq2
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
      (synCpw (synCpw (synChnord X))) (.cv k)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gBiimpri
      (synWf1 (.cv k) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
        (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
        (synCpw (synCpw (synChnord X))))
      p0005
  have p0007 := @gPwex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0008 := @gPw1ex (synCpw X) p0007
  have p0009 := @gPw1ex (synCpw1 (synCpw X)) p0008
  have p0010 := @gPw1ex (synCpw1 (synCpw1 (synCpw X))) p0009
  have p0011 := @gHnordex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0012 := @gPwex (synChnord X) p0011
  have p0013 := @gPwex (synCpw (synChnord X)) p0012
  have p0015 :=
    @gSimpl
      (.classMem (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwcn (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (.classEq (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C)))))
  have p0016 := Nominal.mp p0001 p0015
  have p0017 :=
    @gCfbhnqinjcodecoverdclndv
      (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
          (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
            (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) k (synCpw (synCpw (synChnord X)))
      dv_cache_0003 dv_cache_0004 p0010 p0013 p0016
  have p0018 :=
    @gSyl
      (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
        (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv k) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C)))))))
        (synCpw (synCpw (synChnord X))))
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCec
            (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
            (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      p0006 p0017
  have p0019 :=
    @gExlimiv
      (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
        (synCpw (synCpw (synChnord X))))
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCec
            (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
            (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      k dv_cache_0005 p0018
  have p0020 :=
    @gSyl (synWwpp)
      (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 (synCfv (synC2nd) C))))
          (synCpw (synCpw (synChnord X)))))
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCec
            (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
            (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      p0000 p0019
  have p0021 :=
    @gCfbhnpw13genericquotrepcohndv C Q X hyp_cfbhnpw13genericcodepointcoverndv_1
      hyp_cfbhnpw13genericcodepointcoverndv_2 hyp_cfbhnpw13genericcodepointcoverndv_3
      hyp_cfbhnpw13genericcodepointcoverndv_4
  have p0022 :=
    @gEqcomi
      (synCfv (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)
      (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      p0021
  have p0023 :=
    @gFveq2i
      (synCec (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
            (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
              (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
        (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (synCfv (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)
      (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
        (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))))
      p0022
  have p0024 :=
    @gEleq1i
      (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))) (synCec
          (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
              (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
          (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))))
      (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))) (synCfv
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q))
      (synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      p0023
  have p0025 :=
    @gSylib (synWwpp)
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCec
            (synCfv (synChnsicodemap (synCpw1 (synCpw1 (synCpw X)))) (synCsn
                (synCfv (synChnsicodemap (synCpw1 (synCpw X)))
                  (synCsn (synCfv (synChnsicodemap (synCpw X)) (synCsn C))))))
            (synChwniso (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCfv
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      p0020 p0024
  have p0027 := @gHnpw13quoshiftf1ondv (synCpw X) p0007
  have p0028 :=
    @gF1of (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gPm32i
      (synWf (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (.classMem Q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) p0029
      hyp_cfbhnpw13genericcodepointcoverndv_3
  have p0031 :=
    @gFvco3 (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X))))) Q
      (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
        (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gEleq1i
      (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))) Q)
      (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))) (synCfv
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q))
      (synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      p0032
  have p0034 :=
    @gSylibr (synWwpp)
      (.classMem (synCfv (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))) (synCfv
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X)))))) Q)) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) Q) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
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

/-- Checked nominal proof certificate identified upstream as `g_cfbhnpw13pointcoverndv`. -/
@[expose]
noncomputable def gCfbhnpw13pointcoverndv (X : Class) (q : Var)
    (hyp_cfbhnpw13pointcoverndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbhnpw13pointcoverndv_2 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.imp (synWwpp) (.classMem (synCfv (synCcom
                (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X))))))))) :=
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
  have dv_cache_0001 : u ∉ ((synCpw X)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_u_not_X,
          not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synCuni (synCuni (synCuni (.cv q))))).fv :=
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
      ((Wff.classEq (.cv q) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))))).fv :=
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
      ((Wff.imp (synWwpp) (.classMem (synCfv (synCcom
                (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
                (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
                (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X))))))))).fv :=
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
  have p0000 := @gPw1argclcl (synCpw1 (synCpw1 (synChnord (synCpw X)))) (.cv q)
  have p0001 :=
    @gSimpld
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (.cv q)) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0000
  have p0002 := @gPw1argclcl (synCpw1 (synChnord (synCpw X))) (synCuni (.cv q))
  have p0003 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (.cv q)) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) (synCpw1 (synChnord (synCpw X))))
        (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))))
      p0001 p0002
  have p0004 :=
    @gSimpld
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (.cv q))) (synCpw1 (synChnord (synCpw X))))
      (.classEq (synCuni (.cv q)) (synCsn (synCuni (synCuni (.cv q))))) p0003
  have p0005 := @gPw1argclcl (synChnord (synCpw X)) (synCuni (synCuni (.cv q)))
  have p0006 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (.cv q))) (synCpw1 (synChnord (synCpw X))))
      (synWa (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X)))
        (.classEq (synCuni (synCuni (.cv q)))
          (synCsn (synCuni (synCuni (synCuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @gSimpld
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X)))
      (.classEq (synCuni (synCuni (.cv q)))
        (synCsn (synCuni (synCuni (synCuni (.cv q))))))
      p0006
  have p0016 := @gElex (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X))
  have p0017 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X)))
      (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synCvv)) p0007 p0016
  have p0018 :=
    @gElhnordclndv u (synCpw X) (synCuni (synCuni (synCuni (.cv q)))) dv_cache_0001
      dv_cache_0002
  have p0019 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synCvv))
      (synWb (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X)))
        (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (.cv q))))
            (synCec (.cv u) (synChwniso (synCpw X))))))
      p0017 p0018
  have p0020 :=
    @gMpbid (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCuni (synCuni (synCuni (.cv q)))) (synChnord (synCpw X)))
      (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCec (.cv u) (synChwniso (synCpw X)))))
      p0007 p0019
  have p0021 :=
    @gId
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
  have p0022 :=
    @gUnieqd
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (.cv q)
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      p0021
  have p0023 :=
    @gUnieqd
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCuni (.cv q))
      (synCuni (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      p0022
  have p0024 :=
    @gUnieqd
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCuni (synCuni (.cv q)))
      (synCuni (synCuni (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X)))))))))
      p0023
  have p0025 :=
    @gEqeq1d
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCuni (synCuni (synCuni (.cv q))))
      (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))))))
      (synCec (.cv u) (synChwniso (synCpw X))) p0024
  have p0026 :=
    @gRexbidv
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (.classEq (synCuni (synCuni (synCuni (.cv q))))
        (synCec (.cv u) (synChwniso (synCpw X))))
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))))))
        (synCec (.cv u) (synChwniso (synCpw X))))
      u (synChwcn (synCpw X)) dv_cache_0003 p0025
  have p0028 :=
    @gFveq2d
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (.cv q)
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
      p0021
  have p0029 :=
    @gEleq1d
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q))
      (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      p0028
  have p0030 :=
    @gImbi2d
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X)))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (synWwpp) p0029
  have p0031 :=
    @gImbi12d
      (.classEq (.cv q) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCec (.cv u) (synChwniso (synCpw X)))))
      (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (synCif
                  (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
                  (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)) (synChwniso (synCpw X))))))))))
          (synCec (.cv u) (synChwniso (synCpw X)))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
              (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
              (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X)))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      p0026 p0030
  have p0032 :=
    @gEceq1 (.cv u)
      (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synChwniso (synCpw X))
  have p0033 :=
    @gEqeq2d
      (.classEq (.cv u) (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCec (.cv u) (synChwniso (synCpw X)))
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))))))
      p0032
  have p0034 :=
    @gImbi1d
      (.classEq (.cv u) (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))))))
        (synCec (.cv u) (synChwniso (synCpw X))))
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
              (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
              (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X)))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      p0033
  have p0035 :=
    @gId
      (.classEq (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCif (.classEq (synCuni
              (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
  have p0036 :=
    @gFveq2d
      (.classEq (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCif (.classEq (synCuni
              (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
      p0035
  have p0037 :=
    @gEleq1d
      (.classEq (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCif (.classEq (synCuni
              (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif (.classEq (synCuni
              (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      p0036
  have p0038 :=
    @gImbi2d
      (.classEq (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCif (.classEq (synCuni
              (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X)))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif (.classEq
              (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                      (synCsn (synCsn (synCsn (synCec (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)) (synChwniso (synCpw X)))))))))) (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                  (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (synWwpp) p0037
  have p0039 := @gEqid (synC0)
  have p0040 :=
    @gSimpr (.classEq (synC0) (synC0)) (.classMem (.cv u) (synChwcn (synCpw X)))
  have p0041 := @gHncodecmpdefaultcnndv (synCpw X)
  have p0042 :=
    @gA1i
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn (synCpw X)))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem (.cv u) (synChwcn (synCpw X)))))
      p0041
  have p0043 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem (.cv u) (synChwcn (synCpw X)))
      (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn (synCpw X)) p0040 p0042
  have p0044 := Nominal.mp p0039 p0043
  have p0046 :=
    @gSimpr (.classEq (synC0) (synC0))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
  have p0048 := @gPwex X hyp_cfbhnpw13pointcoverndv_1
  have p0049 :=
    @gHwnisoclasselhnordcl (synCpw X)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      p0048
  have p0050 := Nominal.mp p0041 p0049
  have p0051 :=
    @gSnelpw1
      (synCec
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwniso (synCpw X)))
      (synChnord (synCpw X))
  have p0052 :=
    @gMpbir
      (.classMem (synCsn (synCec
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
            (synChwniso (synCpw X)))) (synCpw1 (synChnord (synCpw X))))
      (.classMem (synCec
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
          (synChwniso (synCpw X))) (synChnord (synCpw X)))
      p0050 p0051
  have p0053 :=
    @gSnelpw1
      (synCsn (synCec (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)) (synChwniso (synCpw X))))
      (synCpw1 (synChnord (synCpw X)))
  have p0054 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCec
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
              (synChwniso (synCpw X))))) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (.classMem (synCsn (synCec
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
            (synChwniso (synCpw X)))) (synCpw1 (synChnord (synCpw X))))
      p0052 p0053
  have p0055 :=
    @gSnelpw1
      (synCsn (synCsn (synCec
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
            (synChwniso (synCpw X)))))
      (synCpw1 (synCpw1 (synChnord (synCpw X))))
  have p0056 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCsn (synCsn (synCec
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
              (synChwniso (synCpw X))))) (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      p0054 p0055
  have p0057 :=
    @gA1i
      (.classMem (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (synWa (.classEq (synC0) (synC0)) (.neg
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))))
      p0056
  have p0058 :=
    @gIfclda (.classEq (synC0) (synC0))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.cv q)
      (synCsn (synCsn (synCsn (synCec
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
              (synChwniso (synCpw X))))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) p0046 p0057
  have p0059 := Nominal.mp p0039 p0058
  have p0067 :=
    @gHwnisoclasselhnordcl (synCpw X)
      (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      p0048
  have p0068 := Nominal.mp p0044 p0067
  have p0069 :=
    @gSnelpw1
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      (synChnord (synCpw X))
  have p0070 :=
    @gMpbir
      (.classMem (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCpw1 (synChnord (synCpw X))))
      (.classMem (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))) (synChnord (synCpw X)))
      p0068 p0069
  have p0071 :=
    @gSnelpw1
      (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCpw1 (synChnord (synCpw X)))
  have p0072 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))))
        (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (.classMem (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCpw1 (synChnord (synCpw X))))
      p0070 p0071
  have p0073 :=
    @gSnelpw1
      (synCsn (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCpw1 (synCpw1 (synChnord (synCpw X))))
  have p0074 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))))
        (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      p0072 p0073
  have p0075 :=
    @gPm32i
      (.classMem (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.classMem (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      p0059 p0074
  have p0076 :=
    @gIfcl
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
  have p0077 := Nominal.mp p0075 p0076
  have p0078 :=
    @gIftrue
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
  have p0079 :=
    @gUnieqd
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      p0078
  have p0080 :=
    @gUnieqd
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCuni (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))))
      p0079
  have p0081 :=
    @gUnieqd
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCuni (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif
                      (.classMem (.cv q)
                        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                      (synCsn (synCsn (synCsn (synCec (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)) (synChwniso (synCpw X)))))))))) (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                  (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))))))))
      (synCuni (synCuni (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X)))))))))
      p0080
  have p0082 :=
    @gId
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
  have p0083 :=
    @gEqtrd
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCuni (synCuni (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif
                        (.classMem (.cv q)
                          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                        (synCsn (synCsn (synCsn (synCec (synCop
                                  (synCin (synCkqrel (synClefin))
                                    (synCxp (synC0) (synC0))) (synC0))
                                (synChwniso (synCpw X)))))))))) (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                    (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0))) (synChwniso (synCpw X))))))))))
      (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))))))
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      p0081 p0082
  have p0084 :=
    @gIffalse
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
  have p0085 :=
    @gUnieqd
      (.neg (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
      p0084
  have p0086 :=
    @gUnieqd
      (.neg (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X)))))))))) (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X)))) (synCif
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
            (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
                    (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCuni (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      p0085
  have p0087 :=
    @gUnieqd
      (.neg (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCuni (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif
                      (.classMem (.cv q)
                        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                      (synCsn (synCsn (synCsn (synCec (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)) (synChwniso (synCpw X)))))))))) (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                  (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))))))))
      (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      p0086
  have p0088 :=
    @gSnex
      (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
  have p0089 :=
    @gUnisn
      (synCsn (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      p0088
  have p0090 :=
    @gUnieqi
      (synCuni (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      p0089
  have p0091 :=
    @gSnex
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
  have p0092 :=
    @gUnisn
      (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      p0091
  have p0093 :=
    @gEqtri
      (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCuni (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
      (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      p0090 p0092
  have p0094 :=
    @gUnieqi
      (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X))))))))
      (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      p0093
  have p0104 :=
    @gElex
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      (synChnord (synCpw X))
  have p0105 := Nominal.mp p0068 p0104
  have p0106 :=
    @gUnisn
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      p0105
  have p0107 :=
    @gEqtri
      (synCuni (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                    (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))))))))
      (synCuni (synCsn (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      p0094 p0106
  have p0108 :=
    @gA1i
      (.classEq (synCuni (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                      (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0))) (synChwniso (synCpw X))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (.neg (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      p0107
  have p0109 :=
    @gEqtrd
      (.neg (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))))
      (synCuni (synCuni (synCuni (synCif (.classEq (synCuni (synCuni (synCuni (synCif
                        (.classMem (.cv q)
                          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                        (synCsn (synCsn (synCsn (synCec (synCop
                                  (synCin (synCkqrel (synClefin))
                                    (synCxp (synC0) (synC0))) (synC0))
                                (synChwniso (synCpw X)))))))))) (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                    (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0))) (synChwniso (synCpw X))))))))))
      (synCuni (synCuni (synCuni (synCsn (synCsn (synCsn (synCec
                    (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))))))))
      (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso (synCpw X)))
      p0087 p0108
  have p0110 :=
    @gPm261i
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (.classEq (synCuni (synCuni (synCuni (synCif (.classEq (synCuni (synCuni (synCuni
                        (synCif (.classMem (.cv q)
                            (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                          (synCsn (synCsn (synCsn (synCec (synCop
                                    (synCin (synCkqrel (synClefin))
                                      (synCxp (synC0) (synC0))) (synC0))
                                  (synChwniso (synCpw X)))))))))) (synCec
                    (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))) (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                        (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0))) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      p0083 p0109
  have p0111 :=
    @gCfbhnpw13genericcodepointcoverndv
      (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCif (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (synCif
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
          (synCsn (synCsn (synCsn (synCec
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn (synCec
                (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))) (synChwniso (synCpw X)))))))
      X hyp_cfbhnpw13pointcoverndv_1 p0044 p0077 p0110 hyp_cfbhnpw13pointcoverndv_2
  have p0112 :=
    @gDedth
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))))) (synCec
          (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso (synCpw X))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
              (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
              (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X)))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif (.classEq
                (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                        (synCsn (synCsn (synCsn (synCec (synCop
                                  (synCin (synCkqrel (synClefin))
                                    (synCxp (synC0) (synC0))) (synC0))
                                (synChwniso (synCpw X)))))))))) (synCec
                  (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
                  (synChwniso (synCpw X)))) (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))) (synCsn (synCsn (synCsn
                    (synCec (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0))) (synChwniso (synCpw X)))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      (synCif (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (.cv q) (synCsn (synCsn (synCsn (synCec
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)) (synChwniso (synCpw X)))))))
      (synCsn (synCsn (synCsn (synCec
              (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))) (synChwniso (synCpw X))))))
      p0038 p0111
  have p0113 :=
    @gDedth (.classMem (.cv u) (synChwcn (synCpw X)))
      (.imp (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X))))))))))
          (synCec (.cv u) (synChwniso (synCpw X)))) (.imp (synWwpp) (.classMem (synCfv
              (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
                (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
                (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))))))
      (.imp (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                    (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                    (synCsn (synCsn (synCec (synCop (synCin (synCkqrel (synClefin))
                              (synCxp (synC0) (synC0))) (synC0))
                          (synChwniso (synCpw X)))))))))) (synCec
            (synCif (.classMem (.cv u) (synChwcn (synCpw X))) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso (synCpw X)))) (.imp (synWwpp) (.classMem (synCfv
              (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
                (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
                (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))))))
      (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      p0034 p0112
  have p0114 :=
    @gRexlimiv
      (.classEq (synCuni (synCuni (synCuni (synCif (.classMem (.cv q)
                  (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q) (synCsn
                  (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X))))))))))
        (synCec (.cv u) (synChwniso (synCpw X))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
              (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
              (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)) (synChwniso (synCpw X)))))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      u (synChwcn (synCpw X)) dv_cache_0004 p0113
  have p0115 :=
    @gDedth (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (.imp (synWrex u (synChwcn (synCpw X))
          (.classEq (synCuni (synCuni (synCuni (.cv q))))
            (synCec (.cv u) (synChwniso (synCpw X))))) (.imp (synWwpp) (.classMem (synCfv
              (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))))))
      (.imp (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (synCif
                    (.classMem (.cv q)
                      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (.cv q)
                    (synCsn (synCsn (synCsn (synCec (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)) (synChwniso (synCpw X))))))))))
            (synCec (.cv u) (synChwniso (synCpw X))))) (.imp (synWwpp) (.classMem (synCfv
              (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (synCif
                (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
                (.cv q) (synCsn (synCsn (synCsn (synCec (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)) (synChwniso (synCpw X)))))))) (synCrn
              (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))))))
      (.cv q)
      (synCsn (synCsn (synCsn (synCec
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
              (synChwniso (synCpw X))))))
      p0031 p0114
  have p0116 :=
    @gMpd (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (synWrex u (synChwcn (synCpw X)) (.classEq (synCuni (synCuni (synCuni (.cv q))))
          (synCec (.cv u) (synChwniso (synCpw X)))))
      (.imp (synWwpp) (.classMem (synCfv (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
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

/-- Checked nominal proof certificate identified upstream as
`g_cfbwppfixedblockhnqimagecoverndv`.
-/
@[expose]
noncomputable def gCfbwppfixedblockhnqimagecoverndv (X : Class)
    (hyp_cfbwppfixedblockhnqimagecoverndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbwppfixedblockhnqimagecoverndv_2 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWss (synCima (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
            (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))))) :=
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
  have dv_cache_0001 : q ∉ ((synWwpp)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    q ∉ ((synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))).fv :=
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
      ((synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X))))))).fv :=
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
      ((synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X)))))))).fv :=
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
    @gCfbhnpw13pointcoverndv X q hyp_cfbwppfixedblockhnqimagecoverndv_1
      hyp_cfbwppfixedblockhnqimagecoverndv_2
  have p0001 :=
    @gCom12 (.classMem (.cv q) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (synWwpp)
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      p0000
  have p0002 :=
    @gRalrimiv (synWwpp)
      (.classMem (synCfv (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) dv_cache_0001 p0001
  have p0003 :=
    @gSsun1 (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
      (synCpw (synCpw (synChnord X)))
  have p0004 := @gPwexg X (synCvv)
  have p0005 := Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0004
  have p0006 := @gPw1exg (synCpw X) (synCvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gPw1exg (synCpw1 (synCpw X)) (synCvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gPw1exg (synCpw1 (synCpw1 (synCpw X))) (synCvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0020 := @gHnordexg X
  have p0021 := Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0020
  have p0022 := @gPwexg (synChnord X) (synCvv)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @gPwexg (synCpw (synChnord X)) (synCvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gPm32i (.classMem (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) (synCvv))
      (.classMem (synCpw (synCpw (synChnord X))) (synCvv)) p0011 p0025
  have p0027 :=
    @gUnexg (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
      (synCpw (synCpw (synChnord X))) (synCvv) (synCvv)
  have p0028 := Nominal.mp p0026 p0027
  have p0029 :=
    @gHnqincfn
      (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) (synCpw (synCpw (synChnord X))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) p0003 p0011 p0028
  have p0032 := @gHnpw13quoshiftf1ondv (synCpw X) p0005
  have p0033 :=
    @gF1of (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 :=
    @gPm32i
      (synWfn (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      (synWf (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X))))))
      p0029 p0034
  have p0036 :=
    @gFnfco (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
        (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @gFnfun (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
  have p0039 := Nominal.mp p0037 p0038
  have p0075 :=
    @gFndm (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
  have p0076 := Nominal.mp p0037 p0075
  have p0077 :=
    @gEqcomi
      (synCdm (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) p0076
  have p0078 :=
    @gSsid
      (synCdm (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
  have p0079 :=
    @gEqsstri (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCdm (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
      (synCdm (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
      p0077 p0078
  have p0080 :=
    @gPm32i
      (synWfun (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
      (synWss (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) (synCdm (synCcom
            (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X)))))))))
      p0039 p0079
  have p0081 :=
    @gFunimass4 q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCrn (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0082 := Nominal.mp p0080 p0081
  have p0083 :=
    @gSylibr (synWwpp)
      (synWral q (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) (.classMem (synCfv
            (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))) (.cv q)) (synCrn
            (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X))))))))
      (synWss (synCima (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      p0002 p0082
  exact p0083

/-- Checked nominal proof certificate identified upstream as `g_cfbwppfixedblockhnqgraphinjndv`. -/
@[expose]
noncomputable def gCfbwppfixedblockhnqgraphinjndv (X : Class)
    (hyp_cfbwppfixedblockhnqgraphinjndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbwppfixedblockhnqgraphinjndv_2 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWf1 (synCres (synCcom (synCcnv
                (synChnqinc (synCpw (synCpw (synChnord X)))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))) (synCcom
                (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
            (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
          (synChnord (synCpw (synCpw (synChnord X)))))) :=
  by
  have p0000 :=
    @gCfbwppfixedblockhnqimagecoverndv X hyp_cfbwppfixedblockhnqgraphinjndv_1
      hyp_cfbwppfixedblockhnqgraphinjndv_2
  have p0001 := @gPwexg X (synCvv)
  have p0002 := Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0001
  have p0003 := @gPw1exg (synCpw X) (synCvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gPw1exg (synCpw1 (synCpw X)) (synCvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gPw1exg (synCpw1 (synCpw1 (synCpw X))) (synCvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gHnordexg X
  have p0010 := Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0009
  have p0011 := @gPwexg (synChnord X) (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gPwexg (synCpw (synChnord X)) (synCvv)
  have p0014 := Nominal.mp p0012 p0013
  have p0017 := @gHnpw13quoshiftf1ondv (synCpw X) p0002
  have p0018 :=
    @gF1of1 (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gHnqcommonprecoverinjndv (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synCpw (synCpw (synChnord X)))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
      p0008 p0014 p0019
  have p0021 :=
    @gSyl (synWwpp)
      (synWss (synCima (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (synCrn
          (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))))
      (synWf1 (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))) (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw (synCpw (synChnord X)))))
      p0000 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end
