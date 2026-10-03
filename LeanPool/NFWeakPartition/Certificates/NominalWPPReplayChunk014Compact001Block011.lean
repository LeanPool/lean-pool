/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutclassordcl (B : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassordcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D)
        (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_chnord D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @g_elex B D
  have p0001 := @g_eleq1 (.cv x) B D
  have p0002 := @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwniso D)
  have p0004 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)))
      p0002 p0003
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D) p0004
  have p0006 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D))
      (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)) p0001
      p0005
  have p0007 := @g_hnwcutclassord x D R dv_cache_0002 hyp_hnwcutclassordcl_1
  have p0008 :=
    @g_vtoclg
      (.imp (.classMem (.cv x) D)
        (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D)))
      (.imp (.classMem B D)
        (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)))
      x B (syn_cvv) dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D)
      (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)) p0000
      p0008
  exact p0009

@[expose]
noncomputable def g_hnwcutmapf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0003 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0004 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_chnord D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_p_not_D, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hnwcutmap D R p
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_pw12argcl (.cv p) D
  have p0002 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv p))) D)
      (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0001
  have p0003 :=
    @g_hnwcutclassordcl (syn_cuni (syn_cuni (.cv p))) D R dv_cache_0003 hyp_hnwcutmapf_1
  have p0004 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv p))) D)
      (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))
        (syn_chnord D))
      p0002 p0003
  have p0005 :=
    @g_fmpti p (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))
      (syn_chnwcutmap R D) dv_cache_0004 dv_cache_0005 p0000 p0004
  exact p0005

@[expose]
noncomputable def g_hnwcutmapval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({ q } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : p ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0003 : Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((syn_cuni (.cv p))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv p)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ (R).fv from (by exact fresh_p_not_R))))))))))
  have dv_cache_0004 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0005 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0006 :
    p ∉
      ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, fresh_p_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0008 : p ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hnwcutmap D R p
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnwcutmap R D) (syn_cmpt p (syn_cpw1 (syn_cpw1 D))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0000
  have p0002 := @g_unieq (.cv p) (.cv q)
  have p0003 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0002
  have p0004 :=
    @g_hnwcutcodeeq3 (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) D R
      dv_cache_0003
  have p0005 :=
    @g_syl (.classEq (.cv p) (.cv q))
      (.classEq (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))))
      (.classEq (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p))))
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      p0003 p0004
  have p0006 :=
    @g_eceq1 (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p))))
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)
  have p0007 :=
    @g_syl (.classEq (.cv p) (.cv q))
      (.classEq (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p))))
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))
      p0005 p0006
  have p0008 :=
    @g_adantl (.classEq (.cv p) (.cv q))
      (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0007
  have p0009 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0010 := @g_pw12argcl (.cv q) D
  have p0011 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0010
  have p0012 :=
    @g_hnwcutclassordcl (syn_cuni (syn_cuni (.cv q))) D R dv_cache_0004 hyp_hnwcutmapval_1
  have p0013 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
        (syn_chnord D))
      p0011 p0012
  have p0014 :=
    @g_elex (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
      (syn_chnord D)
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
        (syn_chnord D))
      (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
        (syn_cvv))
      p0013 p0014
  have p0016 :=
    @g_fvmptd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p (.cv q)
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
      (syn_cpw1 (syn_cpw1 D)) (syn_chnwcutmap R D) (syn_cvv) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0001 p0008 p0009 p0015
  exact p0016

@[expose]
noncomputable def g_hnwcutcodeltnoiso (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg
          (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
            (syn_chnwcutcode R D (.cv y))))) :=
  by
  have p0000 := @g_strictseghwnisono x y D R
  have p0001 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0002 :=
    @g_breq1 (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv y)))
  have p0005 :=
    @g_breq2 (syn_chnwcutcode R D (.cv y))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chwniso D)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0003 p0006
  have p0008 :=
    @g_biimpi
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0007
  have p0009 :=
    @g_a1i
      (.imp (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
          (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0008
  have p0010 :=
    @g_mtod
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000 p0009
  exact p0010

@[expose]
noncomputable def g_hwnisoclasseqbcl (A : Class) (B : Class) (C : Class)
    (hyp_hwnisoclasseqbcl_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
          (syn_wbr B (syn_chwniso A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 : v ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0004 :
    v ∉
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
            (syn_wbr B (syn_chwniso A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_A, fresh_v_not_C, or_false, not_false_eq_true])
  have dv_cache_0005 :
    u ∉
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
            (syn_wbr B (syn_chwniso A) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, fresh_u_ne_v, or_false,
          not_false_eq_true])
  have p0000 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 := @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 := @g_elex C (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 := @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0008 := @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classEq (.cv u) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A)) p0007 p0009
  have p0011 := @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0012 :=
    @g_eqeq1d (.classEq (.cv u) B) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)) p0011
  have p0013 := @g_breq1 (.cv u) B (.cv v) (syn_chwniso A)
  have p0014 :=
    @g_bibi12d (.classEq (.cv u) B)
      (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
      (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) (.cv v)) p0012
      p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv u) B)
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_wbr B (syn_chwniso A) (.cv v)))
      p0010 p0014
  have p0016 := @g_biid (.classMem B (syn_chwcn A))
  have p0017 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)))
      (.classEq (.cv v) C) p0016
  have p0018 := @g_eleq1 (.cv v) C (syn_chwcn A)
  have p0019 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem C (syn_chwcn A)) p0017 p0018
  have p0020 := @g_eceq1 (.cv v) C (syn_chwniso A)
  have p0021 :=
    @g_eqeq2d (.classEq (.cv v) C) (syn_cec (.cv v) (syn_chwniso A))
      (syn_cec C (syn_chwniso A)) (syn_cec B (syn_chwniso A)) p0020
  have p0022 := @g_breq2 (.cv v) C B (syn_chwniso A)
  have p0023 :=
    @g_bibi12d (.classEq (.cv v) C)
      (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
      (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
      (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) C) p0021 p0022
  have p0024 :=
    @g_imbi12d (.classEq (.cv v) C)
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_wbr B (syn_chwniso A) (.cv v)))
      (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
        (syn_wbr B (syn_chwniso A) C))
      p0019 p0023
  have p0025 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      hyp_hwnisoclasseqbcl_1
  have p0026 :=
    @g_id (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0027 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0025
      p0026
  have p0028 := @g_hwnisoclasseqb v u A
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      p0027 p0028
  have p0030 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb
          (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_wbr (.cv u) (syn_chwniso A) (.cv v))))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_wbr B (syn_chwniso A) (.cv v))))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
          (syn_wbr B (syn_chwniso A) C)))
      u v B C (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0015 p0024 p0029
  have p0031 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
          (syn_wbr B (syn_chwniso A) C)))
      p0006 p0030
  have p0032 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)))
        (syn_wbr B (syn_chwniso A) C))
      p0031
  exact p0032

@[expose]
noncomputable def g_hnwcutcodecncl (B : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutcodecncl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @g_elex B D
  have p0001 := @g_eleq1 (.cv x) B D
  have p0002 := @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B)
      (syn_chwcn D) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0001 p0003
  have p0005 := @g_hnwcutcodecn x D R dv_cache_0002 hyp_hnwcutcodecncl_1
  have p0006 :=
    @g_vtoclg
      (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)))
      (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) x B
      (syn_cvv) dv_cache_0003 dv_cache_0004 p0004 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D)
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutclassltne (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassltne_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      hyp_hnwcutclassltne_1
  have p0001 :=
    @g_simpl (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0002 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0002 p0003
  have p0005 := @g_hnwcutcodeltnoiso x y D R
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
          (syn_chnwcutcode R D (.cv y))))
      p0004 p0005
  have p0008 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0009 :=
    @g_ssel (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D
      (.cv x)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv x) D) p0003 p0010
  have p0012 := @g_hnwcutcodecncl (.cv x) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0011
      p0012
  have p0015 := @g_hnwcutcodecncl (.cv y) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) D) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0001
      p0015
  have p0017 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0013 p0016
  have p0018 := @g_brex R D (syn_cwe)
  have p0019 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0020 :=
    @g_syl (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) (.classMem D (syn_cvv))
      p0018 p0019
  have p0021 := Nominal.mp hyp_hnwcutclassltne_1 p0020
  have p0022 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D (.cv y))
      p0021
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
        (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)))
      (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
        (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))))
      p0017 p0022
  have p0024 :=
    @g_biimpd
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      p0023
  have p0025 :=
    @g_con3d
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      p0024
  have p0026 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
          (syn_chnwcutcode R D (.cv y))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0006 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutclassinj (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassinj_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
          (.classEq (.cv x) (.cv y)))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y))
  have p0001 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      p0000 p0001
  have p0003 := @g_wppweconnex D R
  have p0004 := Nominal.mp hyp_hnwcutclassinj_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0008 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0007
      p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv x) D) p0000 p0009
  have p0013 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0007
      p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv y) D) p0000 p0014
  have p0016 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0010 p0015
  have p0017 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0017 p0010
  have p0024 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0026 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv x) (.cv y)) p0017 p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0024 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0023 p0028
  have p0030 := @g_elstrictseg y x D R
  have p0031 :=
    @g_biimpri
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0029 p0031
  have p0033 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0032
  have p0034 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0034 p0015
  have p0041 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0044 :=
    @g_necomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0026
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv y) (.cv x)) p0034 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0041 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0040 p0046
  have p0048 := @g_elstrictseg x y D R
  have p0049 :=
    @g_biimpri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0048
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0047 p0049
  have p0051 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0050
  have p0052 :=
    @g_orim12d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0033 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wo (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0016 p0052
  have p0059 := @g_hnwcutclassltne x y D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0060 :=
    @g_ex (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0059
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D)
      (.imp (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))))
      p0015 p0060
  have p0067 := @g_hnwcutclassltne y x D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0068 :=
    @g_ex (.classMem (.cv x) D)
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))))
      p0067
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D)
      (.imp (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))))
      p0010 p0068
  have p0070 :=
    @g_eqcom (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
  have p0071 :=
    @g_biimpi
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))
      p0070
  have p0072 :=
    @g_con3i
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))
      p0071
  have p0073 :=
    @g_syl6
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0069 p0072
  have p0074 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0061 p0073
  have p0075 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wo (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0053 p0074
  have p0076 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.neg (syn_wne (.cv x) (.cv y))) p0002 p0075
  have p0077 :=
    @g_pm2_01da
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y)) p0076
  have p0078 := @g_nne (.cv x) (.cv y)
  have p0079 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.neg (syn_wne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0077 p0078
  have p0080 :=
    @g_ex (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (.cv x) (.cv y)) p0079
  exact p0080

@[expose]
noncomputable def g_hnwcutclassinjcl (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassinjcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0003 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
            (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((Wff.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp
            (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
            (.classEq B (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_R,
          or_false, not_false_eq_true])
  have p0000 := @g_simpl (.classMem B D) (.classMem C D)
  have p0001 := @g_elex B D
  have p0002 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpr (.classMem B D) (.classMem C D)
  have p0004 := @g_elex C D
  have p0005 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem B (syn_cvv))
      (.classMem C (syn_cvv)) p0002 p0005
  have p0007 := @g_eleq1 (.cv x) B D
  have p0008 := @g_biid (.classMem (.cv y) D)
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0007 p0009
  have p0011 := @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0012 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwniso D)
  have p0013 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)))
      p0011 p0012
  have p0014 :=
    @g_eqeq1d (.classEq (.cv x) B) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) p0013
  have p0015 := @g_id (.classEq (.cv x) B)
  have p0016 := @g_eqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv x) B)
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0014 p0016
  have p0018 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem (.cv y) D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y)))
      p0010 p0017
  have p0019 := @g_biid (.classMem B D)
  have p0020 := @g_a1i (syn_wb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0019
  have p0021 := @g_eleq1 (.cv y) C D
  have p0022 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0020 p0021
  have p0023 := @g_hnwcutcodeeq3 (.cv y) C D R dv_cache_0002
  have p0024 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C) (syn_chwniso D)
  have p0025 :=
    @g_syl (.classEq (.cv y) C)
      (.classEq (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      p0023 p0024
  have p0026 :=
    @g_eqeq2d (.classEq (.cv y) C) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) p0025
  have p0027 := @g_id (.classEq (.cv y) C)
  have p0028 := @g_eqeq2d (.classEq (.cv y) C) (.cv y) C B p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv y) C)
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      (.classEq B (.cv y)) (.classEq B C) p0026 p0028
  have p0030 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem B D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y)))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))
      p0022 p0029
  have p0031 := @g_hnwcutclassinj x y D R dv_cache_0003 hyp_hnwcutclassinjcl_1
  have p0032 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
          (.classEq (.cv x) (.cv y))))
      (.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y))))
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))
      x y B C (syn_cvv) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0018 p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))
      p0006 p0032
  have p0034 :=
    @g_pm2_43i (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))
      p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutmapf1 (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapf1_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : r ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_D,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0006 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnwcutmap R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_chnwcutmap R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_r_not_D, fresh_r_not_R, or_false, not_false_eq_true])
  have p0000 := @g_hnwcutmapf D R dv_cache_0001 hyp_hnwcutmapf1_1
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0002 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0003 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0002 p0003
  have p0005 := @g_pw12argcl (.cv q) D
  have p0006 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0001 p0007
  have p0013 := @g_hnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapf1_1
  have p0014 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))
      p0004 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))
      p0001 p0014
  have p0016 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_cfv (syn_chnwcutmap R D) (.cv q))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) p0015
  have p0017 :=
    @g_simpr
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0018 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
      (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)) p0016
      p0017
  have p0021 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0002 p0021
  have p0023 := @g_hnwcutmapval D R r dv_cache_0001 hyp_hnwcutmapf1_1
  have p0024 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv r))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)))
      p0022 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv r))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)))
      p0001 p0024
  have p0026 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
      (syn_cfv (syn_chnwcutmap R D) (.cv r))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)) p0018
      p0025
  have p0033 :=
    @g_simpld
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0001 p0033
  have p0039 := @g_pw12argcl (.cv r) D
  have p0040 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) D)
        (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))))
      p0022 p0039
  have p0041 :=
    @g_simpld
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0001 p0041
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @g_hnwcutclassinjcl (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) D R
      dv_cache_0001 hyp_hnwcutmapf1_1
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D)
        (.classMem (syn_cuni (syn_cuni (.cv r))) D))
      (.imp (.classEq
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)))
        (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))))
      p0043 p0044
  have p0046 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)))
      (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0026 p0045
  have p0047 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0046
  have p0048 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r))))
      p0047
  have p0049 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0008 p0048
  have p0056 :=
    @g_simprd
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0040
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0001 p0056
  have p0058 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0057
  have p0059 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
        (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))))
      (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @g_ex
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @g_ralrimivva (syn_wbr R (syn_cwe) D)
      (.imp (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)))
      q r (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cpw1 D)) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0060
  have p0062 := Nominal.mp hyp_hnwcutmapf1_1 p0061
  have p0063 :=
    @g_pm3_2i (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
      (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp
            (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
              (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0000 p0062
  have p0064 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_chnwcutmap R D) dv_cache_0006
      dv_cache_0002 dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0065_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
        (syn_wa (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
          (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp
                (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
                  (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnwcutmap syn_cmpt
          syn_cpw1 syn_cec syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_csn
          syn_chnwcutcode syn_cuni syn_chwniso syn_chnord syn_cqs syn_chwcn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0064
  have p0065 :=
    @g_mpbir (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
      (syn_wa (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
        (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp
              (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
                (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0063 p0065_e01_recanon
  exact p0065

@[expose]
noncomputable def g_hnqmap1exg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnqmap1 A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnqmap1 A))
  have p0001 := @g_hwnisoexg A
  have p0002 := @g_imageexg (syn_chwniso A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))
      (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv)) p0001 p0002
  have p0004 := @g_hwcnexg A
  have p0005 := @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_resexg (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv))
        (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)))
      (.classMem (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_cvv))
      p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnqmap1 A)
      (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_cvv) p0000
      p0009
  exact p0010

@[expose]
noncomputable def g_hnqmap1fn (A : Class)
    (hyp_hnqmap1fn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) :=
  by
  have p0000 := @g_hwnisoexg A
  have p0001 := Nominal.mp hyp_hnqmap1fn_1 p0000
  have p0002 := @g_wppimagefn (syn_chwniso A) p0001
  have p0003 := @g_ssv (syn_cpw1 (syn_chwcn A))
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_chwniso A)) (syn_cvv))
      (syn_wss (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0002 p0003
  have p0005 := @g_fnssres (syn_cvv) (syn_cpw1 (syn_chwcn A)) (syn_cimage (syn_chwniso A))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (syn_chnqmap1 A))
  have p0008 :=
    @g_fneq1i (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
      (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) p0007
  have p0009 :=
    @g_mpbir (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
      (syn_wfn (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)))
        (syn_cpw1 (syn_chwcn A)))
      p0006 p0008
  exact p0009

@[expose]
noncomputable def g_hnqmap1val (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (hyp_hnqmap1val_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso A)))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_csn (.cv u))).fv ((syn_chwniso A)).fv := by
    exact
      (show Disjoint ((syn_csn (.cv u))).fv ((syn_chwniso A)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso];
          exact
            (show Disjoint (((Class.cv u)).fv) ((A).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ u } : Finset Var)) ((A).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show u ∉ (A).fv from (by exact dv_A_u))))))))
  have p0000 := (Nominal.classEqRefl (syn_chnqmap1 A))
  have p0001 :=
    @g_fveq1i (syn_csn (.cv u)) (syn_chnqmap1 A)
      (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) p0000
  have p0002 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0003 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0002
  have p0004 :=
    @g_fvres (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)) (syn_cimage (syn_chwniso A))
  have p0005 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)))
          (syn_csn (.cv u))) (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u))))
      p0003 p0004
  have p0006 :=
    @g_syl5eq (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
      (syn_cfv (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)))
        (syn_csn (.cv u)))
      (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u))) p0001 p0005
  have p0007 := @g_hwnisoexg A
  have p0008 := Nominal.mp hyp_hnqmap1val_1 p0007
  have p0009 := @g_snex (.cv u)
  have p0010 := @g_wppfvimage (syn_csn (.cv u)) (syn_chwniso A) dv_cache_0001 p0008 p0009
  have p0011 := (Nominal.classEqRefl (syn_cec (.cv u) (syn_chwniso A)))
  have p0012 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u)))
      (syn_cima (syn_chwniso A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)) p0010
      p0011
  have p0013 :=
    @g_syl6eq (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
      (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u)))
      (syn_cec (.cv u) (syn_chwniso A)) p0006 p0012
  exact p0013

@[expose]
noncomputable def g_hnqmap1f (A : Class)
    (hyp_hnqmap1f_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_q, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0004 :
    u ∉ ((Wff.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have p0000 := @g_hnqmap1fn A hyp_hnqmap1f_1
  have p0002 := @g_elpw1 u (.cv q) (syn_chwcn A) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u)))
  have p0004 := @g_fveq2 (.cv q) (syn_csn (.cv u)) (syn_chnqmap1 A)
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u))))
      (.classEq (.cv q) (syn_csn (.cv u)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))))
      p0003 p0004
  have p0006 := @g_hnqmap1val u A dv_cache_0003 hyp_hnqmap1f_1
  have p0007 := @g_hwnisoclasselhnord u A dv_cache_0003 hyp_hnqmap1f_1
  have p0008 :=
    @g_eqeltrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))
      (syn_chnord A) p0006 p0007
  have p0009 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (.cv u))) p0008
  have p0010 :=
    @g_eqeltrd
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u))))
      (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
      (syn_chnord A) p0005 p0009
  have p0011 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (.cv u)))
      (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) u (syn_chwcn A)
      dv_cache_0004 p0010
  have p0012 :=
    @g_sylbi (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_wrex u (syn_chwcn A) (.classEq (.cv q) (syn_csn (.cv u))))
      (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) p0002 p0011
  have p0013 :=
    @g_rgen (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) q
      (syn_cpw1 (syn_chwcn A)) p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
      (syn_wral q (syn_cpw1 (syn_chwcn A))
        (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)))
      p0000 p0013
  have p0015 :=
    @g_fnfvrnss q (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A) dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
      (syn_wss (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) p0000 p0016
  have p0018 :=
    (Nominal.biimpRefl (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)))
  have p0019 :=
    @g_mpbir (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
        (syn_wss (syn_crn (syn_chnqmap1 A)) (syn_chnord A)))
      p0017 p0018
  exact p0019

@[expose]
noncomputable def g_hnqmap1rn (A : Class)
    (hyp_hnqmap1rn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((syn_chwcn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_z, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0004 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_csn (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_u,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0007 :
    q ∉ ((Wff.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_u, fresh_q_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    u ∉
      ((syn_wrex q (syn_cpw1 (syn_chwcn A))
          (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_A, fresh_u_ne_z,
          fresh_u_ne_q, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_z_not_A, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_z_not_A, not_false_eq_true])
  have dv_cache_0014 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have p0000 := @g_hnqmap1f A hyp_hnqmap1rn_1
  have p0001 := (Nominal.classEqRefl (syn_chnord A))
  have p0002 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (.cv z) p0001
  have p0003 :=
    @g_biimpi (.classMem (.cv z) (syn_chnord A))
      (.classMem (.cv z) (syn_cqs (syn_chwcn A) (syn_chwniso A))) p0002
  have p0004 :=
    @g_elqsi u (syn_chwcn A) (.cv z) (syn_chwniso A) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0005 :=
    @g_syl (.classMem (.cv z) (syn_chnord A))
      (.classMem (.cv z) (syn_cqs (syn_chwcn A) (syn_chwniso A)))
      (syn_wrex u (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))))
      p0003 p0004
  have p0006 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0007 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0006
  have p0008 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))) p0007
  have p0009 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))
  have p0010 := @g_hnqmap1val u A dv_cache_0004 hyp_hnqmap1rn_1
  have p0011 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))) p0010
  have p0012 :=
    @g_eqtr4d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))))
      (.cv z) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) p0009 p0011
  have p0013 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))) p0008 p0012
  have p0014 := @g_fveq2 (.cv q) (syn_csn (.cv u)) (syn_chnqmap1 A)
  have p0015 :=
    @g_eqeq2d (.classEq (.cv q) (syn_csn (.cv u))) (syn_cfv (syn_chnqmap1 A) (.cv q))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (.cv z) p0014
  have p0016 :=
    @g_rspcev (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))) q (syn_csn (.cv u))
      (syn_cpw1 (syn_chwcn A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0015
  have p0017 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wa (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      p0013 p0016
  have p0018 :=
    @g_rexlimiva (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      u (syn_chwcn A) dv_cache_0008 p0017
  have p0019 :=
    @g_syl (.classMem (.cv z) (syn_chnord A))
      (syn_wrex u (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      p0005 p0018
  have p0020 :=
    @g_rgen
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      z (syn_chnord A) p0019
  have p0021 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (syn_wral z (syn_chnord A) (syn_wrex q (syn_cpw1 (syn_chwcn A))
          (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))))
      p0000 p0020
  have p0022 :=
    @g_dffo3 q z (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A) dv_cache_0006
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0023 :=
    @g_mpbir (syn_wfo (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (syn_wa (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
        (syn_wral z (syn_chnord A) (syn_wrex q (syn_cpw1 (syn_chwcn A))
            (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))))
      p0021 p0022
  have p0024 := @g_dffo2 (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A)
  have p0025 :=
    @g_mpbi (syn_wfo (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (syn_wa (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
        (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A)))
      p0023 p0024
  have p0026 :=
    @g_simpri (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) p0025
  exact p0026

@[expose]
noncomputable def g_brlnker (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr X (syn_clnker R) Y) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnker R))
  have p0001 := @g_breqi X Y (syn_clnker R) (syn_cin R (syn_ccnv R)) p0000
  have p0002 := @g_brin X Y R (syn_ccnv R)
  have p0003 := @g_brcnv X Y R
  have p0004 := @g_anbi2i (syn_wbr X (syn_ccnv R) Y) (syn_wbr Y R X) (syn_wbr X R Y) p0003
  have p0005 :=
    @g_bitri (syn_wbr X (syn_cin R (syn_ccnv R)) Y)
      (syn_wa (syn_wbr X R Y) (syn_wbr X (syn_ccnv R) Y))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0002 p0004
  have p0006 :=
    @g_bitri (syn_wbr X (syn_clnker R) Y) (syn_wbr X (syn_cin R (syn_ccnv R)) Y)
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0001 p0005
  exact p0006

@[expose]
noncomputable def g_lnkerex (R : Class)
    (hyp_lnkerex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_clnker R) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnker R))
  have p0001 := @g_cnvex R hyp_lnkerex_1
  have p0002 := @g_inex R (syn_ccnv R) hyp_lnkerex_1 p0001
  have p0003 := @g_eqeltri (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_ellnquo (x : Var) (A : Class) (B : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_ellnquo_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem B (syn_clnquo R A))
        (syn_wrex x A (.classEq B (syn_cec (.cv x) (syn_clnker R))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_clnker R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, dv_R_x,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_clnquo R A))
  have p0001 := @g_eleq2i (syn_clnquo R A) (syn_cqs A (syn_clnker R)) B p0000
  have p0002 :=
    @g_elqs x A B (syn_clnker R) dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_ellnquo_1
  have p0003 :=
    @g_bitri (.classMem B (syn_clnquo R A)) (.classMem B (syn_cqs A (syn_clnker R)))
      (syn_wrex x A (.classEq B (syn_cec (.cv x) (syn_clnker R)))) p0001 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lefinssvvk :
    Nominal.NPrf (syn_wss (syn_clefin) (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : w ≠ x := by exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0002 : w ≠ y := by
    clear dv_cache_0001
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0003 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lefin x y z w
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opkabssvvki (syn_wrex w (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv w)))) x
      y z (syn_clefin) dv_cache_0004 dv_cache_0005 p0000
  exact p0001

@[expose]
noncomputable def g_ltfinssvvk :
    Nominal.NPrf (syn_wss (syn_cltfin) (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let m : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : m ≠ n := by exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0002 : m ≠ p := by
    clear dv_cache_0001
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0003 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0004 : n ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0005 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0006 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0007 : x ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ m from (by exact fresh_x_ne_m))
  have dv_cache_0008 : x ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ n from (by exact fresh_x_ne_n))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ltfin x m n p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opkabssvvki
      (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc)
          (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))))
      x m n (syn_cltfin) dv_cache_0007 dv_cache_0008 p0000
  exact p0001

@[expose]
noncomputable def g_ltfinunidkssvvk :
    Nominal.NPrf
      (syn_wss (syn_cun (syn_cltfin) (syn_cidk)) (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  have p0000 := @g_ltfinssvvk
  have p0001 := @g_idkssvvk
  have p0002 :=
    @g_unssi (syn_cltfin) (syn_cidk) (syn_cxpk (syn_cvv) (syn_cvv)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ellefinunidk (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk)))
          (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) :=
  by
  have p0000 := @g_elun (syn_copk A B) (syn_cltfin) (syn_cidk)
  have p0001 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk)))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cidk))))
      (syn_wa (.classMem A V) (.classMem B W)) p0000
  have p0002 := @g_opkelidkg A B V W
  have p0003 :=
    @g_orbi2d (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_copk A B) (syn_cidk)) (.classEq A B)
      (.classMem (syn_copk A B) (syn_cltfin)) p0002
  have p0004 :=
    @g_bitrd (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk)))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cidk)))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_lefinlteq0 (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_V, fresh_x_not_B, fresh_x_not_W,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_simp1 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0001 := @g_simp2 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0002 :=
    @g_jca (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem A V)
      (.classMem B W) p0000 p0001
  have p0003 := @g_opklefing x A B V W dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_syl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (syn_wa (.classMem A V) (.classMem B W))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))))
      p0002 p0003
  have p0005 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq B (syn_cplc A (.cv x)))
  have p0006 :=
    @g_simpl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classMem (.cv x) (syn_cnnc))
  have p0007 := @g_simp3 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0008 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classEq A (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
          (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))))
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq A (syn_c0)) p0005 p0008
  have p0010 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq B (syn_cplc A (.cv x)))
  have p0012 := @g_addccom A (.cv x)
  have p0013 :=
    @g_a1i (.classEq (syn_cplc A (.cv x)) (syn_cplc (.cv x) A))
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      p0012
  have p0017 :=
    @g_addceq2d
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      A (syn_c0) (.cv x) p0008
  have p0018 :=
    @g_eqtrd
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (syn_cplc A (.cv x)) (syn_cplc (.cv x) A) (syn_cplc (.cv x) (syn_c0)) p0013 p0017
  have p0019 := @g_addcnul1 (.cv x)
  have p0020 :=
    @g_a1i (.classEq (syn_cplc (.cv x) (syn_c0)) (syn_c0))
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      p0019
  have p0021 :=
    @g_eqtrd
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (syn_cplc A (.cv x)) (syn_cplc (.cv x) (syn_c0)) (syn_c0) p0018 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
          (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))))
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq (syn_cplc A (.cv x)) (syn_c0)) p0005 p0021
  have p0023 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
          (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))))
      B (syn_cplc A (.cv x)) (syn_c0) p0010 p0022
  have p0024 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
          (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))))
      B (syn_c0) p0023
  have p0025 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
          (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))))
      A (syn_c0) B p0009 p0024
  have p0026 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq B (syn_cplc A (.cv x))) (.classEq A B) p0025
  have p0027 :=
    @g_rexlimdva (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classEq B (syn_cplc A (.cv x))) (.classEq A B) x (syn_cnnc) dv_cache_0003
      dv_cache_0004 p0026
  have p0028 :=
    @g_sylbid (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.classEq A B) p0004 p0027
  have p0029 :=
    @g_simpl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classEq A B)
  have p0031 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B))
      (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem A V)
      p0029 p0000
  have p0032 := @g_lefinrflx A V
  have p0033 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B))
      (.classMem A V) (.classMem (syn_copk A A) (syn_clefin)) p0031 p0032
  have p0034 :=
    @g_simpr (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classEq A B)
  have p0035 := @g_opkeq2 A B A
  have p0036 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B))
      (.classEq A B) (.classEq (syn_copk A A) (syn_copk A B)) p0034 p0035
  have p0037 :=
    @g_eleq1d
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B))
      (syn_copk A A) (syn_copk A B) (syn_clefin) p0036
  have p0038 :=
    @g_mpbid
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B))
      (.classMem (syn_copk A A) (syn_clefin)) (.classMem (syn_copk A B) (syn_clefin))
      p0033 p0037
  have p0039 :=
    @g_ex (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)
      (.classMem (syn_copk A B) (syn_clefin)) p0038
  have p0040 :=
    @g_impbid (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B) p0028 p0039
  exact p0040

@[expose]
noncomputable def g_lefinlteqall (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_clefin))
          (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 := @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
  have p0001 := @g_simpl (.classMem A V) (.classMem B W)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (syn_wa (.classMem A V) (.classMem B W)) (.classMem A V) p0000 p0001
  have p0004 := @g_simpr (.classMem A V) (.classMem B W)
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (syn_wa (.classMem A V) (.classMem B W)) (.classMem B W) p0000 p0004
  have p0006 := @g_simpr (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
  have p0007 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)) p0002 p0005 p0006
  have p0008 := @g_lefinlteq A B V W
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0007 p0008
  have p0010 :=
    @g_ex (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0009
  have p0011 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (syn_wa (.classMem A V) (.classMem B W)) (.classMem A V) p0011 p0001
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (syn_wa (.classMem A V) (.classMem B W)) (.classMem B W) p0011 p0004
  have p0017 :=
    @g_simpr (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0018 := @g_nne A (syn_c0)
  have p0019 :=
    @g_a1i (syn_wb (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)))
      (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) p0018
  have p0020 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)) p0017 p0019
  have p0021 :=
    @g_n_3jca
      (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.classMem A V) (.classMem B W) (.classEq A (syn_c0)) p0013 p0016 p0020
  have p0022 := @g_lefinlteq0 A B V W
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B)) p0021 p0022
  have p0026 := @g_opkltfing x A B V W dv_cache_0001 dv_cache_0002
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (syn_wa (.classMem A V) (.classMem B W))
      (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      p0011 p0026
  have p0028 :=
    @g_simpl (syn_wne A (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
  have p0029 :=
    @g_a1i
      (.imp (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
        (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) p0028
  have p0030 :=
    @g_sylbid
      (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.classMem (syn_copk A B) (syn_cltfin))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      (syn_wne A (syn_c0)) p0027 p0029
  have p0031 :=
    @g_con3d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.classMem (syn_copk A B) (syn_cltfin)) (syn_wne A (syn_c0)) p0030
  have p0032 :=
    @g_mpd (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.neg (syn_wne A (syn_c0))) (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0017
      p0031
  have p0033 := @g_biorf (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.neg (.classMem (syn_copk A B) (syn_cltfin)))
      (syn_wb (.classEq A B) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0032 p0033
  have p0035 :=
    @g_bitrd (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))))
      (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B)
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0023 p0034
  have p0036 :=
    @g_ex (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0035
  have p0037 :=
    @g_pm2_61d (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0010 p0036
  exact p0037

@[expose]
noncomputable def g_lefinunidk :
    Nominal.NPrf (.classEq (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_clefin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_clefin)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cun (syn_cltfin) (syn_cidk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cun (syn_cltfin) (syn_cidk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_lefinssvvk
  have p0001 := @g_ltfinunidkssvvk
  have p0002 := @g_tru
  have p0003 := @g_vex x
  have p0004 := @g_a1i (.classMem (.cv x) (syn_cvv)) syn_wtru p0003
  have p0005 := @g_vex y
  have p0006 := @g_a1i (.classMem (.cv y) (syn_cvv)) syn_wtru p0005
  have p0007 :=
    @g_jca syn_wtru (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0004
      p0006
  have p0008 := Nominal.mp p0002 p0007
  have p0009 := @g_lefinlteqall (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0018 := @g_ellefinunidk (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0019 := Nominal.mp p0008 p0018
  have p0020 :=
    @g_bitr4i (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
      (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_cltfin)) (.classEq (.cv x) (.cv y)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cun (syn_cltfin) (syn_cidk))) p0010 p0019
  have p0021 :=
    @g_eqrelkriiv x y (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0020
  exact p0021

@[expose]
noncomputable def g_lefinex : Nominal.NPrf (.classMem (syn_clefin) (syn_cvv)) :=
  by
  have p0000 := @g_lefinunidk
  have p0001 := @g_ltfinex
  have p0002 := @g_idkex
  have p0003 := @g_unex (syn_cltfin) (syn_cidk) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_kqrelbrg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B V) (.classMem C W))
        (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_copk B C) A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_copk B C) A)).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_copk B C) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))
      (syn_cop B C) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_cop B C)
          (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))))
      (syn_wa (.classMem B V) (.classMem C W)) p0001
  have p0003 := @g_opkeq1 (.cv x) B (.cv y)
  have p0004 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) (.cv y)) (syn_copk B (.cv y)) A p0003
  have p0005 := @g_opkeq2 (.cv y) C B
  have p0006 := @g_eleq1d (.classEq (.cv y) C) (syn_copk B (.cv y)) (syn_copk B C) A p0005
  have p0007 :=
    @g_opelopabg (.classMem (syn_copk (.cv x) (.cv y)) A)
      (.classMem (syn_copk B (.cv y)) A) (.classMem (syn_copk B C) A) x y B C V W
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003 p0004 p0006
  have p0008 :=
    @g_bitrd (syn_wa (.classMem B V) (.classMem C W))
      (.classMem (syn_cop B C) (syn_ckqrel A))
      (.classMem (syn_cop B C) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)))
      (.classMem (syn_copk B C) A) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_kqlefinbr (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr A (syn_ckqrel (syn_clefin)) B)
          (.classMem (syn_copk A B) (syn_clefin)))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A (syn_ckqrel (syn_clefin)) B))
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr A (syn_ckqrel (syn_clefin)) B)
        (.classMem (syn_cop A B) (syn_ckqrel (syn_clefin))))
      (syn_wa (.classMem A V) (.classMem B W)) p0000
  have p0002 := @g_kqrelbrg (syn_clefin) A B V W
  have p0003 :=
    @g_bitrd (syn_wa (.classMem A V) (.classMem B W))
      (syn_wbr A (syn_ckqrel (syn_clefin)) B)
      (.classMem (syn_cop A B) (syn_ckqrel (syn_clefin)))
      (.classMem (syn_copk A B) (syn_clefin)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_lefintrnn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B C) (syn_clefin)))
          (.classMem (syn_copk A C) (syn_clefin)))) :=
  by
  have p0000 :=
    @g_simpr
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0001 :=
    @g_simpr (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk B C) (syn_clefin))
  have p0002 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
      (.classMem (syn_copk B C) (syn_clefin)) p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0004 :=
    @g_simp2 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0005 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem B (syn_cnnc)) p0003 p0004
  have p0007 :=
    @g_simp3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0008 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem C (syn_cnnc)) p0003 p0007
  have p0009 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)) p0005 p0008
  have p0010 := @g_lenltfin B C
  have p0011 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wb (.classMem (syn_copk B C) (syn_clefin))
        (.neg (.classMem (syn_copk C B) (syn_cltfin))))
      p0009 p0010
  have p0012 :=
    @g_biimpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk B C) (syn_clefin))
      (.neg (.classMem (syn_copk C B) (syn_cltfin))) p0011
  have p0013 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk B C) (syn_clefin))
      (.neg (.classMem (syn_copk C B) (syn_cltfin))) p0002 p0012
  have p0015 :=
    @g_simpl (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk B C) (syn_clefin))
  have p0016 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
      (.classMem (syn_copk A B) (syn_clefin)) p0000 p0015
  have p0018 :=
    @g_simp1 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0019 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem A (syn_cnnc)) p0003 p0018
  have p0020 := @g_elex A (syn_cnnc)
  have p0021 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0019 p0020
  have p0025 := @g_elex B (syn_cnnc)
  have p0026 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0005 p0025
  have p0027 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0021 p0026
  have p0028 := @g_lefinlteqall A B (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))
      p0027 p0028
  have p0030 :=
    @g_biimpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0029
  have p0031 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0016 p0030
  have p0041 :=
    @g_n_3jca
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) p0008
      p0019 p0005
  have p0042 := @g_ltfintr C A B
  have p0043 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_w3a (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk C A) (syn_cltfin))
          (.classMem (syn_copk A B) (syn_cltfin))) (.classMem (syn_copk C B) (syn_cltfin)))
      p0041 p0042
  have p0044 :=
    @g_exp3a
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cltfin))
      (.classMem (syn_copk C B) (syn_cltfin)) p0043
  have p0045 :=
    @g_com23
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cltfin))
      (.classMem (syn_copk C B) (syn_cltfin)) p0044
  have p0046 := @g_opkeq2 A B C
  have p0047 := @g_eleq1d (.classEq A B) (syn_copk C A) (syn_copk C B) (syn_cltfin) p0046
  have p0048 :=
    @g_biimpd (.classEq A B) (.classMem (syn_copk C A) (syn_cltfin))
      (.classMem (syn_copk C B) (syn_cltfin)) p0047
  have p0049 :=
    @g_a1i
      (.imp (.classEq A B) (.imp (.classMem (syn_copk C A) (syn_cltfin))
          (.classMem (syn_copk C B) (syn_cltfin))))
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      p0048
  have p0050 :=
    @g_jaod
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_cltfin))
      (.imp (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)))
      (.classEq A B) p0045 p0049
  have p0051 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))
      (.imp (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)))
      p0031 p0050
  have p0052 :=
    @g_con3d
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin))
      p0051
  have p0053 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.neg (.classMem (syn_copk C B) (syn_cltfin)))
      (.neg (.classMem (syn_copk C A) (syn_cltfin))) p0013 p0052
  have p0060 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) p0019 p0008
  have p0061 := @g_lenltfin A C
  have p0062 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wb (.classMem (syn_copk A C) (syn_clefin))
        (.neg (.classMem (syn_copk C A) (syn_cltfin))))
      p0060 p0061
  have p0063 :=
    @g_biimprd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.classMem (syn_copk A C) (syn_clefin))
      (.neg (.classMem (syn_copk C A) (syn_cltfin))) p0062
  have p0064 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B C) (syn_clefin))))
      (.neg (.classMem (syn_copk C A) (syn_cltfin)))
      (.classMem (syn_copk A C) (syn_clefin)) p0053 p0063
  have p0065 :=
    @g_ex
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
      (.classMem (syn_copk A C) (syn_clefin)) p0064
  exact p0065


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lefinantinn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin))) (.classEq A B))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wne A (syn_c0))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0002 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc))
      p0001 p0002
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem A (syn_cnnc)) p0000 p0003
  have p0007 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc))
      p0001 p0007
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem B (syn_cnnc)) p0000 p0008
  have p0010 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wne A (syn_c0))
  have p0011 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne A (syn_c0)) p0004 p0009
      p0010
  have p0012 := @g_ltfintri A B
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne A (syn_c0)))
      (syn_w3o (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)
        (.classMem (syn_copk B A) (syn_cltfin)))
      p0011 p0012
  have p0015 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0016 :=
    @g_simpr (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk B A) (syn_clefin))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      (.classMem (syn_copk B A) (syn_clefin)) p0015 p0016
  have p0021 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) p0007 p0002
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))) p0001 p0021
  have p0023 := @g_lenltfin B A
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)))
      (syn_wb (.classMem (syn_copk B A) (syn_clefin))
        (.neg (.classMem (syn_copk A B) (syn_cltfin))))
      p0022 p0023
  have p0025 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem (syn_copk B A) (syn_clefin))
      (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0024
  have p0026 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem (syn_copk B A) (syn_clefin))
      (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0017 p0025
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0000 p0026
  have p0028 :=
    @g_pm2_21d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) p0027
  have p0029 := @g_id (.classEq A B)
  have p0030 :=
    @g_a1i (.imp (.classEq A B) (.classEq A B))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      p0029
  have p0033 :=
    @g_simpl (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk B A) (syn_clefin))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      (.classMem (syn_copk A B) (syn_clefin)) p0015 p0033
  have p0036 := @g_lenltfin A B
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (.neg (.classMem (syn_copk B A) (syn_cltfin))))
      p0001 p0036
  have p0038 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0037
  have p0039 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0034 p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0000 p0039
  have p0041 :=
    @g_pm2_21d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (.classMem (syn_copk B A) (syn_cltfin)) (.classEq A B) p0040
  have p0042 :=
    @g_n_3jaod
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) (.classEq A B)
      (.classMem (syn_copk B A) (syn_cltfin)) p0028 p0030 p0041
  have p0043 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)))
      (syn_w3o (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)
        (.classMem (syn_copk B A) (syn_cltfin)))
      (.classEq A B) p0013 p0042
  have p0044 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wne A (syn_c0)) (.classEq A B) p0043
  have p0045 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.neg (syn_wne A (syn_c0)))
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem (syn_copk A B) (syn_clefin)) p0045 p0034
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem A (syn_cnnc)) p0045 p0003
  have p0055 := @g_elex A (syn_cnnc)
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0054 p0055
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.classMem B (syn_cnnc)) p0045 p0008
  have p0062 := @g_elex B (syn_cnnc)
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0061 p0062
  have p0064 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.neg (syn_wne A (syn_c0)))
  have p0065 := @g_nne A (syn_c0)
  have p0066 :=
    @g_a1i (syn_wb (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      p0065
  have p0067 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)) p0064 p0066
  have p0068 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classEq A (syn_c0)) p0056 p0063
      p0067
  have p0069 := @g_lefinlteq0 A B (syn_cvv) (syn_cvv)
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classEq A (syn_c0)))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B)) p0068 p0069
  have p0071 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))))
      (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B) p0049 p0070
  have p0072 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (.neg (syn_wne A (syn_c0))) (.classEq A B) p0071
  have p0073 :=
    @g_pm2_61d
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin))))
      (syn_wne A (syn_c0)) (.classEq A B) p0044 p0072
  have p0074 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      (.classEq A B) p0073
  exact p0074

@[expose]
noncomputable def g_lefinconnexnn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wo (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_clefin)))) :=
  by
  have p0000 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0001 := @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0004 := @g_elex A (syn_cnnc)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cvv)) (.classMem A (syn_cvv)) p0002 p0005
  have p0007 := @g_ltlefin B A (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem A (syn_cvv)))
      (.imp (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin)))
      p0006 p0007
  have p0009 :=
    @g_olc (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A B) (syn_clefin))
  have p0010 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin))
      (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      p0008 p0009
  have p0011 := @g_lenltfin A B
  have p0012 :=
    @g_biimprd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0011
  have p0013 :=
    @g_orc (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))
  have p0014 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.neg (.classMem (syn_copk B A) (syn_cltfin)))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      p0012 p0013
  have p0015 :=
    @g_pm2_61d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_cltfin))
      (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      p0010 p0014
  exact p0015

@[expose]
noncomputable def g_finleor :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : y ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : z ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @g_tru
  have p0001 := @g_lefinex
  have p0002 := @g_kqrelex (syn_clefin) p0001
  have p0003 := @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) syn_wtru p0002
  have p0004 := @g_nncex
  have p0005 := @g_a1i (.classMem (syn_cnnc) (syn_cvv)) syn_wtru p0004
  have p0006 := @g_simpr syn_wtru (.classMem (.cv x) (syn_cnnc))
  have p0007 := @g_elex (.cv x) (syn_cnnc)
  have p0008 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))
      (.classMem (.cv x) (syn_cvv)) p0006 p0007
  have p0009 := @g_lefinrflx (.cv x) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cvv))
      (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin)) p0008 p0009
  have p0017 :=
    @g_jca (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cvv))
      (.classMem (.cv x) (syn_cvv)) p0008 p0008
  have p0018 := @g_kqlefinbr (.cv x) (.cv x) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
      (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv x))
        (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin)))
      p0017 p0018
  have p0020 :=
    @g_mpbird (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc)))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv x))
      (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin)) p0010 p0019
  have p0021 :=
    @g_simp3 syn_wtru
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0022 :=
    @g_simpl (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
  have p0023 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) p0021 p0022
  have p0024 :=
    @g_simp2 syn_wtru
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0025 :=
    @g_simp1 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
      (.classMem (.cv z) (syn_cnnc))
  have p0026 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (.classMem (.cv x) (syn_cnnc)) p0024 p0025
  have p0028 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0026 p0007
  have p0030 :=
    @g_simp2 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
      (.classMem (.cv z) (syn_cnnc))
  have p0031 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (.classMem (.cv y) (syn_cnnc)) p0024 p0030
  have p0032 := @g_elex (.cv y) (syn_cnnc)
  have p0033 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_jca
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0028 p0033
  have p0035 := @g_kqlefinbr (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
      (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)))
      p0034 p0035
  have p0037 :=
    @g_mpbid
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0023 p0036
  have p0039 :=
    @g_simpr (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
  have p0040 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0021 p0039
  have p0047 :=
    @g_simp3 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
      (.classMem (.cv z) (syn_cnnc))
  have p0048 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (.classMem (.cv z) (syn_cnnc)) p0024 p0047
  have p0049 := @g_elex (.cv z) (syn_cnnc)
  have p0050 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) (syn_cvv)) p0048 p0049
  have p0051 :=
    @g_jca
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0033 p0050
  have p0052 := @g_kqlefinbr (.cv y) (.cv z) (syn_cvv) (syn_cvv)
  have p0053 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)))
      (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
        (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)))
      p0051 p0052
  have p0054 :=
    @g_mpbid
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)) p0040 p0053
  have p0055 :=
    @g_jca
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)) p0037 p0054
  have p0057 := @g_lefintrnn (.cv x) (.cv y) (.cv z)
  have p0058 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
        (.classMem (.cv z) (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
          (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)))
        (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)))
      p0024 p0057
  have p0059 :=
    @g_mpd
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
        (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)))
      (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)) p0055 p0058
  have p0070 :=
    @g_jca
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv x) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0028 p0050
  have p0071 := @g_kqlefinbr (.cv x) (.cv z) (syn_cvv) (syn_cvv)
  have p0072 :=
    @g_syl
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv z) (syn_cvv)))
      (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))
        (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)))
      p0070 p0071
  have p0073 :=
    @g_mpbird
      (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
          (.classMem (.cv z) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))
      (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)) p0059 p0072
  have p0074 :=
    @g_simp3 syn_wtru
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0075 :=
    @g_simpl (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0076 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) p0074 p0075
  have p0077 :=
    @g_simp2 syn_wtru
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0078 := @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0079 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv x) (syn_cnnc)) p0077 p0078
  have p0081 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0079 p0007
  have p0083 := @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0084 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv y) (syn_cnnc)) p0077 p0083
  have p0086 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0084 p0032
  have p0087 :=
    @g_jca
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0081 p0086
  have p0089 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
      (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)))
      p0087 p0035
  have p0090 :=
    @g_mpbid
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0076 p0089
  have p0092 :=
    @g_simpr (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0093 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) p0074 p0092
  have p0104 :=
    @g_jca
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0086 p0081
  have p0105 := @g_kqlefinbr (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0106 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
      (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)))
      p0104 p0105
  have p0107 :=
    @g_mpbid
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0093 p0106
  have p0108 :=
    @g_jca
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0090 p0107
  have p0110 := @g_lefinantinn (.cv x) (.cv y)
  have p0111 :=
    @g_syl
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
          (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) (.classEq (.cv x) (.cv y)))
      p0077 p0110
  have p0112 :=
    @g_mpd
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))
      (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)))
      (.classEq (.cv x) (.cv y)) p0108 p0111
  have p0113 :=
    @g_simp2 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0114 :=
    @g_simp3 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0115 :=
    @g_jca
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0113 p0114
  have p0116 := @g_lefinconnexnn (.cv x) (.cv y)
  have p0117 :=
    @g_syl
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)))
      p0115 p0116
  have p0120 :=
    @g_syl
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0113 p0007
  have p0123 :=
    @g_syl
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0114 p0032
  have p0124 :=
    @g_jca
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0120 p0123
  have p0126 :=
    @g_syl
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
      (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)))
      p0124 p0035
  have p0127 :=
    @g_biimprd
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0126
  have p0128 :=
    @g_orc (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0129 :=
    @g_syl6
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      p0127 p0128
  have p0136 :=
    @g_jca
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0123 p0120
  have p0138 :=
    @g_syl
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
      (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)))
      p0136 p0105
  have p0139 :=
    @g_biimprd
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0138
  have p0140 :=
    @g_olc (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0141 :=
    @g_syl6
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
      (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      p0139 p0140
  have p0142 :=
    @g_jaod
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
      (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0129 p0141
  have p0143 :=
    @g_mpd
      (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)))
      (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
      p0117 p0142
  have p0144_e04_recanon :
    Nominal.NPrf
      (.imp (syn_w3a syn_wtru
          (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
          (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
            (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wtru
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0112
  have p0144 :=
    @g_sod syn_wtru x y z (syn_cnnc) (syn_ckqrel (syn_clefin)) (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0003 p0005 p0020 p0073 p0144_e04_recanon p0143
  have p0145 := Nominal.mp p0000 p0144
  exact p0145


end NFChoice.DirectNominalPrf.WPPReplay

end
