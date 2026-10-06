/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppcandstrictsliceleastdndvv`. -/
@[expose]
noncomputable def gWppcandstrictsliceleastdndvv (C : Class) (D : Class) (R : Class)
    (k : Var) (m : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv)
    (dv_C_q : q ∉ C.fv) (dv_D_k : k ∉ D.fv) (dv_D_m : m ∉ D.fv) (dv_D_q : q ∉ D.fv)
    (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_R_k : k ∉ R.fv)
    (dv_R_m : m ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_m : k ≠ m) (dv_k_q : k ≠ q)
    (_dv_m_q : m ≠ q)
    (hyp_wppcandstrictsliceleastdndvv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wppcandstrictsliceleastdndvv_2 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppcandstrictsliceleastdndvv_3 : Nominal.NPrf (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (synWne (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synC0)) (synWrex m
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWral k
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k))))) :=
  by
  let proofSupport : Finset Var :=
    C.fv ∪ D.fv ∪ R.fv ∪ ({ k } : Finset Var) ∪ ({ m } : Finset Var) ∪ F.fv ∪
      ({ q } : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_ne_k : g ≠ k := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_k_ne_g : k ≠ g := Ne.symm fresh_g_ne_k
  have fresh_g_ne_m : g ≠ m := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_m_ne_g : m ≠ g := Ne.symm fresh_g_ne_m
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_q : g ≠ q := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_g : q ≠ g := Ne.symm fresh_g_ne_q
  have dv_cache_0001 : k ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_k, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0003 : g ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_D, not_false_eq_true])
  have dv_cache_0004 :
    k ∉ ((synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_k,
          dv_F_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉ ((synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_q,
          dv_F_q, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    g ∉ ((synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_g_not_C, fresh_g_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : k ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_k, not_false_eq_true])
  have dv_cache_0008 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0009 : g ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_R, not_false_eq_true])
  have dv_cache_0010 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0011 : k ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show k ≠ g from (by exact fresh_k_ne_g))
  have dv_cache_0012 : q ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show q ≠ g from (by exact fresh_q_ne_g))
  have dv_cache_0013 :
    k ∉
      ((Wff.classEq (.cv m) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, dv_k_m, dv_D_k, dv_R_k, fresh_k_ne_g,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    m ∉
      ((synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv g)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_m, dv_R_m, fresh_m_ne_g, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    m ∉ ((synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_m,
          dv_F_m, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    m ∉
      ((synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_m, dv_F_m, dv_D_m, dv_R_m,
          fresh_m_ne_g, (Ne.symm dv_k_m), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 :
    g ∉
      ((synWrex m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_not_C, fresh_g_not_F,
          fresh_g_ne_m, fresh_g_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gWppcandstrictsliceexndv C F hyp_wppcandstrictsliceleastdndvv_2
  have p0001 :=
    @gWecutcardrepleastdndv g D R k
      (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) q
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      hyp_wppcandstrictsliceleastdndvv_1 p0000 hyp_wppcandstrictsliceleastdndvv_3
  have p0002 :=
    @gId
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g)))))))
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k))))
  have p0003 :=
    @gId
      (.classEq (.cv m) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv g))))))))
  have p0004 :=
    @gBreq1d
      (.classEq (.cv m) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv g))))))))
      (.cv m)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv g)))))))
      (.cv k) (synClec) p0003
  have p0005 :=
    @gRalbidv
      (.classEq (.cv m) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv g))))))))
      (synWbr (.cv m) (synClec) (.cv k))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k))
      k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
      dv_cache_0013 p0004
  have p0006 :=
    @gRspcev
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k)))
      m
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv g)))))))
      (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g)))))))
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g)))))))
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k))))
      (synWrex m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      p0002 p0006
  have p0008 :=
    @gA1i
      (.imp (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g)))))))
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k)))) (synWrex m
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWral k
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))))
      (.classMem (.cv g) (synCpw1 (synCpw1 D))) p0007
  have p0009 :=
    @gRexlimiv
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv g)))))))
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k))))
      (synWrex m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      g (synCpw1 (synCpw1 D)) dv_cache_0017 p0008
  have p0010 :=
    @gSyl
      (synWne (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (synWrex g (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv g)))))))
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv g))))))) (synClec) (.cv k)))))
      (synWrex m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      p0001 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as
`g_wppcandstrictsliceleastextenddv`.
-/
@[expose]
noncomputable def gWppcandstrictsliceleastextenddv (z : Var) (C : Class) (k : Var)
    (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (_dv_C_m : m ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_F_k : k ∉ F.fv) (_dv_F_m : m ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_k_m : k ≠ m)
    (dv_k_z : k ≠ z) (dv_m_z : m ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k))))
        (synWa (.classMem (.cv m) (synCwppcand F C))
          (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))))) :=
  by
  have dv_cache_0001 : k ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_k_z,
          not_false_eq_true])
  have dv_cache_0002 :
    k ∉ ((synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_k,
          dv_F_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((synWbr (.cv m) (synClec) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, dv_k_m, dv_k_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_m_z), dv_C_z, dv_F_z,
          (Ne.symm dv_k_z), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpl
      (.classMem (.cv m)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
  have p0001 := @gElwppcandstrictslice C m F
  have p0002 :=
    @gBiimpi
      (.classMem (.cv m)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv m) (synCwppcand F C)) (synWbr (.cv m) (synCltc) C)) p0001
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv m)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv m) (synCwppcand F C)) (synWbr (.cv m) (synCltc) C)) p0000
      p0002
  have p0004 :=
    @gSimpld
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv m) (synCwppcand F C)) (synWbr (.cv m) (synCltc) C) p0003
  have p0005 :=
    @gSimpr
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv z) (synCwppcand F C))
  have p0006 := @gElwppcandstrictslice C z F
  have p0007 :=
    @gBiimpri
      (.classMem (.cv z)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv z) (synCwppcand F C)) (synWbr (.cv z) (synCltc) C)) p0006
  have p0008 :=
    @gEx (.classMem (.cv z) (synCwppcand F C)) (synWbr (.cv z) (synCltc) C)
      (.classMem (.cv z)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      p0007
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (.classMem (.cv z) (synCwppcand F C))
      (.imp (synWbr (.cv z) (synCltc) C) (.classMem (.cv z)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))))
      p0005 p0008
  have p0010 :=
    @gSimpl
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv z) (synCwppcand F C))
  have p0011 :=
    @gSimpr
      (.classMem (.cv m)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
  have p0012 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
      p0010 p0011
  have p0013 := @gId (.classEq (.cv k) (.cv z))
  have p0014 :=
    @gBreq2d (.classEq (.cv k) (.cv z)) (.cv k) (.cv z) (.cv m) (synClec) p0013
  have p0015 :=
    @gRspccv (synWbr (.cv m) (synClec) (.cv k)) (synWbr (.cv m) (synClec) (.cv z)) k
      (.cv z) (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
      (.imp (.classMem (.cv z)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWbr (.cv m) (synClec) (.cv z)))
      p0012 p0015
  have p0017 :=
    @gSyld
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (synWbr (.cv z) (synCltc) C)
      (.classMem (.cv z)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWbr (.cv m) (synClec) (.cv z)) p0009 p0016
  have p0018 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (.neg (synWbr (.cv z) (synCltc) C))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      p0018 p0010
  have p0025 :=
    @gSimprd
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv m) (synCwppcand F C)) (synWbr (.cv m) (synCltc) C) p0003
  have p0026 := @gBrltc (.cv m) C
  have p0027 :=
    @gBiimpi (synWbr (.cv m) (synCltc) C)
      (synWa (synWbr (.cv m) (synClec) C) (synWne (.cv m) C)) p0026
  have p0028 :=
    @gSyl
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWbr (.cv m) (synCltc) C)
      (synWa (synWbr (.cv m) (synClec) C) (synWne (.cv m) C)) p0025 p0027
  have p0029 :=
    @gSimpld
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWbr (.cv m) (synClec) C) (synWne (.cv m) C) p0028
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWbr (.cv m) (synClec) C) p0020 p0029
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (.classMem (.cv z) (synCwppcand F C)) p0018 p0005
  have p0034 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (.neg (synWbr (.cv z) (synCltc) C))
  have p0035 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (.classMem (.cv z) (synCwppcand F C)) (.neg (synWbr (.cv z) (synCltc) C)) p0033
      p0034
  have p0036 := @gWppcandnltpivoteqd C z F
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (synWa (.classMem (.cv z) (synCwppcand F C)) (.neg (synWbr (.cv z) (synCltc) C)))
      (.classEq (.cv z) C) p0035 p0036
  have p0038 :=
    @gBreqtrrd
      (synWa (synWa (synWa (.classMem (.cv m)
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
            (synWral k
              (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
              (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
        (.neg (synWbr (.cv z) (synCltc) C)))
      (.cv m) C (.cv z) (synClec) p0030 p0037
  have p0039 :=
    @gEx
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (.neg (synWbr (.cv z) (synCltc) C)) (synWbr (.cv m) (synClec) (.cv z)) p0038
  have p0040 :=
    @gPm261d
      (synWa (synWa (.classMem (.cv m)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
            (synWbr (.cv m) (synClec) (.cv k)))) (.classMem (.cv z) (synCwppcand F C)))
      (synWbr (.cv z) (synCltc) C) (synWbr (.cv m) (synClec) (.cv z)) p0017 p0039
  have p0041 :=
    @gEx
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv z) (synCwppcand F C)) (synWbr (.cv m) (synClec) (.cv z)) p0040
  have p0042 :=
    @gRalrimiv
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWbr (.cv m) (synClec) (.cv z)) z (synCwppcand F C) dv_cache_0004 p0041
  have p0043 :=
    @gJca
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (.cv m) (synCwppcand F C))
      (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))) p0004 p0042
  exact p0043


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisobranchwwknfdv`. -/
@[expose]
noncomputable def gWecutisobranchwwknfdv (x : Var) (y : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (_dv_D_u : u ∉ D.fv)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv)
    (_dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv)
    (_dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (_dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (_dv_h_x : h ≠ x)
    (dv_h_y : h ≠ y) (_dv_u_x : u ≠ x) (_dv_u_y : u ≠ y) (_dv_x_y : x ≠ y)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
              (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    h ∉
      ((synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S D E)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, or_false,
          not_false_eq_true])
  have p0000 :=
    @gId
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0001 :=
    Nominal.ax1
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
  have p0002 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0001
  have p0003 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0000 p0002
  have p0004 :=
    @gSimpl
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
  have p0005 :=
    @gIsoeq4
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCsn (.cv y)))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      D R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0006 :=
    @gSyl
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0004 p0005
  have p0007 :=
    @gBiimpd
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0006
  have p0008 :=
    @gA2i
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0007
  have p0009 :=
    @gA1i
      (.imp (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0008
  have p0010 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0003 p0009
  have p0011 :=
    @gSimpr
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
  have p0012 :=
    @gIsoeq5 D
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      E R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0013 :=
    @gSyl
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S D E))
      p0011 p0012
  have p0014 :=
    @gBiimpd
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D E)
      p0013
  have p0015 :=
    @gA2i
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D E)
      p0014
  have p0016 :=
    @gA1i
      (.imp (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D E)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0015
  have p0017 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S D E))
      p0010 p0016
  have p0018 := @gSnex (synCop (.cv y) (.cv u))
  have p0019 :=
    @gUnex (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0018
  have p0020 :=
    @gIsoeq1 D E R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      (.cv h)
  have p0021 :=
    @gSpcev (synWiso (.cv h) R S D E)
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D E)
      h (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S D E) (synWex h (synWiso (.cv h) R S D E)))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0021
  have p0023 :=
    @gA2i
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D E)
      (synWex h (synWiso (.cv h) R S D E)) p0022
  have p0024 :=
    @gA1i
      (.imp (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D E)) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) R S D E))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0023
  have p0025 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S D E))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) R S D E)))
      p0017 p0024
  have p0026 :=
    @gN3mix1 (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0027 :=
    @gA1i
      (.imp (synWex h (synWiso (.cv h) R S D E))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0026
  have p0028 :=
    @gA2i
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWex h (synWiso (.cv h) R S D E))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0027
  have p0029 :=
    @gA1i
      (.imp (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) R S D E))) (.imp (synWa
            (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0028
  have p0030 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) R S D E)))
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0025 p0029
  have p0031 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisobranchwcknfdv`. -/
@[expose]
noncomputable def gWecutisobranchwcknfdv (x : Var) (y : Var) (v : Var) (u : Var)
    (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv)
    (_dv_D_u : u ∉ D.fv) (_dv_D_v : v ∉ D.fv) (dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv) (_dv_E_v : v ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (_dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv) (_dv_R_v : v ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (_dv_S_v : v ∉ S.fv) (dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u)
    (dv_h_v : h ≠ v) (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (_dv_u_v : u ≠ v) (_dv_u_x : u ≠ x)
    (_dv_u_y : u ≠ y) (dv_v_x : v ≠ x) (_dv_v_y : v ≠ y) (_dv_x_y : x ≠ y)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    h ∉
      ((synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_S_h, dv_h_v, dv_R_h, dv_h_y, dv_h_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ ((Wff.classEq (.cv x) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_h_x, dv_h_v, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_v_x), not_false_eq_true])
  have dv_cache_0005 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_D_x, dv_E_x, dv_S_x,
          (Ne.symm dv_v_x), (Ne.symm dv_h_x), dv_R_x, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @gId
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0001 :=
    @gA1i
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
          (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0003 :=
    @gSimpr
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classMem (.cv v) E)
  have p0004 :=
    @gSyl
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classMem (.cv v) E))
      (.classMem (.cv v) E) p0002 p0003
  have p0005 :=
    @gA1i
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (.cv v) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0004
  have p0006 := @gId (.classMem (.cv v) E)
  have p0007 :=
    @gA1d (.classMem (.cv v) E) (.classMem (.cv v) E)
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0006
  have p0008 :=
    @gA1i
      (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0007
  have p0009 :=
    @gId
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0010 :=
    Nominal.ax1
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0011 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0010
  have p0012 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0009 p0011
  have p0014 :=
    @gSimpl
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classMem (.cv v) E)
  have p0015 :=
    @gSyl
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      p0002 p0014
  have p0016 :=
    @gIsoeq4
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCsn (.cv y)))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      D R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0015 p0016
  have p0018 :=
    @gBiimpd
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0017
  have p0019 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0018
  have p0020 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0019
  have p0021 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0012 p0020
  have p0022 :=
    @gSimpr
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0023 :=
    @gIsoeq5 D
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0024 :=
    @gSyl
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0022 p0023
  have p0025 :=
    @gBiimpd
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0024
  have p0026 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
        (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0025
  have p0027 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0026
  have p0028 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0021 p0027
  have p0029 :=
    @gIsores2 D
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0030 :=
    @gBiimpi
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0029
  have p0031 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0030
  have p0032 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0031
  have p0033 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0032
  have p0034 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0028 p0033
  have p0035 := @gSnex (synCop (.cv y) (.cv u))
  have p0036 :=
    @gUnex (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0035
  have p0037 :=
    @gIsoeq1 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      (.cv h)
  have p0038 :=
    @gSpcev
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      h (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      dv_cache_0001 dv_cache_0002 p0036 p0037
  have p0039 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0038
  have p0040 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0039
  have p0041 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0040
  have p0042 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0034 p0041
  have p0043 :=
    Nominal.ax1
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (.cv v) E)
  have p0044 :=
    @gA1i
      (.imp (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0043
  have p0045 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0044
  have p0046 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0045
  have p0047 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0042 p0046
  have p0048 :=
    @g_pm3_2 (.classMem (.cv v) E)
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0049 :=
    @gA2i (.classMem (.cv v) E)
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0048
  have p0050 :=
    @gA1i
      (.imp (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0049
  have p0051 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R
              (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0050
  have p0052 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0051
  have p0053 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0047 p0052
  have p0054 :=
    Nominal.ax2
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (.cv v) E)
      (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0055 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))) (.imp
          (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0054
  have p0056 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0053 p0055
  have p0057 :=
    Nominal.ax1
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.classMem (.cv v) E)
  have p0058 :=
    @gA1i
      (.imp (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
        (.imp (.classMem (.cv v) E) (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0057
  have p0059 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (.classMem (.cv v) E) (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      p0056 p0058
  have p0060 :=
    Nominal.ax2 (.classMem (.cv v) E)
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (.cv v) E))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
  have p0061 :=
    @gA1i
      (.imp (.imp (.classMem (.cv v) E) (.imp (.imp (synWa (synWa (.classEq (synCun
                      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
        (.imp (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv v) E))) (.imp (.classMem (.cv v) E) (.imp (synWa (synWa
                  (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0060
  have p0062 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (.imp (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E))) (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      p0059 p0061
  have p0063 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)))
      (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0008 p0062
  have p0064 :=
    Nominal.ax1
      (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0065 :=
    @gA1i
      (.imp (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))) (.imp
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0064
  have p0066 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      p0063 p0065
  have p0067 :=
    Nominal.ax2
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (.cv v) E)
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
  have p0068 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
        (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
              (synWa (synWa (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                        (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0067
  have p0069 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv v) E) (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      p0066 p0068
  have p0070 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (.cv v) E))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0005 p0069
  have p0071 :=
    Nominal.ax2
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0072 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))) (.imp
          (.imp (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
              (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))) (.imp
            (synWa (synWa (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0071
  have p0073 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))) (.imp (synWa
            (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0070 p0072
  have p0074 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
          (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0001 p0073
  have p0075 := @gSneq (.cv x) (.cv v)
  have p0076 :=
    @gImaeq2d (.classEq (.cv x) (.cv v)) (synCsn (.cv x)) (synCsn (.cv v))
      (synCcnv (synCdif S (synCid))) p0075
  have p0077 :=
    @gIneq2d (.classEq (.cv x) (.cv v))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))) E p0076
  have p0081 :=
    @gXpeq12d (.classEq (.cv x) (.cv v))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) p0077
      p0077
  have p0082 :=
    @gIneq2d (.classEq (.cv x) (.cv v))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      S p0081
  have p0083 :=
    @gIsoeq3 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.cv h)
  have p0084 :=
    @gSyl (.classEq (.cv x) (.cv v))
      (.classEq (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWb (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      p0082 p0083
  have p0088 :=
    @gIsoeq5 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.cv h)
  have p0089 :=
    @gSyl (.classEq (.cv x) (.cv v))
      (.classEq (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWb (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0077 p0088
  have p0090 :=
    @gBitrd (.classEq (.cv x) (.cv v))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0084 p0089
  have p0091 :=
    @gExbidv (.classEq (.cv x) (.cv v))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      h dv_cache_0003 p0090
  have p0092 :=
    @gRspcev
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      x (.cv v) E dv_cache_0004 dv_cache_0005 dv_cache_0006 p0091
  have p0093 :=
    @gA1i
      (.imp (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0092
  have p0094 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      p0093
  have p0095 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                    (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0094
  have p0096 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv v) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      p0074 p0095
  have p0097 :=
    @gN3mix2
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0098 :=
    @gA1i
      (.imp (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0097
  have p0099 :=
    @gA2i
      (synWa (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0098
  have p0100 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
        (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0099
  have p0101 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0096 p0100
  have p0102 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0101
  exact p0102


end NFChoice.DirectNominalPrf.WPPReplay

end
