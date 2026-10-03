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

@[expose]
noncomputable def g_wppcandstrictsliceleastdndvv (C : Class) (D : Class) (R : Class)
    (k : Var) (m : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv)
    (dv_C_q : q ∉ C.fv) (dv_D_k : k ∉ D.fv) (dv_D_m : m ∉ D.fv) (dv_D_q : q ∉ D.fv)
    (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_R_k : k ∉ R.fv)
    (dv_R_m : m ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_m : k ≠ m) (dv_k_q : k ≠ q)
    (_dv_m_q : m ≠ q)
    (hyp_wppcandstrictsliceleastdndvv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wppcandstrictsliceleastdndvv_2 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppcandstrictsliceleastdndvv_3 : Nominal.NPrf (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_c0)) (syn_wrex m
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k))))) :=
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
    k ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv :=
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
    q ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv :=
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
    g ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv :=
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
      ((Wff.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g))))))))).fv :=
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
      ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv g)))))))).fv :=
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
    m ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv :=
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
      ((syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))).fv :=
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
      ((syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k))))).fv :=
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
  have p0000 := @g_wppcandstrictsliceexndv C F hyp_wppcandstrictsliceleastdndvv_2
  have p0001 :=
    @g_wecutcardrepleastdndv g D R k
      (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) q
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      hyp_wppcandstrictsliceleastdndvv_1 p0000 hyp_wppcandstrictsliceleastdndvv_3
  have p0002 :=
    @g_id
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))
  have p0003 :=
    @g_id
      (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv g))))))))
  have p0004 :=
    @g_breq1d
      (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv g))))))))
      (.cv m)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
      (.cv k) (syn_clec) p0003
  have p0005 :=
    @g_ralbidv
      (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv g))))))))
      (syn_wbr (.cv m) (syn_clec) (.cv k))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))
      k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
      dv_cache_0013 p0004
  have p0006 :=
    @g_rspcev
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))
      m
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
      (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0005
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))
      (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      p0002 p0006
  have p0008 :=
    @g_a1i
      (.imp (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))) (syn_wrex m
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))))
      (.classMem (.cv g) (syn_cpw1 (syn_cpw1 D))) p0007
  have p0009 :=
    @g_rexlimiv
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))
      (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      g (syn_cpw1 (syn_cpw1 D)) dv_cache_0017 p0008
  have p0010 :=
    @g_syl
      (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (syn_wrex g (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv g)))))))
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))))
      (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      p0001 p0009
  exact p0010

@[expose]
noncomputable def g_wppcandstrictsliceleastextenddv (z : Var) (C : Class) (k : Var)
    (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (_dv_C_m : m ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_F_k : k ∉ F.fv) (_dv_F_m : m ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_k_m : k ≠ m)
    (dv_k_z : k ≠ z) (dv_m_z : m ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k))))
        (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))) :=
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
    k ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv :=
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
  have dv_cache_0003 : k ∉ ((syn_wbr (.cv m) (syn_clec) (.cv z))).fv :=
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
      ((syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k))))).fv :=
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
    @g_simpl
      (.classMem (.cv m)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
  have p0001 := @g_elwppcandstrictslice C m F
  have p0002 :=
    @g_biimpi
      (.classMem (.cv m)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0001
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv m)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0000
      p0002
  have p0004 :=
    @g_simpld
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C) p0003
  have p0005 :=
    @g_simpr
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv z) (syn_cwppcand F C))
  have p0006 := @g_elwppcandstrictslice C z F
  have p0007 :=
    @g_biimpri
      (.classMem (.cv z)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv z) (syn_cltc) C)) p0006
  have p0008 :=
    @g_ex (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv z) (syn_cltc) C)
      (.classMem (.cv z)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      p0007
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (.classMem (.cv z) (syn_cwppcand F C))
      (.imp (syn_wbr (.cv z) (syn_cltc) C) (.classMem (.cv z)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))))
      p0005 p0008
  have p0010 :=
    @g_simpl
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv z) (syn_cwppcand F C))
  have p0011 :=
    @g_simpr
      (.classMem (.cv m)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
      p0010 p0011
  have p0013 := @g_id (.classEq (.cv k) (.cv z))
  have p0014 :=
    @g_breq2d (.classEq (.cv k) (.cv z)) (.cv k) (.cv z) (.cv m) (syn_clec) p0013
  have p0015 :=
    @g_rspccv (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (.cv m) (syn_clec) (.cv z)) k
      (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (.imp (.classMem (.cv z)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wbr (.cv m) (syn_clec) (.cv z)))
      p0012 p0015
  have p0017 :=
    @g_syld
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (syn_wbr (.cv z) (syn_cltc) C)
      (.classMem (.cv z)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wbr (.cv m) (syn_clec) (.cv z)) p0009 p0016
  have p0018 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (.neg (syn_wbr (.cv z) (syn_cltc) C))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      p0018 p0010
  have p0025 :=
    @g_simprd
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C) p0003
  have p0026 := @g_brltc (.cv m) C
  have p0027 :=
    @g_biimpi (syn_wbr (.cv m) (syn_cltc) C)
      (syn_wa (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C)) p0026
  have p0028 :=
    @g_syl
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wbr (.cv m) (syn_cltc) C)
      (syn_wa (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C)) p0025 p0027
  have p0029 :=
    @g_simpld
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C) p0028
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wbr (.cv m) (syn_clec) C) p0020 p0029
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (.classMem (.cv z) (syn_cwppcand F C)) p0018 p0005
  have p0034 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (.neg (syn_wbr (.cv z) (syn_cltc) C))
  have p0035 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (.classMem (.cv z) (syn_cwppcand F C)) (.neg (syn_wbr (.cv z) (syn_cltc) C)) p0033
      p0034
  have p0036 := @g_wppcandnltpivoteqd C z F
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (syn_wa (.classMem (.cv z) (syn_cwppcand F C)) (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (.classEq (.cv z) C) p0035 p0036
  have p0038 :=
    @g_breqtrrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m)
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
            (syn_wral k
              (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
              (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
        (.neg (syn_wbr (.cv z) (syn_cltc) C)))
      (.cv m) C (.cv z) (syn_clec) p0030 p0037
  have p0039 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (.neg (syn_wbr (.cv z) (syn_cltc) C)) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0038
  have p0040 :=
    @g_pm2_61d
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
            (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)))
      (syn_wbr (.cv z) (syn_cltc) C) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0017 p0039
  have p0041 :=
    @g_ex
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0040
  have p0042 :=
    @g_ralrimiv
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wbr (.cv m) (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0004 p0041
  have p0043 :=
    @g_jca
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (.cv m) (syn_cwppcand F C))
      (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))) p0004 p0042
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

@[expose]
noncomputable def g_wecutisobranchwwknfdv (x : Var) (y : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (_dv_D_u : u ∉ D.fv)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv)
    (_dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv)
    (_dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (_dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (_dv_h_x : h ≠ x)
    (dv_h_y : h ≠ y) (_dv_u_x : u ≠ x) (_dv_u_y : u ≠ y) (_dv_x_y : x ≠ y)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
              (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv x)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
              (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv x)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))).fv :=
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
      ((syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
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
    @g_id
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
  have p0001 :=
    Nominal.ax1
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
  have p0002 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0001
  have p0003 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0000 p0002
  have p0004 :=
    @g_simpl
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
  have p0005 :=
    @g_isoeq4
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_csn (.cv y)))
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      D R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0006 :=
    @g_syl
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0004 p0005
  have p0007 :=
    @g_biimpd
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0006
  have p0008 :=
    @g_a2i
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0007
  have p0009 :=
    @g_a1i
      (.imp (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0008
  have p0010 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0003 p0009
  have p0011 :=
    @g_simpr
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
  have p0012 :=
    @g_isoeq5 D
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      E R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0013 :=
    @g_syl
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S D E))
      p0011 p0012
  have p0014 :=
    @g_biimpd
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D E)
      p0013
  have p0015 :=
    @g_a2i
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D E)
      p0014
  have p0016 :=
    @g_a1i
      (.imp (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0015
  have p0017 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S D E))
      p0010 p0016
  have p0018 := @g_snex (syn_cop (.cv y) (.cv u))
  have p0019 :=
    @g_unex (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0018
  have p0020 :=
    @g_isoeq1 D E R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
      (.cv h)
  have p0021 :=
    @g_spcev (syn_wiso (.cv h) R S D E)
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D E)
      h (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
      dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S D E) (syn_wex h (syn_wiso (.cv h) R S D E)))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0021
  have p0023 :=
    @g_a2i
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D E)
      (syn_wex h (syn_wiso (.cv h) R S D E)) p0022
  have p0024 :=
    @g_a1i
      (.imp (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0023
  have p0025 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S D E))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E)))
      p0017 p0024
  have p0026 :=
    @g_n_3mix1 (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0027 :=
    @g_a1i
      (.imp (syn_wex h (syn_wiso (.cv h) R S D E))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0026
  have p0028 :=
    @g_a2i
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0027
  have p0029 :=
    @g_a1i
      (.imp (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E))) (.imp (syn_wa
            (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0028
  have p0030 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E)))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0025 p0029
  have p0031 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0030
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

@[expose]
noncomputable def g_wecutisobranchwcknfdv (x : Var) (y : Var) (v : Var) (u : Var)
    (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv)
    (_dv_D_u : u ∉ D.fv) (_dv_D_v : v ∉ D.fv) (dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv) (_dv_E_v : v ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (_dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv) (_dv_R_v : v ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (_dv_S_v : v ∉ S.fv) (dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u)
    (dv_h_v : h ≠ v) (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (_dv_u_v : u ≠ v) (_dv_u_x : u ≠ x)
    (_dv_u_y : u ≠ y) (dv_v_x : v ≠ x) (_dv_v_y : v ≠ y) (_dv_x_y : x ≠ y)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                  (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv x)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
              (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv x)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))).fv :=
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
      ((syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))).fv :=
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
      ((syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))).fv :=
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
    @g_id
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0001 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_wa
          (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0003 :=
    @g_simpr
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classMem (.cv v) E)
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classMem (.cv v) E))
      (.classMem (.cv v) E) p0002 p0003
  have p0005 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classMem (.cv v) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0004
  have p0006 := @g_id (.classMem (.cv v) E)
  have p0007 :=
    @g_a1d (.classMem (.cv v) E) (.classMem (.cv v) E)
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0006
  have p0008 :=
    @g_a1i
      (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0007
  have p0009 :=
    @g_id
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
  have p0010 :=
    Nominal.ax1
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0011 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0010
  have p0012 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0009 p0011
  have p0014 :=
    @g_simpl
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classMem (.cv v) E)
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      p0002 p0014
  have p0016 :=
    @g_isoeq4
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_csn (.cv y)))
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      D R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0015 p0016
  have p0018 :=
    @g_biimpd
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0017
  have p0019 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0018
  have p0020 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0019
  have p0021 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0012 p0020
  have p0022 :=
    @g_simpr
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0023 :=
    @g_isoeq5 D
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0022 p0023
  have p0025 :=
    @g_biimpd
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0024
  have p0026 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
        (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0025
  have p0027 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0026
  have p0028 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0021 p0027
  have p0029 :=
    @g_isores2 D
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0030 :=
    @g_biimpi
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0029
  have p0031 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0030
  have p0032 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0031
  have p0033 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0032
  have p0034 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0028 p0033
  have p0035 := @g_snex (syn_cop (.cv y) (.cv u))
  have p0036 :=
    @g_unex (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0035
  have p0037 :=
    @g_isoeq1 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
      (.cv h)
  have p0038 :=
    @g_spcev
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      h (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
      dv_cache_0001 dv_cache_0002 p0036 p0037
  have p0039 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0038
  have p0040 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0039
  have p0041 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0040
  have p0042 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      p0034 p0041
  have p0043 :=
    Nominal.ax1
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classMem (.cv v) E)
  have p0044 :=
    @g_a1i
      (.imp (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0043
  have p0045 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      p0044
  have p0046 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0045
  have p0047 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      p0042 p0046
  have p0048 :=
    @g_pm3_2 (.classMem (.cv v) E)
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0049 :=
    @g_a2i (.classMem (.cv v) E)
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      p0048
  have p0050 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0049
  have p0051 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R
              (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      p0050
  have p0052 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
        (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0051
  have p0053 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      p0047 p0052
  have p0054 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classMem (.cv v) E)
      (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
  have p0055 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))) (.imp
          (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0054
  have p0056 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      p0053 p0055
  have p0057 :=
    Nominal.ax1
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (.classMem (.cv v) E)
  have p0058 :=
    @g_a1i
      (.imp (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
        (.imp (.classMem (.cv v) E) (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0057
  have p0059 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (.imp (.classMem (.cv v) E) (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      p0056 p0058
  have p0060 :=
    Nominal.ax2 (.classMem (.cv v) E)
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classMem (.cv v) E))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
  have p0061 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv v) E) (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
        (.imp (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (.classMem (.cv v) E))) (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa
                  (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0060
  have p0062 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      (.imp (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E))) (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      p0059 p0061
  have p0063 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)))
      (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      p0008 p0062
  have p0064 :=
    Nominal.ax1
      (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0065 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))) (.imp
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0064
  have p0066 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      p0063 p0065
  have p0067 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classMem (.cv v) E)
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
  have p0068 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
        (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
              (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                        (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0067
  have p0069 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.imp (.classMem (.cv v) E) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classMem (.cv v) E)) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
            (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      p0066 p0068
  have p0070 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classMem (.cv v) E))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      p0005 p0069
  have p0071 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
  have p0072 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
            (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))) (.imp
          (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_wa
              (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (.imp
            (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
                  (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0071
  have p0073 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (.imp
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (.imp (syn_wa
            (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))))
      p0070 p0072
  have p0074 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_wa
          (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      p0001 p0073
  have p0075 := @g_sneq (.cv x) (.cv v)
  have p0076 :=
    @g_imaeq2d (.classEq (.cv x) (.cv v)) (syn_csn (.cv x)) (syn_csn (.cv v))
      (syn_ccnv (syn_cdif S (syn_cid))) p0075
  have p0077 :=
    @g_ineq2d (.classEq (.cv x) (.cv v))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))) E p0076
  have p0081 :=
    @g_xpeq12d (.classEq (.cv x) (.cv v))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) p0077
      p0077
  have p0082 :=
    @g_ineq2d (.classEq (.cv x) (.cv v))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      S p0081
  have p0083 :=
    @g_isoeq3 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.cv h)
  have p0084 :=
    @g_syl (.classEq (.cv x) (.cv v))
      (.classEq (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      p0082 p0083
  have p0088 :=
    @g_isoeq5 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.cv h)
  have p0089 :=
    @g_syl (.classEq (.cv x) (.cv v))
      (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0077 p0088
  have p0090 :=
    @g_bitrd (.classEq (.cv x) (.cv v))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0084 p0089
  have p0091 :=
    @g_exbidv (.classEq (.cv x) (.cv v))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      h dv_cache_0003 p0090
  have p0092 :=
    @g_rspcev
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      x (.cv v) E dv_cache_0004 dv_cache_0005 dv_cache_0006 p0091
  have p0093 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0092
  have p0094 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      p0093
  have p0095 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
        (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0094
  have p0096 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wa (.classMem (.cv v) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      p0074 p0095
  have p0097 :=
    @g_n_3mix2
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0098 :=
    @g_a1i
      (.imp (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0097
  have p0099 :=
    @g_a2i
      (syn_wa (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0098
  have p0100 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
        (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0099
  have p0101 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0096 p0100
  have p0102 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0101
  exact p0102


end NFChoice.DirectNominalPrf.WPPReplay

end
