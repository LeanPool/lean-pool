/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogenfixedfwd (x : Var) (y : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (_dv_D_x : x ∉ D.fv)
    (dv_E_f : f ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_R_f : f ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_S_f : f ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y)
    (hyp_wecutisogenfixedfwd_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisogenfixedfwd_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv f) (syn_cwecutisogen R D S E))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪
        ({ f } : Finset Var) ∪
      E.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_f : r ≠ f := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_r : f ≠ r := Ne.symm fresh_r_ne_f
  have fresh_r_not_E : r ∉ E.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_chnwcutcode R D (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_f_x, dv_D_f, dv_R_f, or_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chnwcutcode R D (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_D, fresh_r_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_chnwcutcode S E (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_f_y, dv_E_f, dv_S_f, or_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chnwcutcode S E (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_y, fresh_r_not_E, fresh_r_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0007 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0008 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D,
          fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, or_false, not_false_eq_true])
  have dv_cache_0009 :
    r ∉
      ((syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
              (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_D, fresh_r_ne_y, fresh_r_not_E,
          fresh_r_not_R, fresh_r_not_S, fresh_r_ne_f, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0001 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000
      p0001
  have p0003 := @g_wecutisogencodeambient x D R hyp_wecutisogenfixedfwd_1
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D)
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) p0002 p0003
  have p0006 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0000
      p0006
  have p0008 := @g_wecutisogencodeambient y E S hyp_wecutisogenfixedfwd_2
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) E)
      (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))) p0007 p0008
  have p0010 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv)))
      (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))) p0004 p0009
  have p0011 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0015 := @g_wecutisogencodeparts x D R hyp_wecutisogenfixedfwd_1
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D)
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0002 p0015
  have p0017 :=
    @g_simpl
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0016 p0017
  have p0019 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
      (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.cv f)
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))))
      p0018 p0019
  have p0024 := @g_wecutisogencodeparts y E S hyp_wecutisogenfixedfwd_2
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) E)
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0007 p0024
  have p0026 :=
    @g_simpl
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      p0025 p0026
  have p0028 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))))
      p0027 p0028
  have p0030 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      p0020 p0029
  have p0036 :=
    @g_simpr
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0016 p0036
  have p0038 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))))
      p0037 p0038
  have p0040 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      p0030 p0039
  have p0046 :=
    @g_simpr
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0025 p0046
  have p0048 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0047 p0048
  have p0050 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0040 p0049
  have p0051 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0011 p0050
  have p0052 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv)))
        (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))
      p0010 p0051
  have p0053 :=
    @g_wecutisogenrawcl (syn_cvv) (syn_chnwcutcode R D (.cv x))
      (syn_chnwcutcode S E (.cv y)) f r dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv)))
          (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      p0052 p0053
  have p0055 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
  have p0059 := @g_wecutisogencodeinran x D R hyp_wecutisogenfixedfwd_1
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D)
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) p0002 p0059
  have p0064 := @g_wecutisogencodeinran y E S hyp_wecutisogenfixedfwd_2
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) E)
      (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))) p0007 p0064
  have p0066 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))
      (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))) p0060 p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa
              (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))))
      p0055 p0066
  have p0068 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
  have p0069 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa
              (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))))
      (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      p0067 p0068
  have p0070 :=
    @g_wecutisogenrawmem (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv y)) D R S
      f E r
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa
              (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))))
      (syn_wa (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa
              (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E)) p0069 p0070
  have p0072 :=
    @g_rexlimddv
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E)) r (syn_cvv) dv_cache_0008
      dv_cache_0009 p0054 p0071
  exact p0072


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisossgen (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisossgen_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisossgen_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (syn_wss (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_f_ne_x : f ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_f : x ≠ f := Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_f : y ≠ f := Ne.symm fresh_f_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0012 : f ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0013 : f ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_E, not_false_eq_true])
  have dv_cache_0014 : f ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_R, not_false_eq_true])
  have dv_cache_0015 : f ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_S, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_f, fresh_x_not_D,
          fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, Finset.mem_singleton, fresh_y_ne_f, fresh_y_not_D,
          fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false, not_false_eq_true])
  have dv_cache_0018 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0019 : f ∉ ((syn_cwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0020 : f ∉ ((syn_cwecutisogen R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_elwecutiso x y D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @g_biimpi (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      p0000
  have p0002 :=
    @g_wecutisogenfixedfwd x y D R S f E dv_cache_0012 dv_cache_0002 dv_cache_0013
      dv_cache_0003 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0007 dv_cache_0010
      dv_cache_0009 hyp_wecutisossgen_1 hyp_wecutisossgen_2
  have p0003 :=
    @g_ex (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E)) p0002
  have p0004 :=
    @g_rexlimivv
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E)) x y D E dv_cache_0001 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0003
  have p0005 :=
    @g_syl (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E)) p0001 p0004
  have p0006 :=
    @g_ssriv f (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E) dv_cache_0019
      dv_cache_0020 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogensswecutiso (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogensswecutiso_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisogensswecutiso_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (syn_wss (syn_cwecutisogen R D S E) (syn_cwecutiso R D S E)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_E : r ∉ E.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_f_ne_r : f ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_f : r ≠ f := Ne.symm fresh_f_ne_r
  have fresh_f_ne_x : f ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_f : x ≠ f := Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_f : y ≠ f := Ne.symm fresh_f_ne_y
  have fresh_r_ne_x : r ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : r ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_D, not_false_eq_true])
  have dv_cache_0002 : r ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_E, not_false_eq_true])
  have dv_cache_0003 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0004 : r ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_S, not_false_eq_true])
  have dv_cache_0005 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0006 : x ∉ ((syn_cop (.cv r) (syn_cdm (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_f, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0011 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0012 : f ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0013 : y ∉ (D).fv :=
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
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0014 : f ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_E, not_false_eq_true])
  have dv_cache_0015 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0016 : f ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_R, not_false_eq_true])
  have dv_cache_0017 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0018 : f ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_S, not_false_eq_true])
  have dv_cache_0019 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0020 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0021 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0022 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0023 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0024 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0025 : y ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have dv_cache_0026 :
    y ∉
      ((syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f)))
              (syn_chnwcutcode R D (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          Finset.mem_union, Finset.mem_singleton, fresh_y_ne_r, fresh_y_ne_f,
          fresh_y_not_D, fresh_y_not_R, fresh_y_not_E, fresh_y_not_S, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R,
          fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0028 :
    x ∉
      ((syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_f,
          fresh_x_not_D, fresh_x_not_R, fresh_x_not_E, fresh_x_not_S,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D, fresh_r_not_E, fresh_r_not_R,
          fresh_r_not_S, or_false, not_false_eq_true])
  have dv_cache_0030 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D,
          fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, or_false, not_false_eq_true])
  have dv_cache_0031 : f ∉ ((syn_cwecutisogen R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0032 : f ∉ ((syn_cwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_wecutisogenrawout D R S f E r dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_simpr (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
  have p0002 :=
    @g_simpr (.classMem (.cv r) (syn_cvv))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
  have p0003 :=
    @g_simpr
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
  have p0004 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      p0002 p0003
  have p0005 :=
    @g_simpl
      (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) p0004
      p0005
  have p0007 :=
    @g_wecutisogenrangedecode x (syn_cop (.cv r) (syn_cdm (.cv f))) D R dv_cache_0006
      dv_cache_0007 dv_cache_0008 hyp_wecutisogensswecutiso_1
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
      (syn_wrex x D
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
      p0006 p0007
  have p0009 :=
    @g_simpl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (.cv x) D)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0013 :=
    @g_simpr
      (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
  have p0014 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
      p0004 p0013
  have p0015 :=
    @g_wecutisogenrangedecode y
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      E S dv_cache_0009 dv_cache_0010 dv_cache_0011 hyp_wecutisogensswecutiso_2
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
      (syn_wrex y E (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      p0014 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wrex y E (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      p0009 p0016
  have p0018 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (syn_wa (.classMem (.cv y) E) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (syn_chnwcutcode S E (.cv y))))
  have p0019 :=
    @g_simpr
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (.cv x) D)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (syn_wa (.classMem (.cv x) D)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
      p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (.cv x) D)
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
      (.classMem (.cv x) D) p0020 p0021
  have p0023 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (syn_wa (.classMem (.cv y) E) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (syn_chnwcutcode S E (.cv y))))
  have p0024 :=
    @g_simpl (.classMem (.cv y) E)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv y) E) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (syn_chnwcutcode S E (.cv y))))
      (.classMem (.cv y) E) p0023 p0024
  have p0026 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (.classMem (.cv x) D) (.classMem (.cv y) E) p0022 p0025
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      p0018 p0009
  have p0031 :=
    @g_simpl
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
  have p0032 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0002 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0029 p0032
  have p0037 :=
    @g_simpr (.classMem (.cv x) D)
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) p0020
      p0037
  have p0040 :=
    @g_simpr (.classMem (.cv y) E)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv y) E) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (syn_chnwcutcode S E (.cv y))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
      p0023 p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
      p0038 p0041
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      p0033 p0042
  have p0044 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      p0026 p0043
  have p0045 :=
    @g_wecutisogenfixedrev x y D R S f E r dv_cache_0012 dv_cache_0001 dv_cache_0007
      dv_cache_0013 dv_cache_0014 dv_cache_0002 dv_cache_0015 dv_cache_0010 dv_cache_0016
      dv_cache_0003 dv_cache_0008 dv_cache_0017 dv_cache_0018 dv_cache_0004 dv_cache_0019
      dv_cache_0011 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                  (syn_crn (syn_chnwcutrel R D))) (.classMem
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
          (syn_wa (.classMem (.cv x) D)
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
        (syn_wa (.classMem (.cv y) E) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) p0044 p0045
  have p0047 :=
    @g_rexlimddv
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
        (syn_wa (.classMem (.cv x) D)
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) y E dv_cache_0025 dv_cache_0026 p0017
      p0046
  have p0048 :=
    @g_rexlimddv
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) x D dv_cache_0027 dv_cache_0028 p0008
      p0047
  have p0049 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutisogen R D S E))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) p0001 p0048
  have p0050 :=
    @g_rexlimddv (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) r (syn_cvv) dv_cache_0029 dv_cache_0030
      p0000 p0049
  have p0051 :=
    @g_ssriv f (syn_cwecutisogen R D S E) (syn_cwecutiso R D S E) dv_cache_0031
      dv_cache_0032 p0050
  exact p0051


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogeneq (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogeneq_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisogeneq_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classEq (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E)) :=
  by
  have p0000 := @g_wecutisossgen D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0001 := @g_wecutisogensswecutiso D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0002 := @g_eqssi (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wecutisogenex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogenex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisogenex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cwecutisogen R D S E) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwecutisogen R D S E))
  have p0001 := @g_hwbijex
  have p0002 := @g_vvex
  have p0003 := @g_xpex (syn_chwbij) (syn_cvv) p0001 p0002
  have p0004 := @g_hwgenex
  have p0005 := @g_cnvex (syn_chwgen) p0004
  have p0006 := @g_hnwcutrelex D R hyp_wecutisogenex_1
  have p0007 := @g_rnex (syn_chnwcutrel R D) p0006
  have p0008 := @g_hnwcutrelex E S hyp_wecutisogenex_2
  have p0009 := @g_rnex (syn_chnwcutrel S E) p0008
  have p0010 :=
    @g_xpex (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)) p0007 p0009
  have p0011 :=
    @g_imaex (syn_ccnv (syn_chwgen))
      (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0005 p0010
  have p0012 :=
    @g_inex (syn_cxp (syn_chwbij) (syn_cvv))
      (syn_cima (syn_ccnv (syn_chwgen))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      p0003 p0011
  have p0013 :=
    @g_dmex
      (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      p0012
  have p0014 :=
    @g_eqeltri (syn_cwecutisogen R D S E)
      (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_cvv) p0000 p0013
  exact p0014

@[expose]
noncomputable def g_wecutisoex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisoex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisoex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cwecutiso R D S E) (syn_cvv)) :=
  by
  have p0000 := @g_wecutisogeneq D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0001 := @g_wecutisogenex D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0002 :=
    @g_eqeltri (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wecutisouniex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisouniex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisouniex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv)) :=
  by
  have p0000 := @g_wecutisoex D R S E hyp_wecutisouniex_1 hyp_wecutisouniex_2
  have p0001 := @g_uniex (syn_cwecutiso R D S E) p0000
  exact p0001

@[expose]
noncomputable def g_wecutcardfnfn (D : Class) (R : Class) :
    Nominal.NPrf (syn_wfn (syn_cwecutcardfn R D) (syn_cpw1 (syn_cpw1 D))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have p0000 :=
    @g_ncex
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R q
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_fnmpti q (syn_cpw1 (syn_cpw1 D))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cwecutcardfn R D) dv_cache_0003 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wecutcardfactorex (D : Class) (R : Class)
    (hyp_wecutcardfactorex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_cwecutcardfactor R D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwecutcardfactor R D))
  have p0001 := @g_enex
  have p0002 := @g_imageex (syn_cen) p0001
  have p0003 := @g_n_2ndex
  have p0004 := @g_hnwcutrelex D R hyp_wecutcardfactorex_1
  have p0005 := @g_coex (syn_c2nd) (syn_chnwcutrel R D) p0003 p0004
  have p0006 := @g_siex (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) p0005
  have p0007 :=
    @g_coex (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
      p0002 p0006
  have p0008 :=
    @g_eqeltri (syn_cwecutcardfactor R D)
      (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wecutcardfactorfn (D : Class) (R : Class)
    (hyp_wecutcardfactorfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D))) :=
  by
  have p0000 := @g_enex
  have p0001 := @g_wppimagefn (syn_cen) p0000
  have p0002 := @g_ssv (syn_crn (syn_cimage (syn_cen)))
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv))
      (syn_wss (syn_crn (syn_cimage (syn_cen))) (syn_cvv)) p0001 p0002
  have p0004 := (Nominal.biimpRefl (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv)))
  have p0005 :=
    @g_mpbir (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv))
      (syn_wa (syn_wfn (syn_cimage (syn_cen)) (syn_cvv))
        (syn_wss (syn_crn (syn_cimage (syn_cen))) (syn_cvv)))
      p0003 p0004
  have p0006 := @g_n_2ndfo
  have p0007 := @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_hnwcutrelfndv D R hyp_wecutcardfactorfn_1
  have p0010 := @g_ssv (syn_chwcn D)
  have p0011 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_cvv)) p0009 p0010
  have p0012 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv))
      (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0008 p0013
  have p0015 := @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_sifmap (syn_cpw1 D) (syn_cvv) (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_ssv (syn_cpw1 (syn_cvv))
  have p0020 :=
    @g_pm3_2i
      (syn_wf (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))
        (syn_cpw1 (syn_cvv)))
      (syn_wss (syn_cpw1 (syn_cvv)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_fss (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cvv)) (syn_cvv)
      (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv))
      (syn_wf (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))
        (syn_cvv))
      p0005 p0022
  have p0024 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cvv) (syn_cvv) (syn_cimage (syn_cen))
      (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_cvv)
      (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (syn_cwecutcardfactor R D))
  have p0029 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfactor R D)
      (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
      p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D)))
      (syn_wfn (syn_ccom (syn_cimage (syn_cen))
          (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (syn_cpw1 (syn_cpw1 D)))
      p0027 p0029
  exact p0030

@[expose]
noncomputable def g_wecutcardhrelfn (D : Class) (R : Class)
    (hyp_wecutcardhrelfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) :=
  by
  have p0000 := @g_hnwcutrelfndv D R hyp_wecutcardhrelfn_1
  have p0001 := @g_ssv (syn_chwcn D)
  have p0002 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_cvv)) p0000 p0001
  have p0003 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_ffn (syn_cpw1 D) (syn_cvv) (syn_chnwcutrel R D)
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

@[expose]
noncomputable def g_wecutcardinnerf (D : Class) (R : Class)
    (hyp_wecutcardinnerf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (syn_wf (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_cpw1 D) (syn_cvv)) :=
  by
  have p0000 := @g_n_2ndfo
  have p0001 := @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_hnwcutrelfndv D R hyp_wecutcardinnerf_1
  have p0004 := @g_ssv (syn_chwcn D)
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_cvv)) p0003 p0004
  have p0006 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv))
      (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0002 p0007
  have p0009 := @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

@[expose]
noncomputable def g_wecutcardsiliftfn (D : Class) (R : Class)
    (hyp_wecutcardsiliftfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) :=
  by
  have p0000 := @g_n_2ndfo
  have p0001 := @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_hnwcutrelfndv D R hyp_wecutcardsiliftfn_1
  have p0004 := @g_ssv (syn_chwcn D)
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_cvv)) p0003 p0004
  have p0006 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv))
      (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0002 p0007
  have p0009 := @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_sifmap (syn_cpw1 D) (syn_cvv) (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0014 := Nominal.mp p0012 p0013
  exact p0014

@[expose]
noncomputable def g_wecutcardfactorval (D : Class) (R : Class) (q : Var)
    (_dv_D_q : q ∉ D.fv) (_dv_R_q : q ∉ R.fv)
    (hyp_wecutcardfactorval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwecutcardfactor R D))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_cwecutcardfactor R D)
      (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
      p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cfv
          (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
          (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0001
  have p0003 := @g_wecutcardsiliftfn D R hyp_wecutcardfactorval_1
  have p0004 :=
    @g_a1i
      (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0003
  have p0005 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0006 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0004 p0005
  have p0007 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 D)) (.cv q) (syn_cimage (syn_cen))
      (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0008 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
          (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cen))
            (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q))
        (syn_cfv (syn_cimage (syn_cen))
          (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q))))
      p0006 p0007
  have p0009 := @g_pw12argcl (.cv q) D
  have p0010 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0009
  have p0011 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) p0010
  have p0013 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0009
  have p0014 := @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0015 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0014
  have p0016 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0013 p0015
  have p0017 := @g_wecutcardinnerf D R hyp_wecutcardfactorval_1
  have p0018 :=
    @g_sifvald (syn_cpw1 D) (syn_cvv) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) p0017
  have p0019 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn
          (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0016 p0018
  have p0020 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q))
      (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
        (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0011 p0019
  have p0021 := @g_wecutcardhrelfn D R hyp_wecutcardfactorval_1
  have p0022 :=
    @g_a1i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0021
  have p0028 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0022 p0016
  have p0029 :=
    @g_fvco2 (syn_cpw1 D) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_c2nd)
      (syn_chnwcutrel R D)
  have p0030 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
        (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)))
      (.classEq (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0028 p0029
  have p0033 :=
    @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_wecutcardfactorval_1
  have p0034 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      p0013 p0033
  have p0035 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_c2nd) p0034
  have p0036 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
        (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_cfv (syn_c2nd)
        (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0030 p0035
  have p0037 := (Nominal.classEqRefl (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
  have p0038 :=
    @g_fveq2i (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))
      (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_c2nd) p0037
  have p0039 := @g_brex R D (syn_cwe)
  have p0040 := Nominal.mp hyp_wecutcardfactorval_1 p0039
  have p0041 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0040
  have p0044 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0040
  have p0048 := @g_idex
  have p0049 := @g_difex R (syn_cid) p0041 p0048
  have p0050 := @g_cnvex (syn_cdif R (syn_cid)) p0049
  have p0051 := @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0052 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      p0050 p0051
  have p0053 :=
    @g_inex D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      p0044 p0052
  have p0066 :=
    @g_xpex
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0053 p0053
  have p0067 :=
    @g_inex R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0041 p0066
  have p0080 :=
    @g_opfv2nd
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0067 p0053
  have p0081 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0038 p0080
  have p0082 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0081
  have p0083 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
        (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0036 p0082
  have p0084 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
        (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0083
  have p0085 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q))
      (syn_csn (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0020 p0084
  have p0086 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q))
      (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cimage (syn_cen)) p0085
  have p0087 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cen))
          (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q))
      (syn_cfv (syn_cimage (syn_cen))
        (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q)))
      (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0008 p0086
  have p0088 := @g_enex
  have p0089 :=
    @g_snex
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0090 :=
    @g_fvimagecl
      (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cen) p0088 p0089
  have p0091 :=
    (Nominal.classEqRefl (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen)))
  have p0092 :=
    @g_eqcomi
      (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen))
      (syn_cima (syn_cen) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0091
  have p0093 :=
    @g_eqtri
      (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cima (syn_cen) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen))
      p0090 p0092
  have p0094 :=
    (Nominal.classEqRefl (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
  have p0095 :=
    @g_eqcomi
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen))
      p0094
  have p0096 :=
    @g_eqtri
      (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0093 p0095
  have p0097 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0096
  have p0098 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cen))
          (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q))
      (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0087 p0097
  have p0099 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_cwecutcardfactor R D) (.cv q))
      (syn_cfv (syn_ccom (syn_cimage (syn_cen))
          (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0002 p0098
  exact p0099

@[expose]
noncomputable def g_wecutcardfnval (D : Class) (R : Class) (q : Var) (_dv_D_q : q ∉ D.fv)
    (_dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) :=
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
  have dv_cache_0003 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
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
          Finset.mem_singleton, fresh_p_not_D, fresh_p_not_R, fresh_p_ne_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0006 : p ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R p
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_a1i
      (.classEq (syn_cwecutcardfn R D) (syn_cmpt p (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv p)))))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))
  have p0003 := @g_unieq (.cv p) (.cv q)
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (.classEq (.cv p) (.cv q)) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0002
      p0003
  have p0005 :=
    @g_unieqd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0004
  have p0006 :=
    @g_sneqd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) p0005
  have p0007 :=
    @g_imaeq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      (syn_ccnv (syn_cdif R (syn_cid))) p0006
  have p0008 :=
    @g_ineq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv p)))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      D p0007
  have p0009 :=
    @g_nceqd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv p))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0008
  have p0010 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0011 :=
    @g_ncex
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0012 :=
    @g_a1i
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cvv))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0011
  have p0013 :=
    @g_fvmptd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p (.cv q)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv p)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfn R D) (syn_cvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0001 p0009 p0010 p0012
  exact p0013

@[expose]
noncomputable def g_wecutcardfnfactor (D : Class) (R : Class)
    (hyp_wecutcardfnfactor_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classEq (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cwecutcardfn R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cwecutcardfactor R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfactor,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have p0000 := @g_wecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_wecutcardfactorval D R q dv_cache_0001 dv_cache_0002 hyp_wecutcardfnfactor_1
  have p0002 :=
    @g_eqcomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_cwecutcardfactor R D) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0001
  have p0003 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_cwecutcardfn R D) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) p0000 p0002
  have p0004 :=
    @g_rgen
      (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q))
        (syn_cfv (syn_cwecutcardfactor R D) (.cv q)))
      q (syn_cpw1 (syn_cpw1 D)) p0003
  have p0005 := @g_wecutcardfnfn D R
  have p0006 := @g_wecutcardfactorfn D R hyp_wecutcardfnfactor_1
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cwecutcardfn R D) (syn_cpw1 (syn_cpw1 D)))
      (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D))) p0005 p0006
  have p0008 :=
    @g_eqfnfv q (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D)
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_mpbir (.classEq (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D))
      (syn_wral q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q))
          (syn_cfv (syn_cwecutcardfactor R D) (.cv q))))
      p0004 p0009
  exact p0010

@[expose]
noncomputable def g_wecutcardfnex (D : Class) (R : Class)
    (hyp_wecutcardfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_cwecutcardfn R D) (syn_cvv)) :=
  by
  have p0000 := @g_wecutcardfnfactor D R hyp_wecutcardfnex_1
  have p0001 := @g_wecutcardfactorex D R hyp_wecutcardfnex_1
  have p0002 :=
    @g_eqeltri (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wecutcardpreimandv (D : Class) (R : Class) (K : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))) :=
  by
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_q,
          not_false_eq_true])
  have p0000 :=
    @g_ncex
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R q
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_fnmpti q (syn_cpw1 (syn_cpw1 D))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cwecutcardfn R D) dv_cache_0003 p0000 p0001
  have p0003 := @g_elpreima (syn_cpw1 (syn_cpw1 D)) (.cv q) K (syn_cwecutcardfn R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_a1i
      (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0004
  have p0006 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0007 :=
    @g_biantrurd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) p0006
  have p0008 :=
    @g_bicomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K)
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K))
      p0007
  have p0009 :=
    @g_bitrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K))
      (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) p0005 p0008
  have p0010 := @g_wecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0011 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_cwecutcardfn R D) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      K p0010
  have p0012 :=
    @g_bitrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K)
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      p0009 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_siorndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have dv_cache_0001 : x ∉ ((syn_cpw1 D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_y_not_D,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_z_not_D,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_z_not_R,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
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
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0002 := @g_siexg R (syn_cvv)
  have p0003 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv))
      (.classMem (syn_csi R) (syn_cvv)) p0001 p0002
  have p0005 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0006 := @g_pw1exg D (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem D (syn_cvv))
      (.classMem (syn_cpw1 D) (syn_cvv)) p0005 p0006
  have p0008 := @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0009 := @g_wppweref D R
  have p0010 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cref) D) p0008 p0009
  have p0011 := @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0012 := @g_hnwpw1argcl D x
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (.classMem (.cv x) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))))
      p0011 p0012
  have p0014 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0013
  have p0015 :=
    @g_refd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) D R
      (syn_cuni (.cv x)) p0010 p0014
  have p0019 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0013
  have p0024 :=
    @g_breq12d (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.cv x)
      (syn_csn (syn_cuni (.cv x))) (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csi R) p0019
      p0019
  have p0025 := @g_vex x
  have p0026 := @g_uniex (.cv x) p0025
  have p0029 := @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv x)) R p0026 p0026
  have p0030 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
        (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) p0029
  have p0031 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (syn_wbr (.cv x) (syn_csi R) (.cv x))
      (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))) p0024 p0030
  have p0032 :=
    @g_biimprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (syn_wbr (.cv x) (syn_csi R) (.cv x))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))) p0031
  have p0033 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x)))
      (syn_wbr (.cv x) (syn_csi R) (.cv x)) p0015 p0032
  have p0034 :=
    @g_simp1 (syn_wbr R (syn_cwe) D)
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0035 := @g_wppwepo D R
  have p0036 := @g_porta D R
  have p0037 :=
    @g_simp2bi (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cref) D)
      (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0036
  have p0038 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_ctrans) D)
      p0035 p0037
  have p0039 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_ctrans) D) p0034 p0038
  have p0040 :=
    @g_simp2 (syn_wbr R (syn_cwe) D)
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0041 :=
    @g_simp1 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
      (.classMem (.cv z) (syn_cpw1 D))
  have p0042 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (.classMem (.cv x) (syn_cpw1 D)) p0040 p0041
  have p0044 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (.cv x) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))))
      p0042 p0012
  have p0045 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0044
  have p0047 :=
    @g_simp2 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
      (.classMem (.cv z) (syn_cpw1 D))
  have p0048 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (.classMem (.cv y) (syn_cpw1 D)) p0040 p0047
  have p0049 := @g_hnwpw1argcl D y
  have p0050 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (.cv y) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))))
      p0048 p0049
  have p0051 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0050
  have p0053 :=
    @g_simp3 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
      (.classMem (.cv z) (syn_cpw1 D))
  have p0054 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cpw1 D)) p0040 p0053
  have p0055 := @g_hnwpw1argcl D z
  have p0056 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (.cv z) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))))
      p0054 p0055
  have p0057 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))
      p0056
  have p0058 :=
    @g_simp3 (syn_wbr R (syn_cwe) D)
      (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
        (.classMem (.cv z) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0059 :=
    @g_simpl (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))
  have p0060 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
      (syn_wbr (.cv x) (syn_csi R) (.cv y)) p0058 p0059
  have p0066 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0044
  have p0072 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0050
  have p0073 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y)))
      (syn_csi R) p0066 p0072
  have p0076 := @g_vex y
  have p0077 := @g_uniex (.cv y) p0076
  have p0078 := @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv y)) R p0026 p0077
  have p0079 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
        (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))))
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      p0078
  have p0080 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0073 p0079
  have p0081 :=
    @g_biimpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0080
  have p0082 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0060 p0081
  have p0084 :=
    @g_simpr (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))
  have p0085 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
      (syn_wbr (.cv y) (syn_csi R) (.cv z)) p0058 p0084
  have p0097 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))
      p0056
  have p0098 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv z) (syn_csn (syn_cuni (.cv z)))
      (syn_csi R) p0072 p0097
  have p0101 := @g_vex z
  have p0102 := @g_uniex (.cv z) p0101
  have p0103 := @g_brsnsi (syn_cuni (.cv y)) (syn_cuni (.cv z)) R p0077 p0102
  have p0104 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv z))))
        (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))))
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      p0103
  have p0105 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv y) (syn_csi R) (.cv z))
      (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv z))))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0098 p0104
  have p0106 :=
    @g_biimpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv y) (syn_csi R) (.cv z))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0105
  have p0107 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv y) (syn_csi R) (.cv z))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0085 p0106
  have p0108 :=
    @g_trd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) (syn_cuni (.cv z)) p0039 p0045 p0051 p0057
      p0082 p0107
  have p0121 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv z) (syn_csn (syn_cuni (.cv z)))
      (syn_csi R) p0066 p0097
  have p0126 := @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv z)) R p0026 p0102
  have p0127 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv z))))
        (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))))
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      p0126
  have p0128 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv x) (syn_csi R) (.cv z))
      (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv z))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))) p0121 p0127
  have p0129 :=
    @g_biimprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (.cv x) (syn_csi R) (.cv z))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))) p0128
  have p0130 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
          (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y))
          (syn_wbr (.cv y) (syn_csi R) (.cv z))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z)))
      (syn_wbr (.cv x) (syn_csi R) (.cv z)) p0108 p0129
  have p0131 :=
    @g_simp2 (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0132 := @g_simpl (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0133 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (.cv x) (syn_cpw1 D)) p0131 p0132
  have p0135 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (.cv x) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))))
      p0133 p0012
  have p0136 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0135
  have p0137 :=
    @g_simp1 (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0138 := @g_wppweantisym D R
  have p0139 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cantisym) D) p0137 p0138
  have p0145 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0135
  have p0147 := @g_simpr (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0148 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (.cv y) (syn_cpw1 D)) p0131 p0147
  have p0150 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (.cv y) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))))
      p0148 p0049
  have p0151 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0150
  have p0152 :=
    @g_simp3 (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0153 :=
    @g_simpl (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0154 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      (syn_wbr (.cv x) (syn_csi R) (.cv y)) p0152 p0153
  have p0166 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0150
  have p0167 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y)))
      (syn_csi R) p0136 p0166
  have p0173 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
        (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))))
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      p0078
  have p0174 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0167 p0173
  have p0175 :=
    @g_biimpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0174
  have p0176 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0154 p0175
  have p0178 :=
    @g_simpr (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0179 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      (syn_wbr (.cv y) (syn_csi R) (.cv x)) p0152 p0178
  have p0192 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv x) (syn_csn (syn_cuni (.cv x)))
      (syn_csi R) p0166 p0136
  have p0197 := @g_brsnsi (syn_cuni (.cv y)) (syn_cuni (.cv x)) R p0077 p0026
  have p0198 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
        (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))))
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      p0197
  have p0199 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0192 p0198
  have p0200 :=
    @g_biimpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0199
  have p0201 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0179 p0200
  have p0202 :=
    @g_antid
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0139 p0145 p0151 p0176 p0201
  have p0203 :=
    @g_sneqd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0202
  have p0204 :=
    @g_eqtrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csn (syn_cuni (.cv y))) p0136 p0203
  have p0211 :=
    @g_eqcomd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.cv y) (syn_csn (syn_cuni (.cv y))) p0166
  have p0212 :=
    @g_eqtrd
      (syn_w3a (syn_wbr R (syn_cwe) D)
        (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
        (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
      (.cv x) (syn_csn (syn_cuni (.cv y))) (.cv y) p0204 p0211
  have p0213 :=
    @g_simp1 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
      (.classMem (.cv y) (syn_cpw1 D))
  have p0214 := @g_wppweconnex D R
  have p0215 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cconnex) D) p0213 p0214
  have p0216 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
      (.classMem (.cv y) (syn_cpw1 D))
  have p0218 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (.cv x) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))))
      p0216 p0012
  have p0219 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0218
  have p0220 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
      (.classMem (.cv y) (syn_cpw1 D))
  have p0222 :=
    @g_syl
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (.cv y) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))))
      p0220 p0049
  have p0223 :=
    @g_simpld
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0222
  have p0224 :=
    @g_connexd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0215 p0219 p0223
  have p0228 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))
      p0218
  have p0232 :=
    @g_simprd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))
      p0222
  have p0233 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y)))
      (syn_csi R) p0228 p0232
  have p0239 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
        (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))))
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      p0078
  have p0240 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y))))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0233 p0239
  have p0241 :=
    @g_biimprd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0240
  have p0242 :=
    @g_orc (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0243 :=
    @g_syl6
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      p0241 p0242
  have p0252 :=
    @g_breq12d
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv x) (syn_csn (syn_cuni (.cv x)))
      (syn_csi R) p0232 p0228
  have p0258 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
        (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))))
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      p0197
  have p0259 :=
    @g_bitrd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x))))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0252 p0258
  have p0260 :=
    @g_biimprd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0259
  have p0261 :=
    @g_olc (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (.cv x) (syn_csi R) (.cv y))
  have p0262 :=
    @g_syl6
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x)))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      p0260 p0261
  have p0263 :=
    @g_jaod
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))
      (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0243 p0262
  have p0264 :=
    @g_mpd
      (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
        (.classMem (.cv y) (syn_cpw1 D)))
      (syn_wo (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))
        (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))))
      (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
      p0224 p0263
  have p0265_e04_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
          (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))))
        (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0212
  have p0265 :=
    @g_sod (syn_wbr R (syn_cwe) D) x y z (syn_cpw1 D) (syn_csi R) (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0003 p0007 p0033 p0130 p0265_e04_recanon p0264
  exact p0265


end NFChoice.DirectNominalPrf.WPPReplay

end
