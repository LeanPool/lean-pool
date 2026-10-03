/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppreachincballfin (C : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachincballfin_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachincballfin_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let e : Var := freshVar proofSupport 3
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_m_ne_d : m ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_m : d ≠ m := Ne.symm fresh_m_ne_d
  have fresh_m_ne_e : m ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_e_ne_m : e ≠ m := Ne.symm fresh_m_ne_e
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have dv_cache_0001 : n ∉ ((syn_cwppreachincb F C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, fresh_n_not_C, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (C).fv (F).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0003 : d ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0006 : Disjoint (C).fv ((syn_ctc (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (C).fv ((syn_ctc (.cv m))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc];
          exact
            (show Disjoint ((C).fv) (((Class.cv m)).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint ((C).fv) (({ m } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show m ∉ (C).fv from (by exact fresh_m_not_C))))))))
  have dv_cache_0007 : Disjoint (F).fv ((syn_ctc (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (F).fv ((syn_ctc (.cv m))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc];
          exact
            (show Disjoint ((F).fv) (((Class.cv m)).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint ((F).fv) (({ m } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show m ∉ (F).fv from (by exact fresh_m_not_F))))))))
  have dv_cache_0008 : e ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_m, not_false_eq_true])
  have dv_cache_0009 : e ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_C, not_false_eq_true])
  have dv_cache_0010 : e ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_F, not_false_eq_true])
  have dv_cache_0011 : e ∉ ((syn_cfv F (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_F, or_false, not_false_eq_true])
  have dv_cache_0012 : e ∉ ((syn_cdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_e_not_F,
          not_false_eq_true])
  have dv_cache_0013 :
    e ∉
      ((syn_wb (.classMem (syn_cfv F (.cv d)) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d))
            (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          Finset.mem_union, Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_F,
          fresh_e_ne_m, fresh_e_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    d ∉
      ((syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, Finset.mem_singleton, fresh_d_ne_m, fresh_d_not_C,
          fresh_d_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : d ∉ ((syn_cplc (.cv m) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : n ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((Wff.classMem (.cv m) (syn_cwppreachincb F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_C,
          fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0018 : m ∉ ((Wff.classMem (.cv n) (syn_cwppreachincb F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_C,
          fresh_m_not_F, or_false, not_false_eq_true])
  have dv_cache_0019 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwppreachincb F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((Wff.classMem N (syn_cwppreachincb F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, fresh_n_not_N, fresh_n_not_C, fresh_n_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0021 :
    n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_C,
          fresh_n_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wppreachincballfin_1 p0000
  have p0002 := @g_wppreachincbex C F p0001
  have p0003 := @g_abid2 n (syn_cwppreachincb F C) dv_cache_0001
  have p0004 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwppreachincb F C))) (syn_cwppreachincb F C)
      (syn_cvv) p0003
  have p0005 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwppreachincb F C))) (syn_cvv))
      (.classMem (syn_cwppreachincb F C) (syn_cvv)) p0002 p0004
  have p0006 := @g_id (.classEq (.cv n) (syn_c0c))
  have p0007 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwppreachincb F C) p0006
  have p0008 := @g_id (.classEq (.cv n) (.cv m))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwppreachincb F C) p0008
  have p0010 := @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n)
      (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C) p0010
  have p0012 := @g_id (.classEq (.cv n) N)
  have p0013 := @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwppreachincb F C) p0012
  have p0014 := @g_tc0c
  have p0015 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0014
  have p0018 := @g_wppreach0 C F dv_cache_0002 p0001
  have p0019 :=
    @g_eqtri
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (syn_c0c)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_c0c))
      (syn_cima (syn_clec) (syn_csn C)) p0015 p0018
  have p0020 := @g_peano1
  have p0023 := @g_wpppowlayerseqfvcl (syn_c0c) C F dv_cache_0002 p0001
  have p0024 := Nominal.mp p0020 p0023
  have p0026 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      p0014
  have p0029 := @g_wpppowcore0 F p0001
  have p0030 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) p0026 p0029
  have p0031 :=
    @g_cnveqi (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
      (syn_cid) p0030
  have p0032 := @g_cnvi
  have p0033 :=
    @g_eqtri
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))))
      (syn_ccnv (syn_cid)) (syn_cid) p0031 p0032
  have p0034 :=
    @g_imaeq1i
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))))
      (syn_cid) (syn_cima (syn_clec) (syn_csn C)) p0033
  have p0035 := @g_imai (syn_cima (syn_clec) (syn_csn C))
  have p0036 :=
    @g_eqtri
      (syn_cima (syn_ccnv
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_cid) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_clec) (syn_csn C)) p0034 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c)))
      (syn_cima (syn_ccnv
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_clec) (syn_csn C)) p0024 p0036
  have p0038 :=
    @g_eqcomi (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c)))
      (syn_cima (syn_clec) (syn_csn C)) p0037
  have p0039 :=
    @g_eqtri
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (syn_c0c)))
      (syn_cima (syn_clec) (syn_csn C))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) p0019 p0038
  have p0040 :=
    @g_eleq2i
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (syn_c0c)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) (.cv d) p0039
  have p0041 :=
    @g_a1i
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (syn_c0c))))
        (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c)))))
      (.classMem (.cv d) (syn_cdm F)) p0040
  have p0042 :=
    @g_rgen
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (syn_c0c))))
        (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c)))))
      d (syn_cdm F) p0041
  have p0046 :=
    @g_wppreachincblayerscl (syn_c0c) C F d dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0005 p0001
  have p0047 := Nominal.mp p0020 p0046
  have p0048 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwppreachincb F C))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (syn_c0c))))
          (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))))))
      p0042 p0047
  have p0049 :=
    @g_simpl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv d) (syn_cdm F))
  have p0050 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv m) (syn_cnnc)) p0049 p0050
  have p0052 := @g_nntcsuc (.cv m)
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      p0051 p0052
  have p0054 :=
    @g_fveq2d
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0053
  have p0058 := @g_nntccl (.cv m)
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0051 p0058
  have p0062 :=
    @g_wppreachsucndv C F (syn_ctc (.cv m)) dv_cache_0002 dv_cache_0006 dv_cache_0007
      p0001
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_ctc (.cv m)) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cima (syn_ccnv F)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))))
      p0059 p0062
  have p0064 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      (syn_cima (syn_ccnv F)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      p0054 p0063
  have p0065 :=
    @g_eleq2d
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (syn_cplc (.cv m) (syn_c1c))))
      (syn_cima (syn_ccnv F)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      (.cv d) p0064
  have p0066 := @g_elfunsi F
  have p0067 := Nominal.mp hyp_wppreachincballfin_1 p0066
  have p0068 := @g_funfn F
  have p0069 := @g_biimpi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0068
  have p0070 := Nominal.mp p0067 p0069
  have p0071 :=
    @g_elpreima (syn_cdm F) (.cv d)
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (.cv m)))
      F
  have p0072 := Nominal.mp p0070 p0071
  have p0073 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))) (syn_wa (.classMem (.cv d) (syn_cdm F))
          (.classMem (syn_cfv F (.cv d)) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      p0072
  have p0074 :=
    @g_simpr
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv d) (syn_cdm F))
  have p0075 :=
    @g_biantrurd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d) (syn_cdm F))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      p0074
  have p0076 :=
    @g_bicomd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))))
      p0075
  have p0077 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d) (syn_cima (syn_ccnv F)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))))
      (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      p0073 p0076
  have p0078 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (.cv d) (syn_cima (syn_ccnv F)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      p0065 p0077
  have p0081 :=
    @g_a1i (syn_wfun F)
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      p0067
  have p0083 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_wfun F) (.classMem (.cv d) (syn_cdm F)) p0081 p0074
  have p0084 := @g_fvelrn (.cv d) F
  have p0085 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_wa (syn_wfun F) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_cfv F (.cv d)) (syn_crn F)) p0083 p0084
  have p0086 :=
    @g_sseli (syn_crn F) (syn_cdm F) (syn_cfv F (.cv d)) hyp_wppreachincballfin_2
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_cfv F (.cv d)) (syn_crn F))
      (.classMem (syn_cfv F (.cv d)) (syn_cdm F)) p0085 p0086
  have p0089 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0093 :=
    @g_wppreachincblayerscl (.cv m) C F e dv_cache_0008 dv_cache_0002 dv_cache_0009
      dv_cache_0010 p0001
  have p0094 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wb (.classMem (.cv m) (syn_cwppreachincb F C)) (syn_wral e (syn_cdm F) (syn_wb
            (.classMem (.cv e) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc (.cv m))))
            (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))))
      p0050 p0093
  have p0095 :=
    @g_biimpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv m) (syn_cwppreachincb F C))
      (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))
          (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))
      p0094
  have p0096 :=
    @g_mpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv m) (syn_cwppreachincb F C))
      (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))
          (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))
      p0089 p0095
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))
          (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))
      p0049 p0096
  have p0098 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_cfv F (.cv d)) (syn_cdm F))
      (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv m))))
          (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))
      p0087 p0097
  have p0099 := @g_id (.classEq (.cv e) (syn_cfv F (.cv d)))
  have p0100 :=
    @g_eleq1d (.classEq (.cv e) (syn_cfv F (.cv d))) (.cv e) (syn_cfv F (.cv d))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (.cv m)))
      p0099
  have p0102 :=
    @g_eleq1d (.classEq (.cv e) (syn_cfv F (.cv d))) (.cv e) (syn_cfv F (.cv d))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))) p0099
  have p0103 :=
    @g_bibi12d (.classEq (.cv e) (syn_cfv F (.cv d)))
      (.classMem (.cv e)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      p0100 p0102
  have p0104 :=
    @g_rspcva
      (syn_wb (.classMem (.cv e)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m))))
        (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      (syn_wb (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      e (syn_cfv F (.cv d)) (syn_cdm F) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0103
  have p0105 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_wa (.classMem (syn_cfv F (.cv d)) (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb
            (.classMem (.cv e) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc (.cv m))))
            (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))))
      (syn_wb (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      p0098 p0104
  have p0106 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (syn_cfv F (.cv d))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv m))))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      p0078 p0105
  have p0112 :=
    @g_elpreima (syn_cdm F) (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))
      F
  have p0113 := Nominal.mp p0070 p0112
  have p0114 :=
    @g_a1i
      (syn_wb (.classMem (.cv d)
          (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
        (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d))
            (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      p0113
  have p0116 :=
    @g_biantrurd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d) (syn_cdm F))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      p0074
  have p0117 :=
    @g_bicomd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      p0116
  have p0118 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d))
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      p0114 p0117
  have p0119 :=
    @g_bicomd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      p0118
  have p0120 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      (.classMem (.cv d)
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      p0106 p0119
  have p0126 := @g_wpppowlayerseqsuc C m F dv_cache_0002 p0001
  have p0127 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      p0051 p0126
  have p0128 :=
    @g_eleq2d
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))
      (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))
      (.cv d) p0127
  have p0129 :=
    @g_bicomd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (.cv d)
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      p0128
  have p0130 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F)))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (.cv d)
        (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))
      (.classMem (.cv d)
        (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))))
      p0120 p0129
  have p0131 :=
    @g_ralrimiva
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d)
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))))
      d (syn_cdm F) dv_cache_0014 p0130
  have p0133 := @g_peano2 (.cv m)
  have p0134 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      p0050 p0133
  have p0137 :=
    @g_wppreachincblayerscl (syn_cplc (.cv m) (syn_c1c)) C F d dv_cache_0015 dv_cache_0002
      dv_cache_0004 dv_cache_0005 p0001
  have p0138 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C))
        (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d)
              (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))))))
      p0134 p0137
  have p0139 :=
    @g_mpbird
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d)
            (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))))))
      p0131 p0138
  have p0140 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C)) p0139
  have p0141_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C))
          (.classMem (.cv m) (syn_cwppreachincb F C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwppreachincb syn_cuni1 syn_cuni syn_wex syn_wa syn_cin
          syn_ccompl syn_cnin syn_wnan syn_c1c
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0141 :=
    @g_finds (.classMem (.cv n) (syn_cwppreachincb F C))
      (.classMem (syn_c0c) (syn_cwppreachincb F C))
      (.classMem (.cv m) (syn_cwppreachincb F C))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C))
      (.classMem N (syn_cwppreachincb F C)) n m N dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0005 p0007
      p0141_e02_recanon p0011 p0013 p0048 p0140
  exact p0141

@[expose]
noncomputable def g_wppreachpowlayers (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_N_d : d ∉ N.fv) (hyp_wppreachpowlayers_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachpowlayers_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc N)))
            (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : d ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_d, not_false_eq_true])
  have dv_cache_0003 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0004 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_d, not_false_eq_true])
  have p0000 :=
    @g_wppreachincballfin C F N dv_cache_0001 hyp_wppreachpowlayers_1
      hyp_wppreachpowlayers_2
  have p0001 := @g_elex F (syn_cfuns)
  have p0002 := Nominal.mp hyp_wppreachpowlayers_1 p0001
  have p0003 :=
    @g_wppreachincblayerscl N C F d dv_cache_0002 dv_cache_0001 dv_cache_0003
      dv_cache_0004 p0002
  have p0004 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N)))
          (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_wpppowlayerorbcl (B : Class) (C : Class) (D : Class) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerorbcl_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowlayerorbcl_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowlayerorbcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc))
        (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_C, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0004 : n ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0005 :
    n ∉
      ((Wff.imp (.classMem B (syn_cnnc))
          (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_D, fresh_n_not_C, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_sneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C)
      p0004
  have p0006 :=
    @g_eleq2d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) D p0005
  have p0008 := @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F D) p0001
  have p0009 :=
    @g_breq2d (.classEq (.cv n) B) (syn_cfv (syn_cfrec F D) (.cv n))
      (syn_cfv (syn_cfrec F D) B) C (syn_clec) p0008
  have p0010 :=
    @g_bibi12d (.classEq (.cv n) B)
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)) p0006 p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))
      (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)))
      p0002 p0010
  have p0012 :=
    @g_wpppowlayerorb C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wpppowlayerorbcl_1 hyp_wpppowlayerorbcl_2 hyp_wpppowlayerorbcl_3
  have p0013 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc))
        (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))))
      (.imp (.classMem B (syn_cnnc))
        (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B))))
      n B (syn_cnnc) dv_cache_0004 dv_cache_0005 p0011 p0012
  have p0014 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)))
      p0000 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppreachlayerorbfin (C : Class) (D : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachlayerorbfin_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachlayerorbfin_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachlayerorbfin_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ N.fv
  let e : Var := freshVar proofSupport 0
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_e_not_D : e ∉ D.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_N : e ∉ N.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : e ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_C, not_false_eq_true])
  have dv_cache_0003 : e ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_F, not_false_eq_true])
  have dv_cache_0004 : e ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_N, not_false_eq_true])
  have dv_cache_0005 : e ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_D, not_false_eq_true])
  have dv_cache_0006 : e ∉ ((syn_cdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_e_not_F,
          not_false_eq_true])
  have dv_cache_0007 :
    e ∉
      ((syn_wb (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N)))
          (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          Finset.mem_union, fresh_e_not_D, fresh_e_not_N, fresh_e_not_F, fresh_e_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_a1i (.classMem D (syn_cdm F)) (.classMem N (syn_cnnc)) hyp_wppreachlayerorbfin_2
  have p0001 :=
    @g_wppreachpowlayers C F N e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_wppreachlayerorbfin_1 hyp_wppreachlayerorbfin_3
  have p0002 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem D (syn_cdm F))
      (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N)))
          (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))))
      p0000 p0001
  have p0003 := @g_id (.classEq (.cv e) D)
  have p0004 :=
    @g_eleq1d (.classEq (.cv e) D) (.cv e) D
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc N))
      p0003
  have p0006 :=
    @g_eleq1d (.classEq (.cv e) D) (.cv e) D
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)) p0003
  have p0007 :=
    @g_bibi12d (.classEq (.cv e) D)
      (.classMem (.cv e)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc N)))
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc N)))
      (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))) p0004 p0006
  have p0008 :=
    @g_rspcva
      (syn_wb (.classMem (.cv e)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc N))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))
      (syn_wb (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))
      e D (syn_cdm F) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wa (.classMem D (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e)
              (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc N)))
            (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))))
      (syn_wb (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))
      p0002 p0008
  have p0010 :=
    @g_wpppowlayerorbcl N C D F dv_cache_0001 hyp_wppreachlayerorbfin_1
      hyp_wppreachlayerorbfin_2 hyp_wppreachlayerorbfin_3
  have p0011 :=
    @g_bitrd (.classMem N (syn_cnnc))
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc N)))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)) p0009 p0010
  exact p0011

@[expose]
noncomputable def g_strictsegdifinindv (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    y ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    y ∉
      ((syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, or_false,
          not_false_eq_true])
  have p0000 := @g_elstrictseg x y D R
  have p0001 :=
    @g_eldifsn (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (.cv x)
  have p0002 := @g_elin (.cv y) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0003 := @g_eliniseg R (.cv x) (.cv y)
  have p0004 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) D) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) p0002 p0004
  have p0006 :=
    @g_anbi1i (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) (syn_wne (.cv y) (.cv x))
      p0005
  have p0007 :=
    @g_bitri
      (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
        (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)))
        (syn_wne (.cv y) (.cv x)))
      p0001 p0006
  have p0008 :=
    @g_anass (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0009 :=
    @g_bitri
      (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)))
        (syn_wne (.cv y) (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0007 p0008
  have p0010 :=
    @g_bitr4i
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      p0000 p0009
  have p0011 :=
    @g_eqriv y (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
      dv_cache_0001 dv_cache_0002 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisoendpointseqndv (x : Var) (y : Var) (D : Class) (R : Class)
    (H : Class) (hyp_wecutisoendpointseqndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (.cv x) (.cv y))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wne (.cv x) (.cv y))
  have p0001 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0000 p0001
  have p0003 := @g_wppweconnex D R
  have p0004 := Nominal.mp hyp_wecutisoendpointseqndv_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0008 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) p0007 p0008
  have p0010 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0009
      p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D) p0000 p0011
  have p0017 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0009
      p0017
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) D) p0000 p0018
  have p0020 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0012 p0019
  have p0021 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      hyp_wecutisoendpointseqndv_1
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0022 p0019
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0021 p0030
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0022 p0012
  have p0041 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0043 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wne (.cv x) (.cv y))
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv x) (.cv y)) p0022 p0043
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0041 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0040 p0045
  have p0047 := @g_elstrictseg y x D R
  have p0048 :=
    @g_biimpri
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      p0047
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0046 p0048
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0031 p0049
  have p0054 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (.classMem H (syn_cvv)) p0007 p0054
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem H (syn_cvv)) p0000 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem H (syn_cvv)) p0022 p0056
  have p0058 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem H (syn_cvv)) p0050 p0057
  have p0059 := @g_strictsegltnoiso x y D R H
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0058 p0059
  have p0061 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0060
  have p0062 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      hyp_wecutisoendpointseqndv_1
  have p0063 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0063 p0012
  have p0072 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0062 p0071
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0063 p0019
  have p0082 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0085 :=
    @g_necomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0043
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv y) (.cv x)) p0063 p0085
  have p0087 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0082 p0086
  have p0088 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0081 p0087
  have p0089 := @g_elstrictseg x y D R
  have p0090 :=
    @g_biimpri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0089
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0088 p0090
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0072 p0091
  have p0099 := @g_cnvexg H (syn_cvv)
  have p0100 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem H (syn_cvv)) (.classMem (syn_ccnv H) (syn_cvv)) p0056 p0099
  have p0101 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (syn_ccnv H) (syn_cvv)) p0063 p0100
  have p0102 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (syn_ccnv H) (syn_cvv)) p0092 p0101
  have p0103 := @g_strictsegltnoiso y x D R (syn_ccnv H)
  have p0104 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (syn_ccnv H) (syn_cvv)))
      (.neg (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0102 p0103
  have p0105 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      H
  have p0106 :=
    @g_a1i
      (.imp (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      p0105
  have p0107 :=
    @g_con3d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0106
  have p0108 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.neg (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0104 p0107
  have p0109 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0108
  have p0110 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (.cv y) R (.cv x)) p0061 p0109
  have p0111 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0020 p0110
  have p0112 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.neg (syn_wne (.cv x) (.cv y))) p0002 p0111
  have p0113 :=
    @g_pm2_01da
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wne (.cv x) (.cv y)) p0112
  have p0114 := @g_nne (.cv x) (.cv y)
  have p0115 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0113 p0114
  exact p0115


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisoendpointseqclndv (B : Class) (C : Class) (D : Class)
    (R : Class) (H : Class)
    (hyp_wecutisoendpointseqclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (.classEq B C)) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0004 :
    y ∉
      ((Wff.imp (syn_wa
            (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
            (syn_wiso H (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
              (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (.classEq B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, fresh_y_not_B,
          fresh_y_not_D, fresh_y_not_C, fresh_y_not_H, fresh_y_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D))
              (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classEq B (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_H,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
  have p0001 := @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
      (syn_wa (.classMem B D) (.classMem C D)) p0000 p0001
  have p0003 := @g_simpl (.classMem B D) (.classMem C D)
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) p0002 p0003
  have p0005 := @g_elex B D
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (.classMem B D) (.classMem B (syn_cvv)) p0004 p0005
  have p0010 := @g_simpr (.classMem B D) (.classMem C D)
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) p0002 p0010
  have p0012 := @g_elex C D
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (.classMem C D) (.classMem C (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0006 p0013
  have p0015 := @g_eleq1 (.cv x) B D
  have p0016 := @g_biid (.classMem (.cv y) D)
  have p0017 :=
    @g_a1i (syn_wb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0016
  have p0018 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0015 p0017
  have p0019 := @g_biid (.classMem H (syn_cvv))
  have p0020 :=
    @g_a1i (syn_wb (.classMem H (syn_cvv)) (.classMem H (syn_cvv))) (.classEq (.cv x) B)
      p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))
      (.classMem H (syn_cvv)) p0018 p0020
  have p0022 := @g_sneq (.cv x) B
  have p0023 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B)
      (syn_ccnv (syn_cdif R (syn_cid))) p0022
  have p0024 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0023
  have p0028 :=
    @g_xpeq12d (.classEq (.cv x) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0024 p0024
  have p0029 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      R p0028
  have p0030 :=
    @g_isoeq2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      H
  have p0031 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))
      (syn_wb (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0029 p0030
  have p0035 :=
    @g_isoeq4 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      H
  have p0036 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_wb (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0024 p0035
  have p0037 :=
    @g_bitrd (.classEq (.cv x) B)
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0031 p0036
  have p0038 :=
    @g_anbi12d (.classEq (.cv x) B)
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0021 p0037
  have p0039 := @g_id (.classEq (.cv x) B)
  have p0040 := @g_eqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0039
  have p0041 :=
    @g_imbi12d (.classEq (.cv x) B)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0038 p0040
  have p0042 := @g_biid (.classMem B D)
  have p0043 := @g_a1i (syn_wb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0042
  have p0044 := @g_eleq1 (.cv y) C D
  have p0045 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0043 p0044
  have p0047 :=
    @g_a1i (syn_wb (.classMem H (syn_cvv)) (.classMem H (syn_cvv))) (.classEq (.cv y) C)
      p0019
  have p0048 :=
    @g_anbi12d (.classEq (.cv y) C) (syn_wa (.classMem B D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))
      (.classMem H (syn_cvv)) p0045 p0047
  have p0049 := @g_sneq (.cv y) C
  have p0050 :=
    @g_imaeq2d (.classEq (.cv y) C) (syn_csn (.cv y)) (syn_csn C)
      (syn_ccnv (syn_cdif R (syn_cid))) p0049
  have p0051 :=
    @g_ineq2d (.classEq (.cv y) C)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)) D p0050
  have p0055 :=
    @g_xpeq12d (.classEq (.cv y) C)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) p0051 p0051
  have p0056 :=
    @g_ineq2d (.classEq (.cv y) C)
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
      R p0055
  have p0057 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      H
  have p0058 :=
    @g_syl (.classEq (.cv y) C)
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))))
      (syn_wb (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0056 p0057
  have p0062 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      H
  have p0063 :=
    @g_syl (.classEq (.cv y) C)
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
      (syn_wb (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      p0051 p0062
  have p0064 :=
    @g_bitrd (.classEq (.cv y) C)
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
      p0058 p0063
  have p0065 :=
    @g_anbi12d (.classEq (.cv y) C)
      (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso H (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
      p0048 p0064
  have p0066 := @g_id (.classEq (.cv y) C)
  have p0067 := @g_eqeq2d (.classEq (.cv y) C) (.cv y) C B p0066
  have p0068 :=
    @g_imbi12d (.classEq (.cv y) C)
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (.classEq B (.cv y)) (.classEq B C) p0065 p0067
  have p0069 := @g_wecutisoendpointseqndv x y D R H hyp_wecutisoendpointseqclndv_1
  have p0070 :=
    @g_vtocl2g
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (.cv x) (.cv y)))
      (.imp (syn_wa
          (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq B (.cv y)))
      (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (.classEq B C))
      x y B C (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0041 p0068 p0069
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
        (.classEq B C))
      p0014 p0070
  have p0072 :=
    @g_pm2_43i
      (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)))
        (syn_wiso H (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
      (.classEq B C) p0071
  exact p0072

@[expose]
noncomputable def g_strictsegdifiniclndv (B : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cvv))
        (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)))) :=
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
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((Wff.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_R, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_sneq (.cv x) B
  have p0001 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B)
      (syn_ccnv (syn_cdif R (syn_cid))) p0000
  have p0002 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0001
  have p0004 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv R) p0000
  have p0005 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv R) (syn_csn B)) D p0004
  have p0007 :=
    @g_difeq12d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn (.cv x)) (syn_csn B) p0005
      p0000
  have p0008 :=
    @g_eqeq12d (.classEq (.cv x) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
      (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)) p0002 p0007
  have p0009 := @g_strictsegdifinindv x D R
  have p0010 :=
    @g_vtoclg
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))))
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)))
      x B (syn_cvv) dv_cache_0001 dv_cache_0002 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_isostrictsegimandv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (.classEq (syn_cima H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
              (syn_csn (syn_cfv H (.cv x))))))) :=
  by
  have p0000 := @g_strictsegdifinindv x D R
  have p0001 :=
    @g_a1i
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))))
      (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @g_imaeq2d (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) H
      p0001
  have p0003 := @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0004 := @g_isof1o D E R S H
  have p0005 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E)
      (syn_wf1o H D E) p0003 p0004
  have p0006 := @g_f1ocnv D E H
  have p0007 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E)
      (syn_wf1o (syn_ccnv H) E D) p0005 p0006
  have p0008 := @g_f1ofun E D (syn_ccnv H)
  have p0009 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o (syn_ccnv H) E D)
      (syn_wfun (syn_ccnv H)) p0007 p0008
  have p0010 :=
    @g_imadif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)) H
  have p0011 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wfun (syn_ccnv H))
      (.classEq (syn_cima H (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
            (syn_csn (.cv x))))
        (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
          (syn_cima H (syn_csn (.cv x)))))
      p0009 p0010
  have p0012 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cima H (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
        (syn_cima H (syn_csn (.cv x))))
      p0002 p0011
  have p0013 := @g_isoini D E (.cv x) R S H
  have p0017 := @g_f1ofn D E H
  have p0018 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E)
      (syn_wfn H D) p0005 p0017
  have p0019 := @g_simpr (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0020 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wfn H D)
      (.classMem (.cv x) D) p0018 p0019
  have p0021 := @g_fnsnfv D (.cv x) H
  have p0022 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (.classEq (syn_csn (syn_cfv H (.cv x))) (syn_cima H (syn_csn (.cv x)))) p0020 p0021
  have p0023 :=
    @g_eqcomd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_csn (syn_cfv H (.cv x))) (syn_cima H (syn_csn (.cv x))) p0022
  have p0024 :=
    @g_difeq12d (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cima H (syn_csn (.cv x))) (syn_csn (syn_cfv H (.cv x))) p0013 p0023
  have p0025 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
        (syn_cima H (syn_csn (.cv x))))
      (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x)))))
        (syn_csn (syn_cfv H (.cv x))))
      p0012 p0024
  have p0029 := @g_f1of D E H
  have p0030 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E)
      (syn_wf H D E) p0005 p0029
  have p0032 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf H D E)
      (.classMem (.cv x) D) p0030 p0019
  have p0033 := @g_ffvelrn D E (.cv x) H
  have p0034 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (syn_wf H D E) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) E)
      p0032 p0033
  have p0035 := @g_elex (syn_cfv H (.cv x)) E
  have p0036 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (.classMem (syn_cfv H (.cv x)) E) (.classMem (syn_cfv H (.cv x)) (syn_cvv)) p0034
      p0035
  have p0037 := @g_strictsegdifiniclndv (syn_cfv H (.cv x)) E S
  have p0038 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (.classMem (syn_cfv H (.cv x)) (syn_cvv))
      (.classEq (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
        (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x)))))
          (syn_csn (syn_cfv H (.cv x)))))
      p0036 p0037
  have p0039 :=
    @g_eqcomd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x)))))
        (syn_csn (syn_cfv H (.cv x))))
      p0038
  have p0040 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x)))))
        (syn_csn (syn_cfv H (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      p0025 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isostrictsegresndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_H : u ∉ H.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_H : v ∉ H.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 :
    v ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_D, fresh_v_not_R, fresh_v_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_D, fresh_u_not_E, fresh_u_not_H,
          fresh_u_not_R, fresh_u_not_S, fresh_u_ne_x, or_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_D, fresh_v_not_E, fresh_v_not_H,
          fresh_v_not_R, fresh_v_not_S, fresh_v_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 :
    u ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_D, fresh_u_not_R, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    u ∉
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
            (syn_csn (syn_cfv H (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_E, fresh_u_not_S, fresh_u_ne_x, fresh_u_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    v ∉
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
            (syn_csn (syn_cfv H (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_x, fresh_v_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    u ∉
      ((syn_cres H (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_H, fresh_u_not_D, fresh_u_not_R, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    v ∉
      ((syn_cres H (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_H, fresh_v_not_D, fresh_v_not_R, fresh_v_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0012 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have dv_cache_0013 : v ∉ (S).fv :=
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
        simp only [fresh_v_not_S, not_false_eq_true])
  have p0000 := @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0001 := @g_isof1o D E R S H
  have p0002 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E)
      (syn_wf1o H D E) p0000 p0001
  have p0003 := @g_f1of1 D E H
  have p0004 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E)
      (syn_wf1 H D E) p0002 p0003
  have p0005 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0006 :=
    @g_a1i
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) p0005
  have p0007 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1 H D E)
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      p0004 p0006
  have p0008 :=
    @g_f1ores D E
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0009 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (syn_wf1 H D E) (syn_wss
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D))
      (syn_wf1o (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0007 p0008
  have p0010 := @g_isostrictsegimandv x D R S E H
  have p0011 :=
    @g_f1oeq3
      (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0012 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (.classEq (syn_cima H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wb (syn_wf1o (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_wf1o (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0010 p0011
  have p0013 :=
    @g_mpbid (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wf1o (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wf1o (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0009 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv u)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv v)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) p0014 p0000
  have p0017 :=
    @g_simpr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv u)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv v)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0018 :=
    @g_simpl
      (.classMem (.cv u)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv v)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wa (.classMem (.cv u)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv v)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv u)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0017 p0018
  have p0021 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D
      (.cv u) p0005
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv u)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv u) D) p0019 p0021
  have p0024 :=
    @g_simpr
      (.classMem (.cv u)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv v)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wa (.classMem (.cv u)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv v)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv v)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0017 p0024
  have p0027 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D
      (.cv v) p0005
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv v)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv v) D) p0025 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv u) D) (.classMem (.cv v) D) p0022 p0028
  have p0030 :=
    @g_jca
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wiso H R S D E) (syn_wa (.classMem (.cv u) D) (.classMem (.cv v) D)) p0016
      p0029
  have p0031 := @g_isorel D E (.cv u) (.cv v) R S H
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wa (syn_wiso H R S D E) (syn_wa (.classMem (.cv u) D) (.classMem (.cv v) D)))
      (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v))))
      p0030 p0031
  have p0036 :=
    @g_fvres (.cv u)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv u)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u))
        (syn_cfv H (.cv u)))
      p0019 p0036
  have p0041 :=
    @g_fvres (.cv v)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv v)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v))
        (syn_cfv H (.cv v)))
      p0025 p0041
  have p0043 :=
    @g_breq12d
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cfv (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u))
      (syn_cfv H (.cv u))
      (syn_cfv (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v))
      (syn_cfv H (.cv v)) S p0037 p0042
  have p0044 :=
    @g_bibi2d
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wbr (syn_cfv (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u))
        S (syn_cfv (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.cv v)))
      (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v))) (syn_wbr (.cv u) R (.cv v))
      p0043
  have p0045 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv v)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.cv u)) S (syn_cfv (syn_cres H
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.cv v))))
      (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v))))
      p0032 p0044
  have p0046 :=
    @g_ralrimivva (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.cv u)) S (syn_cfv (syn_cres H
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.cv v))))
      u v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0045
  have p0047 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wf1o (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wral u (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_wral v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S
              (syn_cfv (syn_cres H (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
                (.cv v))))))
      p0013 p0046
  have p0048 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso u v
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      R S
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0004
  have p0049 :=
    @g_sylibr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (syn_wf1o (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wral u (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_wral v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u))
                S (syn_cfv (syn_cres H (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
                  (.cv v)))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0047 p0048
  have p0050 :=
    @g_isores1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      R S
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0051 :=
    @g_sylib (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0049 p0050
  have p0052 :=
    @g_isores2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      S
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0053 :=
    @g_sylib (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0051 p0052
  exact p0053


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_weisouniquecl (D : Class) (R : Class) (S : Class) (E : Class)
    (F : Class) (G : Class) (hyp_weisouniquecl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_weisouniquecl_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classEq F G)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0003 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R,
          fresh_x_not_S, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0001 := @g_simpl (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso F R S D E) p0000 p0001
  have p0003 := @g_isof1o D E R S F
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wiso F R S D E) (syn_wf1o F D E) p0002 p0003
  have p0005 := @g_f1ofn D E F
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf1o F D E) (syn_wfn F D) p0004 p0005
  have p0008 := @g_simpr (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso G R S D E) p0000 p0008
  have p0010 := @g_isof1o D E R S G
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wiso G R S D E) (syn_wf1o G D E) p0009 p0010
  have p0012 := @g_f1ofn D E G
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf1o G D E) (syn_wfn G D) p0011 p0012
  have p0014 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (.classMem (.cv x) D)
  have p0020 := @g_f1of D E F
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf1o F D E) (syn_wf F D E) p0004 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf F D E) p0014 p0021
  have p0023 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (.classMem (.cv x) D)
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wf F D E) (.classMem (.cv x) D) p0022 p0023
  have p0025 := @g_ffvelrn D E (.cv x) F
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wf F D E) (.classMem (.cv x) D)) (.classMem (syn_cfv F (.cv x)) E)
      p0024 p0025
  have p0033 := @g_f1of D E G
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf1o G D E) (syn_wf G D E) p0011 p0033
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wf G D E) p0014 p0034
  have p0037 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wf G D E) (.classMem (.cv x) D) p0035 p0023
  have p0038 := @g_ffvelrn D E (.cv x) G
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wf G D E) (.classMem (.cv x) D)) (.classMem (syn_cfv G (.cv x)) E)
      p0037 p0038
  have p0040 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E) p0026 p0039
  have p0042 :=
    @g_simpl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0043 := @g_simpr (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem G (syn_cvv))
      p0042 p0043
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (.classMem G (syn_cvv)) p0014 p0044
  have p0046 := @g_brex R D (syn_cwe)
  have p0047 := Nominal.mp hyp_weisouniquecl_1 p0046
  have p0048 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0049 := Nominal.mp p0047 p0048
  have p0052 := @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0053 := Nominal.mp p0047 p0052
  have p0054 := @g_idex
  have p0055 := @g_difex R (syn_cid) p0053 p0054
  have p0056 := @g_cnvex (syn_cdif R (syn_cid)) p0055
  have p0057 := @g_snex (.cv x)
  have p0058 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0056 p0057
  have p0059 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0049 p0058
  have p0060 :=
    @g_a1i
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      p0059
  have p0061 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (.classMem G (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0045 p0060
  have p0062 :=
    @g_resexg G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cvv) (syn_cvv)
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (.classMem G (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)))
      (.classMem (syn_cres G
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      p0061 p0062
  have p0066 := @g_simpl (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem F (syn_cvv))
      p0042 p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (.classMem F (syn_cvv)) p0014 p0067
  have p0084 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (.classMem F (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0068 p0060
  have p0085 :=
    @g_resexg F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cvv) (syn_cvv)
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (.classMem F (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)))
      (.classMem (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      p0084 p0085
  have p0087 :=
    @g_cnvexg
      (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cvv)
  have p0088 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      (.classMem (syn_ccnv (syn_cres F
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      p0086 p0087
  have p0089 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (syn_cres G
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      (.classMem (syn_ccnv (syn_cres F
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      p0063 p0088
  have p0090 :=
    @g_coexg
      (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_ccnv (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cvv) (syn_cvv)
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cvv)) (.classMem (syn_ccnv (syn_cres F
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cvv)))
      (.classMem (syn_ccom (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_ccnv (syn_cres F (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv))
      p0089 p0090
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E))
      (.classMem (syn_ccom (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_ccnv (syn_cres F (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv))
      p0040 p0091
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wiso F R S D E) p0014 p0002
  have p0099 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wiso F R S D E) (.classMem (.cv x) D) p0097 p0023
  have p0100 := @g_isostrictsegresndv x D R S E F
  have p0101 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wiso F R S D E) (.classMem (.cv x) D))
      (syn_wiso (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))
      p0099 p0100
  have p0102 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))))
      (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0103 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wiso (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))
      (syn_wiso (syn_ccnv (syn_cres F
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0101 p0102
  have p0108 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      (syn_wiso G R S D E) p0014 p0009
  have p0110 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wiso G R S D E) (.classMem (.cv x) D) p0108 p0023
  have p0111 := @g_isostrictsegresndv x D R S E G
  have p0112 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wiso G R S D E) (.classMem (.cv x) D))
      (syn_wiso (syn_cres G
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv G (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))
      p0110 p0111
  have p0113 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wiso (syn_ccnv (syn_cres F
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (syn_cres G
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv G (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))
      p0103 p0112
  have p0114 :=
    @g_isotr
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))))
      (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_ccnv (syn_cres F
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0115 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wiso (syn_ccnv (syn_cres F
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv F (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso
          (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv G (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))))
      (syn_wiso (syn_ccom (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_ccnv (syn_cres F (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv G (.cv x))))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))
      p0113 p0114
  have p0116 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E))
        (.classMem (syn_ccom (syn_cres G
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_ccnv (syn_cres F (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv)))
      (syn_wiso (syn_ccom (syn_cres G
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_ccnv (syn_cres F (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv F (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv G (.cv x))))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))
      p0092 p0115
  have p0117 :=
    @g_wecutisoendpointseqclndv (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) E S
      (syn_ccom (syn_cres G
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv
          (syn_cres F
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      hyp_weisouniquecl_2
  have p0118 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
          (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D))
      (syn_wa (syn_wa
          (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E))
          (.classMem (syn_ccom (syn_cres G (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv
                (syn_cres F (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
            (syn_cvv))) (syn_wiso (syn_ccom (syn_cres G
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_ccnv (syn_cres F (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv F (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv G (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))))
      (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) p0116 p0117
  have p0119 :=
    @g_eqfnfvd
      (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))
      x D F G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0013 p0118
  exact p0119

@[expose]
noncomputable def g_wecutisouniquecl (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (E : Class) (F : Class) (G : Class)
    (hyp_wecutisouniquecl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisouniquecl_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F
              (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
              (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))) (syn_wiso G
              (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
              (syn_cin S (syn_cxp
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))))))
        (.classEq F G)) :=
  by
  have p0000 := @g_id (syn_wbr R (syn_cwe) D)
  have p0001 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))
  have p0002 :=
    @g_a1i
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) D)
      (syn_wbr R (syn_cwe) D) p0001
  have p0003 := @g_brex R D (syn_cwe)
  have p0004 := Nominal.mp hyp_wecutisouniquecl_1 p0003
  have p0005 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0006 := Nominal.mp p0004 p0005
  have p0009 := @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0010 := Nominal.mp p0004 p0009
  have p0011 := @g_idex
  have p0012 := @g_difex R (syn_cid) p0010 p0011
  have p0013 := @g_cnvex (syn_cdif R (syn_cid)) p0012
  have p0014 := @g_snex B
  have p0015 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B) p0013 p0014
  have p0016 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) p0006 p0015
  have p0017 :=
    @g_a1i
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cvv))
      (syn_wbr R (syn_cwe) D) p0016
  have p0018 :=
    @g_werestrndv (syn_wbr R (syn_cwe) D)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) D R p0000 p0002
      p0017
  have p0019 := Nominal.mp hyp_wecutisouniquecl_1 p0018
  have p0020 := @g_id (syn_wbr S (syn_cwe) E)
  have p0021 := @g_inss1 E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))
  have p0022 :=
    @g_a1i
      (syn_wss (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) E)
      (syn_wbr S (syn_cwe) E) p0021
  have p0023 := @g_brex S E (syn_cwe)
  have p0024 := Nominal.mp hyp_wecutisouniquecl_2 p0023
  have p0025 := @g_simpr (.classMem S (syn_cvv)) (.classMem E (syn_cvv))
  have p0026 := Nominal.mp p0024 p0025
  have p0029 := @g_simpl (.classMem S (syn_cvv)) (.classMem E (syn_cvv))
  have p0030 := Nominal.mp p0024 p0029
  have p0032 := @g_difex S (syn_cid) p0030 p0011
  have p0033 := @g_cnvex (syn_cdif S (syn_cid)) p0032
  have p0034 := @g_snex C
  have p0035 := @g_imaex (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C) p0033 p0034
  have p0036 :=
    @g_inex E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)) p0026 p0035
  have p0037 :=
    @g_a1i
      (.classMem (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) (syn_cvv))
      (syn_wbr S (syn_cwe) E) p0036
  have p0038 :=
    @g_werestrndv (syn_wbr S (syn_cwe) E)
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) E S p0020 p0022
      p0037
  have p0039 := Nominal.mp hyp_wecutisouniquecl_2 p0038
  have p0040 :=
    @g_weisouniquecl (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) F G p0019 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end
