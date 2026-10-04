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

/-- Checked nominal proof certificate identified upstream as `g_wppreachincballfin`. -/
@[expose]
noncomputable def gWppreachincballfin (C : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachincballfin_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachincballfin_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem N (synCwppreachincb F C))) :=
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
  have dv_cache_0001 : n ∉ ((synCwppreachincb F C)).fv := by
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
  have dv_cache_0003 : d ∉ ((synC0c)).fv :=
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
  have dv_cache_0006 : Disjoint (C).fv ((synCtc (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (C).fv ((synCtc (.cv m))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc];
          exact
            (show Disjoint ((C).fv) (((Class.cv m)).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint ((C).fv) (({ m } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show m ∉ (C).fv from (by exact fresh_m_not_C))))))))
  have dv_cache_0007 : Disjoint (F).fv ((synCtc (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (F).fv ((synCtc (.cv m))).fv from (by
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
  have dv_cache_0011 : e ∉ ((synCfv F (.cv d))).fv :=
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
  have dv_cache_0012 : e ∉ ((synCdm F)).fv :=
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
      ((synWb (.classMem (synCfv F (.cv d)) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m)))) (.classMem (synCfv F (.cv d))
            (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))).fv :=
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
      ((synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C)))).fv :=
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
  have dv_cache_0015 : d ∉ ((synCplc (.cv m) (synC1c))).fv :=
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
  have dv_cache_0017 : n ∉ ((Wff.classMem (.cv m) (synCwppreachincb F C))).fv :=
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
  have dv_cache_0018 : m ∉ ((Wff.classMem (.cv n) (synCwppreachincb F C))).fv :=
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
  have dv_cache_0019 : n ∉ ((Wff.classMem (synC0c) (synCwppreachincb F C))).fv :=
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
  have dv_cache_0020 : n ∉ ((Wff.classMem N (synCwppreachincb F C))).fv :=
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
    n ∉ ((Wff.classMem (synCplc (.cv m) (synC1c)) (synCwppreachincb F C))).fv :=
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
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppreachincballfin_1 p0000
  have p0002 := @gWppreachincbex C F p0001
  have p0003 := @gAbid2 n (synCwppreachincb F C) dv_cache_0001
  have p0004 :=
    @gEleq1i (.cab n (.classMem (.cv n) (synCwppreachincb F C))) (synCwppreachincb F C)
      (synCvv) p0003
  have p0005 :=
    @gMpbir (.classMem (.cab n (.classMem (.cv n) (synCwppreachincb F C))) (synCvv))
      (.classMem (synCwppreachincb F C) (synCvv)) p0002 p0004
  have p0006 := @gId (.classEq (.cv n) (synC0c))
  have p0007 :=
    @gEleq1d (.classEq (.cv n) (synC0c)) (.cv n) (synC0c) (synCwppreachincb F C) p0006
  have p0008 := @gId (.classEq (.cv n) (.cv m))
  have p0009 :=
    @gEleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (synCwppreachincb F C) p0008
  have p0010 := @gId (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
  have p0011 :=
    @gEleq1d (.classEq (.cv n) (synCplc (.cv m) (synC1c))) (.cv n)
      (synCplc (.cv m) (synC1c)) (synCwppreachincb F C) p0010
  have p0012 := @gId (.classEq (.cv n) N)
  have p0013 := @gEleq1d (.classEq (.cv n) N) (.cv n) N (synCwppreachincb F C) p0012
  have p0014 := @gTc0c
  have p0015 :=
    @gFveq2i (synCtc (synC0c)) (synC0c)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0014
  have p0018 := @gWppreach0 C F dv_cache_0002 p0001
  have p0019 :=
    @gEqtri
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (synC0c)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synC0c))
      (synCima (synClec) (synCsn C)) p0015 p0018
  have p0020 := @gPeano1
  have p0023 := @gWpppowlayerseqfvcl (synC0c) C F dv_cache_0002 p0001
  have p0024 := Nominal.mp p0020 p0023
  have p0026 :=
    @gFveq2i (synCtc (synC0c)) (synC0c) (synCfrec (synCwpppostcomp F) (synCid))
      p0014
  have p0029 := @gWpppowcore0 F p0001
  have p0030 :=
    @gEqtri (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) (synCid) p0026 p0029
  have p0031 :=
    @gCnveqi (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
      (synCid) p0030
  have p0032 := @gCnvi
  have p0033 :=
    @gEqtri
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c))))
      (synCcnv (synCid)) (synCid) p0031 p0032
  have p0034 :=
    @gImaeq1i
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c))))
      (synCid) (synCima (synClec) (synCsn C)) p0033
  have p0035 := @gImai (synCima (synClec) (synCsn C))
  have p0036 :=
    @gEqtri
      (synCima (synCcnv
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c))))
        (synCima (synClec) (synCsn C)))
      (synCima (synCid) (synCima (synClec) (synCsn C)))
      (synCima (synClec) (synCsn C)) p0034 p0035
  have p0037 :=
    @gEqtri (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c)))
      (synCima (synCcnv
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c))))
        (synCima (synClec) (synCsn C)))
      (synCima (synClec) (synCsn C)) p0024 p0036
  have p0038 :=
    @gEqcomi (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c)))
      (synCima (synClec) (synCsn C)) p0037
  have p0039 :=
    @gEqtri
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (synC0c)))
      (synCima (synClec) (synCsn C))
      (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c))) p0019 p0038
  have p0040 :=
    @gEleq2i
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (synC0c)))
      (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c))) (.cv d) p0039
  have p0041 :=
    @gA1i
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (synC0c))))
        (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c)))))
      (.classMem (.cv d) (synCdm F)) p0040
  have p0042 :=
    @gRgen
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (synC0c))))
        (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c)))))
      d (synCdm F) p0041
  have p0046 :=
    @gWppreachincblayerscl (synC0c) C F d dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0005 p0001
  have p0047 := Nominal.mp p0020 p0046
  have p0048 :=
    @gMpbir (.classMem (synC0c) (synCwppreachincb F C))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (synC0c))))
          (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (synC0c))))))
      p0042 p0047
  have p0049 :=
    @gSimpl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv d) (synCdm F))
  have p0050 :=
    @gSimpl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C))
  have p0051 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv m) (synCnnc)) p0049 p0050
  have p0052 := @gNntcsuc (.cv m)
  have p0053 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c)))
      p0051 p0052
  have p0054 :=
    @gFveq2d
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0053
  have p0058 := @gNntccl (.cv m)
  have p0059 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCtc (.cv m)) (synCnnc)) p0051 p0058
  have p0062 :=
    @gWppreachsucndv C F (synCtc (.cv m)) dv_cache_0002 dv_cache_0006 dv_cache_0007
      p0001
  have p0063 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCtc (.cv m)) (synCnnc))
      (.classEq (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCplc (synCtc (.cv m)) (synC1c))) (synCima (synCcnv F)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))))
      p0059 p0062
  have p0064 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (synCplc (.cv m) (synC1c))))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCplc (synCtc (.cv m)) (synC1c)))
      (synCima (synCcnv F)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      p0054 p0063
  have p0065 :=
    @gEleq2d
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (synCplc (.cv m) (synC1c))))
      (synCima (synCcnv F)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      (.cv d) p0064
  have p0066 := @gElfunsi F
  have p0067 := Nominal.mp hyp_wppreachincballfin_1 p0066
  have p0068 := @gFunfn F
  have p0069 := @gBiimpi (synWfun F) (synWfn F (synCdm F)) p0068
  have p0070 := Nominal.mp p0067 p0069
  have p0071 :=
    @gElpreima (synCdm F) (.cv d)
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (.cv m)))
      F
  have p0072 := Nominal.mp p0070 p0071
  have p0073 :=
    @gA1i
      (synWb (.classMem (.cv d) (synCima (synCcnv F) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))) (synWa (.classMem (.cv d) (synCdm F))
          (.classMem (synCfv F (.cv d)) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      p0072
  have p0074 :=
    @gSimpr
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv d) (synCdm F))
  have p0075 :=
    @gBiantrurd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d) (synCdm F))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      p0074
  have p0076 :=
    @gBicomd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      (synWa (.classMem (.cv d) (synCdm F)) (.classMem (synCfv F (.cv d))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))))
      p0075
  have p0077 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d) (synCima (synCcnv F)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))))
      (synWa (.classMem (.cv d) (synCdm F)) (.classMem (synCfv F (.cv d))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      p0073 p0076
  have p0078 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (synCplc (.cv m) (synC1c)))))
      (.classMem (.cv d) (synCima (synCcnv F)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      p0065 p0077
  have p0081 :=
    @gA1i (synWfun F)
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      p0067
  have p0083 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synWfun F) (.classMem (.cv d) (synCdm F)) p0081 p0074
  have p0084 := @gFvelrn (.cv d) F
  have p0085 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synWa (synWfun F) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCfv F (.cv d)) (synCrn F)) p0083 p0084
  have p0086 :=
    @gSseli (synCrn F) (synCdm F) (synCfv F (.cv d)) hyp_wppreachincballfin_2
  have p0087 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCfv F (.cv d)) (synCrn F))
      (.classMem (synCfv F (.cv d)) (synCdm F)) p0085 p0086
  have p0089 :=
    @gSimpr (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C))
  have p0093 :=
    @gWppreachincblayerscl (.cv m) C F e dv_cache_0008 dv_cache_0002 dv_cache_0009
      dv_cache_0010 p0001
  have p0094 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv m) (synCnnc))
      (synWb (.classMem (.cv m) (synCwppreachincb F C)) (synWral e (synCdm F) (synWb
            (.classMem (.cv e) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc (.cv m))))
            (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))))
      p0050 p0093
  have p0095 :=
    @gBiimpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv m) (synCwppreachincb F C))
      (synWral e (synCdm F) (synWb (.classMem (.cv e) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))
          (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))))
      p0094
  have p0096 :=
    @gMpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv m) (synCwppreachincb F C))
      (synWral e (synCdm F) (synWb (.classMem (.cv e) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))
          (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))))
      p0089 p0095
  have p0097 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (synWral e (synCdm F) (synWb (.classMem (.cv e) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))
          (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))))
      p0049 p0096
  have p0098 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCfv F (.cv d)) (synCdm F))
      (synWral e (synCdm F) (synWb (.classMem (.cv e) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv m))))
          (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))))
      p0087 p0097
  have p0099 := @gId (.classEq (.cv e) (synCfv F (.cv d)))
  have p0100 :=
    @gEleq1d (.classEq (.cv e) (synCfv F (.cv d))) (.cv e) (synCfv F (.cv d))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (.cv m)))
      p0099
  have p0102 :=
    @gEleq1d (.classEq (.cv e) (synCfv F (.cv d))) (.cv e) (synCfv F (.cv d))
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))) p0099
  have p0103 :=
    @gBibi12d (.classEq (.cv e) (synCfv F (.cv d)))
      (.classMem (.cv e)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      p0100 p0102
  have p0104 :=
    @gRspcva
      (synWb (.classMem (.cv e)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m))))
        (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      (synWb (.classMem (synCfv F (.cv d))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))) (.classMem (synCfv F (.cv d))
          (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      e (synCfv F (.cv d)) (synCdm F) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0103
  have p0105 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synWa (.classMem (synCfv F (.cv d)) (synCdm F)) (synWral e (synCdm F) (synWb
            (.classMem (.cv e) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc (.cv m))))
            (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))))
      (synWb (.classMem (synCfv F (.cv d))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv m)))) (.classMem (synCfv F (.cv d))
          (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      p0098 p0104
  have p0106 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (synCplc (.cv m) (synC1c)))))
      (.classMem (synCfv F (.cv d))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv m))))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      p0078 p0105
  have p0112 :=
    @gElpreima (synCdm F) (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))
      F
  have p0113 := Nominal.mp p0070 p0112
  have p0114 :=
    @gA1i
      (synWb (.classMem (.cv d)
          (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
        (synWa (.classMem (.cv d) (synCdm F)) (.classMem (synCfv F (.cv d))
            (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      p0113
  have p0116 :=
    @gBiantrurd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d) (synCdm F))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      p0074
  have p0117 :=
    @gBicomd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      (synWa (.classMem (.cv d) (synCdm F)) (.classMem (synCfv F (.cv d))
          (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      p0116
  have p0118 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      (synWa (.classMem (.cv d) (synCdm F)) (.classMem (synCfv F (.cv d))
          (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      p0114 p0117
  have p0119 :=
    @gBicomd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      p0118
  have p0120 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (synCplc (.cv m) (synC1c)))))
      (.classMem (synCfv F (.cv d)) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      (.classMem (.cv d)
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      p0106 p0119
  have p0126 := @gWpppowlayerseqsuc C m F dv_cache_0002 p0001
  have p0127 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c))))
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      p0051 p0126
  have p0128 :=
    @gEleq2d
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c))))
      (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m))))
      (.cv d) p0127
  have p0129 :=
    @gBicomd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c)))))
      (.classMem (.cv d)
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      p0128
  have p0130 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (.classMem (.cv m) (synCwppreachincb F C))) (.classMem (.cv d) (synCdm F)))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (synCplc (.cv m) (synC1c)))))
      (.classMem (.cv d)
        (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv m)))))
      (.classMem (.cv d)
        (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c)))))
      p0120 p0129
  have p0131 :=
    @gRalrimiva
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (synCplc (.cv m) (synC1c))))) (.classMem (.cv d)
          (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c))))))
      d (synCdm F) dv_cache_0014 p0130
  have p0133 := @gPeano2 (.cv m)
  have p0134 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      p0050 p0133
  have p0137 :=
    @gWppreachincblayerscl (synCplc (.cv m) (synC1c)) C F d dv_cache_0015 dv_cache_0002
      dv_cache_0004 dv_cache_0005 p0001
  have p0138 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (synWb (.classMem (synCplc (.cv m) (synC1c)) (synCwppreachincb F C))
        (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc (synCplc (.cv m) (synC1c))))) (.classMem (.cv d)
              (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c))))))))
      p0134 p0137
  have p0139 :=
    @gMpbird
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwppreachincb F C))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (synCplc (.cv m) (synC1c))))) (.classMem (.cv d)
            (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv m) (synC1c)))))))
      p0131 p0138
  have p0140 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwppreachincb F C))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwppreachincb F C)) p0139
  have p0141_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classMem (.cv n) (synCwppreachincb F C))
          (.classMem (.cv m) (synCwppreachincb F C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwppreachincb synCuni1 synCuni synWex synWa synCin
          synCcompl synCnin synWnan synC1c
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0141 :=
    @gFinds (.classMem (.cv n) (synCwppreachincb F C))
      (.classMem (synC0c) (synCwppreachincb F C))
      (.classMem (.cv m) (synCwppreachincb F C))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwppreachincb F C))
      (.classMem N (synCwppreachincb F C)) n m N dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0005 p0007
      p0141_e02_recanon p0011 p0013 p0048 p0140
  exact p0141

/-- Checked nominal proof certificate identified upstream as `g_wppreachpowlayers`. -/
@[expose]
noncomputable def gWppreachpowlayers (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_N_d : d ∉ N.fv) (hyp_wppreachpowlayers_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachpowlayers_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc N)))
            (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn N)))))) :=
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
    @gWppreachincballfin C F N dv_cache_0001 hyp_wppreachpowlayers_1
      hyp_wppreachpowlayers_2
  have p0001 := @gElex F (synCfuns)
  have p0002 := Nominal.mp hyp_wppreachpowlayers_1 p0001
  have p0003 :=
    @gWppreachincblayerscl N C F d dv_cache_0002 dv_cache_0001 dv_cache_0003
      dv_cache_0004 p0002
  have p0004 :=
    @gMpbid (.classMem N (synCnnc)) (.classMem N (synCwppreachincb F C))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N)))
          (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn N)))))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerorbcl`. -/
@[expose]
noncomputable def gWpppowlayerorbcl (B : Class) (C : Class) (D : Class) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerorbcl_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowlayerorbcl_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowlayerorbcl_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc))
        (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
          (synWbr C (synClec) (synCfv (synCfrec F D) B)))) :=
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
      ((Wff.imp (.classMem B (synCnnc))
          (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
            (synWbr C (synClec) (synCfv (synCfrec F D) B))))).fv :=
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
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gSneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0005 :=
    @gFveq2d (.classEq (.cv n) B) (synCsn (.cv n)) (synCsn B) (synCwpppowlayerseq F C)
      p0004
  have p0006 :=
    @gEleq2d (.classEq (.cv n) B) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCfv (synCwpppowlayerseq F C) (synCsn B)) D p0005
  have p0008 := @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec F D) p0001
  have p0009 :=
    @gBreq2d (.classEq (.cv n) B) (synCfv (synCfrec F D) (.cv n))
      (synCfv (synCfrec F D) B) C (synClec) p0008
  have p0010 :=
    @gBibi12d (.classEq (.cv n) B)
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
      (synWbr C (synClec) (synCfv (synCfrec F D) B)) p0006 p0009
  have p0011 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
        (synWbr C (synClec) (synCfv (synCfrec F D) B)))
      p0002 p0010
  have p0012 :=
    @gWpppowlayerorb C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wpppowlayerorbcl_1 hyp_wpppowlayerorbcl_2 hyp_wpppowlayerorbcl_3
  have p0013 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc))
        (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
          (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))))
      (.imp (.classMem B (synCnnc))
        (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
          (synWbr C (synClec) (synCfv (synCfrec F D) B))))
      n B (synCnnc) dv_cache_0004 dv_cache_0005 p0011 p0012
  have p0014 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn B)))
        (synWbr C (synClec) (synCfv (synCfrec F D) B)))
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

/-- Checked nominal proof certificate identified upstream as `g_wppreachlayerorbfin`. -/
@[expose]
noncomputable def gWppreachlayerorbfin (C : Class) (D : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachlayerorbfin_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachlayerorbfin_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachlayerorbfin_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (synWb (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N))) (synWbr C (synClec) (synCfv (synCfrec F D) N)))) :=
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
  have dv_cache_0006 : e ∉ ((synCdm F)).fv :=
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
      ((synWb (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N)))
          (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn N))))).fv :=
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
    @gA1i (.classMem D (synCdm F)) (.classMem N (synCnnc)) hyp_wppreachlayerorbfin_2
  have p0001 :=
    @gWppreachpowlayers C F N e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_wppreachlayerorbfin_1 hyp_wppreachlayerorbfin_3
  have p0002 :=
    @gJca (.classMem N (synCnnc)) (.classMem D (synCdm F))
      (synWral e (synCdm F) (synWb (.classMem (.cv e) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N)))
          (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn N)))))
      p0000 p0001
  have p0003 := @gId (.classEq (.cv e) D)
  have p0004 :=
    @gEleq1d (.classEq (.cv e) D) (.cv e) D
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc N))
      p0003
  have p0006 :=
    @gEleq1d (.classEq (.cv e) D) (.cv e) D
      (synCfv (synCwpppowlayerseq F C) (synCsn N)) p0003
  have p0007 :=
    @gBibi12d (.classEq (.cv e) D)
      (.classMem (.cv e)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc N)))
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc N)))
      (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn N)))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn N))) p0004 p0006
  have p0008 :=
    @gRspcva
      (synWb (.classMem (.cv e)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc N))) (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn N))))
      (synWb (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc N))) (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn N))))
      e D (synCdm F) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @gSyl (.classMem N (synCnnc))
      (synWa (.classMem D (synCdm F)) (synWral e (synCdm F) (synWb (.classMem (.cv e)
              (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc N)))
            (.classMem (.cv e) (synCfv (synCwpppowlayerseq F C) (synCsn N))))))
      (synWb (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc N))) (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn N))))
      p0002 p0008
  have p0010 :=
    @gWpppowlayerorbcl N C D F dv_cache_0001 hyp_wppreachlayerorbfin_1
      hyp_wppreachlayerorbfin_2 hyp_wppreachlayerorbfin_3
  have p0011 :=
    @gBitrd (.classMem N (synCnnc))
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc N)))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn N)))
      (synWbr C (synClec) (synCfv (synCfrec F D) N)) p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_strictsegdifinindv`. -/
@[expose]
noncomputable def gStrictsegdifinindv (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))) :=
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
    y ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
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
      ((synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))).fv :=
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
  have p0000 := @gElstrictseg x y D R
  have p0001 :=
    @gEldifsn (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (.cv x)
  have p0002 := @gElin (.cv y) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0003 := @gEliniseg R (.cv x) (.cv y)
  have p0004 :=
    @gAnbi2i (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x))))
      (synWbr (.cv y) R (.cv x)) (.classMem (.cv y) D) p0003
  have p0005 :=
    @gBitri (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x))) p0002 p0004
  have p0006 :=
    @gAnbi1i (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x))) (synWne (.cv y) (.cv x))
      p0005
  have p0007 :=
    @gBitri
      (.classMem (.cv y) (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
          (synCsn (.cv x))))
      (synWa (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
        (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)))
        (synWne (.cv y) (.cv x)))
      p0001 p0006
  have p0008 :=
    @gAnass (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))
  have p0009 :=
    @gBitri
      (.classMem (.cv y) (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
          (synCsn (.cv x))))
      (synWa (synWa (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)))
        (synWne (.cv y) (.cv x)))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0007 p0008
  have p0010 :=
    @gBitr4i
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y) (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
          (synCsn (.cv x))))
      p0000 p0009
  have p0011 :=
    @gEqriv y (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisoendpointseqndv`. -/
@[expose]
noncomputable def gWecutisoendpointseqndv (x : Var) (y : Var) (D : Class) (R : Class)
    (H : Class) (hyp_wecutisoendpointseqndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (.cv x) (.cv y))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWne (.cv x) (.cv y))
  have p0001 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0000 p0001
  have p0003 := @gWppweconnex D R
  have p0004 := Nominal.mp hyp_wecutisoendpointseqndv_1 p0003
  have p0005 :=
    @gA1i (synWbr R (synCconnex) D)
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0008 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv))
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) p0007 p0008
  have p0010 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0009
      p0010
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D) p0000 p0011
  have p0017 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0009
      p0017
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) D) p0000 p0018
  have p0020 :=
    @gConnexd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0012 p0019
  have p0021 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      hyp_wecutisoendpointseqndv_1
  have p0022 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0022 p0019
  have p0031 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr R (synCwe) D) (.classMem (.cv y) D) p0021 p0030
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0022 p0012
  have p0041 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0043 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWne (.cv x) (.cv y))
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWne (.cv x) (.cv y)) p0022 p0043
  have p0045 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)) p0041 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)))
      p0040 p0045
  have p0047 := @gElstrictseg y x D R
  have p0048 :=
    @gBiimpri
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      p0047
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0046 p0048
  have p0050 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0031 p0049
  have p0054 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv))
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (.classMem H (synCvv)) p0007 p0054
  have p0056 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem H (synCvv)) p0000 p0055
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem H (synCvv)) p0022 p0056
  have p0058 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem H (synCvv)) p0050 p0057
  have p0059 := @gStrictsegltnoiso x y D R H
  have p0060 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0058 p0059
  have p0061 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0060
  have p0062 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      hyp_wecutisoendpointseqndv_1
  have p0063 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0063 p0012
  have p0072 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWbr R (synCwe) D) (.classMem (.cv x) D) p0062 p0071
  have p0081 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0063 p0019
  have p0082 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0085 :=
    @gNecomd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0043
  have p0086 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWne (.cv y) (.cv x)) p0063 p0085
  have p0087 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0082 p0086
  have p0088 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0081 p0087
  have p0089 := @gElstrictseg x y D R
  have p0090 :=
    @gBiimpri
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0089
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0088 p0090
  have p0092 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0072 p0091
  have p0099 := @gCnvexg H (synCvv)
  have p0100 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem H (synCvv)) (.classMem (synCcnv H) (synCvv)) p0056 p0099
  have p0101 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (.classMem (synCcnv H) (synCvv)) p0063 p0100
  have p0102 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (synCcnv H) (synCvv)) p0092 p0101
  have p0103 := @gStrictsegltnoiso y x D R (synCcnv H)
  have p0104 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (synCcnv H) (synCvv)))
      (.neg (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0102 p0103
  have p0105 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      H
  have p0106 :=
    @gA1i
      (.imp (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      p0105
  have p0107 :=
    @gCon3d
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0106
  have p0108 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (.neg (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0104 p0107
  have p0109 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0108
  have p0110 :=
    @gJaod
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (.cv y) R (.cv x)) p0061 p0109
  have p0111 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0020 p0110
  have p0112 :=
    @gPm221dd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWne (.cv x) (.cv y)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.neg (synWne (.cv x) (.cv y))) p0002 p0111
  have p0113 :=
    @gPm201da
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWne (.cv x) (.cv y)) p0112
  have p0114 := @gNne (.cv x) (.cv y)
  have p0115 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0113 p0114
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisoendpointseqclndv`. -/
@[expose]
noncomputable def gWecutisoendpointseqclndv (B : Class) (C : Class) (D : Class)
    (R : Class) (H : Class)
    (hyp_wecutisoendpointseqclndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
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
      ((Wff.imp (synWa
            (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
            (synWiso H (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
              (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
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
      ((Wff.imp (synWa (synWa (synWa (.classMem B D) (.classMem (.cv y) D))
              (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
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
    @gSimpl (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))
  have p0001 := @gSimpl (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
      (synWa (.classMem B D) (.classMem C D)) p0000 p0001
  have p0003 := @gSimpl (.classMem B D) (.classMem C D)
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (synWa (.classMem B D) (.classMem C D)) (.classMem B D) p0002 p0003
  have p0005 := @gElex B D
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (.classMem B D) (.classMem B (synCvv)) p0004 p0005
  have p0010 := @gSimpr (.classMem B D) (.classMem C D)
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (synWa (.classMem B D) (.classMem C D)) (.classMem C D) p0002 p0010
  have p0012 := @gElex C D
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (.classMem C D) (.classMem C (synCvv)) p0011 p0012
  have p0014 :=
    @gJca
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (.classMem B (synCvv)) (.classMem C (synCvv)) p0006 p0013
  have p0015 := @gEleq1 (.cv x) B D
  have p0016 := @gBiid (.classMem (.cv y) D)
  have p0017 :=
    @gA1i (synWb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0016
  have p0018 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0015 p0017
  have p0019 := @gBiid (.classMem H (synCvv))
  have p0020 :=
    @gA1i (synWb (.classMem H (synCvv)) (.classMem H (synCvv))) (.classEq (.cv x) B)
      p0019
  have p0021 :=
    @gAnbi12d (.classEq (.cv x) B) (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv))
      (.classMem H (synCvv)) p0018 p0020
  have p0022 := @gSneq (.cv x) B
  have p0023 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B)
      (synCcnv (synCdif R (synCid))) p0022
  have p0024 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) D p0023
  have p0028 :=
    @gXpeq12d (.classEq (.cv x) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) p0024 p0024
  have p0029 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      R p0028
  have p0030 :=
    @gIsoeq2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      H
  have p0031 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))))
      (synWb (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0029 p0030
  have p0035 :=
    @gIsoeq4 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      H
  have p0036 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synWb (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0024 p0035
  have p0037 :=
    @gBitrd (.classEq (.cv x) B)
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0031 p0036
  have p0038 :=
    @gAnbi12d (.classEq (.cv x) B)
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWa (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0021 p0037
  have p0039 := @gId (.classEq (.cv x) B)
  have p0040 := @gEqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0039
  have p0041 :=
    @gImbi12d (.classEq (.cv x) B)
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0038 p0040
  have p0042 := @gBiid (.classMem B D)
  have p0043 := @gA1i (synWb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0042
  have p0044 := @gEleq1 (.cv y) C D
  have p0045 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0043 p0044
  have p0047 :=
    @gA1i (synWb (.classMem H (synCvv)) (.classMem H (synCvv))) (.classEq (.cv y) C)
      p0019
  have p0048 :=
    @gAnbi12d (.classEq (.cv y) C) (synWa (.classMem B D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv))
      (.classMem H (synCvv)) p0045 p0047
  have p0049 := @gSneq (.cv y) C
  have p0050 :=
    @gImaeq2d (.classEq (.cv y) C) (synCsn (.cv y)) (synCsn C)
      (synCcnv (synCdif R (synCid))) p0049
  have p0051 :=
    @gIneq2d (.classEq (.cv y) C)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn C)) D p0050
  have p0055 :=
    @gXpeq12d (.classEq (.cv y) C)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))) p0051 p0051
  have p0056 :=
    @gIneq2d (.classEq (.cv y) C)
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))
      R p0055
  have p0057 :=
    @gIsoeq3 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      H
  have p0058 :=
    @gSyl (.classEq (.cv y) C)
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))))
      (synWb (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0056 p0057
  have p0062 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      H
  have p0063 :=
    @gSyl (.classEq (.cv y) C)
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))
      (synWb (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      p0051 p0062
  have p0064 :=
    @gBitrd (.classEq (.cv y) C)
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))
      p0058 p0063
  have p0065 :=
    @gAnbi12d (.classEq (.cv y) C)
      (synWa (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
      (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso H (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))
      p0048 p0064
  have p0066 := @gId (.classEq (.cv y) C)
  have p0067 := @gEqeq2d (.classEq (.cv y) C) (.cv y) C B p0066
  have p0068 :=
    @gImbi12d (.classEq (.cv y) C)
      (synWa (synWa (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (.classEq B (.cv y)) (.classEq B C) p0065 p0067
  have p0069 := @gWecutisoendpointseqndv x y D R H hyp_wecutisoendpointseqclndv_1
  have p0070 :=
    @gVtocl2g
      (.imp (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (.cv x) (.cv y)))
      (.imp (synWa
          (synWa (synWa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (synCvv)))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq B (.cv y)))
      (.imp (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (.classEq B C))
      x y B C (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0041 p0068 p0069
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
        (.classEq B C))
      p0014 p0070
  have p0072 :=
    @gPm243i
      (synWa (synWa (synWa (.classMem B D) (.classMem C D)) (.classMem H (synCvv)))
        (synWiso H (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
      (.classEq B C) p0071
  exact p0072

/-- Checked nominal proof certificate identified upstream as `g_strictsegdifiniclndv`. -/
@[expose]
noncomputable def gStrictsegdifiniclndv (B : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCvv))
        (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCdif (synCin D (synCima (synCcnv R) (synCsn B))) (synCsn B)))) :=
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
      ((Wff.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCdif (synCin D (synCima (synCcnv R) (synCsn B))) (synCsn B)))).fv :=
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
  have p0000 := @gSneq (.cv x) B
  have p0001 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B)
      (synCcnv (synCdif R (synCid))) p0000
  have p0002 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) D p0001
  have p0004 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B) (synCcnv R) p0000
  have p0005 :=
    @gIneq2d (.classEq (.cv x) B) (synCima (synCcnv R) (synCsn (.cv x)))
      (synCima (synCcnv R) (synCsn B)) D p0004
  have p0007 :=
    @gDifeq12d (.classEq (.cv x) B) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv R) (synCsn B))) (synCsn (.cv x)) (synCsn B) p0005
      p0000
  have p0008 :=
    @gEqeq12d (.classEq (.cv x) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
      (synCdif (synCin D (synCima (synCcnv R) (synCsn B))) (synCsn B)) p0002 p0007
  have p0009 := @gStrictsegdifinindv x D R
  have p0010 :=
    @gVtoclg
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x))))
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCdif (synCin D (synCima (synCcnv R) (synCsn B))) (synCsn B)))
      x B (synCvv) dv_cache_0001 dv_cache_0002 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_isostrictsegimandv`. -/
@[expose]
noncomputable def gIsostrictsegimandv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (.classEq (synCima H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin E (synCima (synCcnv (synCdif S (synCid)))
              (synCsn (synCfv H (.cv x))))))) :=
  by
  have p0000 := @gStrictsegdifinindv x D R
  have p0001 :=
    @gA1i
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x))))
      (synWa (synWiso H R S D E) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @gImaeq2d (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x))) H
      p0001
  have p0003 := @gSimpl (synWiso H R S D E) (.classMem (.cv x) D)
  have p0004 := @gIsof1o D E R S H
  have p0005 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWiso H R S D E)
      (synWf1o H D E) p0003 p0004
  have p0006 := @gF1ocnv D E H
  have p0007 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1o H D E)
      (synWf1o (synCcnv H) E D) p0005 p0006
  have p0008 := @gF1ofun E D (synCcnv H)
  have p0009 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1o (synCcnv H) E D)
      (synWfun (synCcnv H)) p0007 p0008
  have p0010 :=
    @gImadif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)) H
  have p0011 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWfun (synCcnv H))
      (.classEq (synCima H (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
            (synCsn (.cv x))))
        (synCdif (synCima H (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
          (synCima H (synCsn (.cv x)))))
      p0009 p0010
  have p0012 :=
    @gEqtrd (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCima H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCima H (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
          (synCsn (.cv x))))
      (synCdif (synCima H (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
        (synCima H (synCsn (.cv x))))
      p0002 p0011
  have p0013 := @gIsoini D E (.cv x) R S H
  have p0017 := @gF1ofn D E H
  have p0018 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1o H D E)
      (synWfn H D) p0005 p0017
  have p0019 := @gSimpr (synWiso H R S D E) (.classMem (.cv x) D)
  have p0020 :=
    @gJca (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWfn H D)
      (.classMem (.cv x) D) p0018 p0019
  have p0021 := @gFnsnfv D (.cv x) H
  have p0022 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (synWfn H D) (.classMem (.cv x) D))
      (.classEq (synCsn (synCfv H (.cv x))) (synCima H (synCsn (.cv x)))) p0020 p0021
  have p0023 :=
    @gEqcomd (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCsn (synCfv H (.cv x))) (synCima H (synCsn (.cv x))) p0022
  have p0024 :=
    @gDifeq12d (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCima H (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (synCin E (synCima (synCcnv S) (synCsn (synCfv H (.cv x)))))
      (synCima H (synCsn (.cv x))) (synCsn (synCfv H (.cv x))) p0013 p0023
  have p0025 :=
    @gEqtrd (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCima H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCdif (synCima H (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
        (synCima H (synCsn (.cv x))))
      (synCdif (synCin E (synCima (synCcnv S) (synCsn (synCfv H (.cv x)))))
        (synCsn (synCfv H (.cv x))))
      p0012 p0024
  have p0029 := @gF1of D E H
  have p0030 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1o H D E)
      (synWf H D E) p0005 p0029
  have p0032 :=
    @gJca (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf H D E)
      (.classMem (.cv x) D) p0030 p0019
  have p0033 := @gFfvelrn D E (.cv x) H
  have p0034 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (synWf H D E) (.classMem (.cv x) D)) (.classMem (synCfv H (.cv x)) E)
      p0032 p0033
  have p0035 := @gElex (synCfv H (.cv x)) E
  have p0036 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (.classMem (synCfv H (.cv x)) E) (.classMem (synCfv H (.cv x)) (synCvv)) p0034
      p0035
  have p0037 := @gStrictsegdifiniclndv (synCfv H (.cv x)) E S
  have p0038 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (.classMem (synCfv H (.cv x)) (synCvv))
      (.classEq (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
        (synCdif (synCin E (synCima (synCcnv S) (synCsn (synCfv H (.cv x)))))
          (synCsn (synCfv H (.cv x)))))
      p0036 p0037
  have p0039 :=
    @gEqcomd (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCdif (synCin E (synCima (synCcnv S) (synCsn (synCfv H (.cv x)))))
        (synCsn (synCfv H (.cv x))))
      p0038
  have p0040 :=
    @gEqtrd (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synCima H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCdif (synCin E (synCima (synCcnv S) (synCsn (synCfv H (.cv x)))))
        (synCsn (synCfv H (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
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

/-- Checked nominal proof certificate identified upstream as `g_isostrictsegresndv`. -/
@[expose]
noncomputable def gIsostrictsegresndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))) :=
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
    v ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
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
  have dv_cache_0002 : u ∉ ((synWa (synWiso H R S D E) (.classMem (.cv x) D))).fv :=
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
  have dv_cache_0003 : v ∉ ((synWa (synWiso H R S D E) (.classMem (.cv x) D))).fv :=
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
    u ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
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
      ((synCin E (synCima (synCcnv (synCdif S (synCid)))
            (synCsn (synCfv H (.cv x)))))).fv :=
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
      ((synCin E (synCima (synCcnv (synCdif S (synCid)))
            (synCsn (synCfv H (.cv x)))))).fv :=
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
      ((synCres H (synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))).fv :=
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
      ((synCres H (synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))).fv :=
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
  have p0000 := @gSimpl (synWiso H R S D E) (.classMem (.cv x) D)
  have p0001 := @gIsof1o D E R S H
  have p0002 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWiso H R S D E)
      (synWf1o H D E) p0000 p0001
  have p0003 := @gF1of1 D E H
  have p0004 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1o H D E)
      (synWf1 H D E) p0002 p0003
  have p0005 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0006 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      (synWa (synWiso H R S D E) (.classMem (.cv x) D)) p0005
  have p0007 :=
    @gJca (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWf1 H D E)
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      p0004 p0006
  have p0008 :=
    @gF1ores D E
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) H
  have p0009 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (synWf1 H D E) (synWss
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D))
      (synWf1o (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCima H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0007 p0008
  have p0010 := @gIsostrictsegimandv x D R S E H
  have p0011 :=
    @gF1oeq3
      (synCima H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0012 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (.classEq (synCima H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWb (synWf1o (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCima H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synWf1o (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0010 p0011
  have p0013 :=
    @gMpbid (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWf1o (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCima H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWf1o (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0009 p0012
  have p0014 :=
    @gSimpl (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (.classMem (.cv u)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv v)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWiso H R S D E) p0014 p0000
  have p0017 :=
    @gSimpr (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (.classMem (.cv u)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv v)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0018 :=
    @gSimpl
      (.classMem (.cv u)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv v)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0019 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWa (.classMem (.cv u)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv v)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv u)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0017 p0018
  have p0021 :=
    @gSseli (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D
      (.cv u) p0005
  have p0022 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv u)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv u) D) p0019 p0021
  have p0024 :=
    @gSimpr
      (.classMem (.cv u)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv v)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0025 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWa (.classMem (.cv u)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv v)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv v)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0017 p0024
  have p0027 :=
    @gSseli (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D
      (.cv v) p0005
  have p0028 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv v)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv v) D) p0025 p0027
  have p0029 :=
    @gJca
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv u) D) (.classMem (.cv v) D) p0022 p0028
  have p0030 :=
    @gJca
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWiso H R S D E) (synWa (.classMem (.cv u) D) (.classMem (.cv v) D)) p0016
      p0029
  have p0031 := @gIsorel D E (.cv u) (.cv v) R S H
  have p0032 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWa (synWiso H R S D E) (synWa (.classMem (.cv u) D) (.classMem (.cv v) D)))
      (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv H (.cv u)) S (synCfv H (.cv v))))
      p0030 p0031
  have p0036 :=
    @gFvres (.cv u)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) H
  have p0037 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv u)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCfv (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv u))
        (synCfv H (.cv u)))
      p0019 p0036
  have p0041 :=
    @gFvres (.cv v)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) H
  have p0042 :=
    @gSyl
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv v)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCfv (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv v))
        (synCfv H (.cv v)))
      p0025 p0041
  have p0043 :=
    @gBreq12d
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCfv (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv u))
      (synCfv H (.cv u))
      (synCfv (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv v))
      (synCfv H (.cv v)) S p0037 p0042
  have p0044 :=
    @gBibi2d
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWbr (synCfv (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv u))
        S (synCfv (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.cv v)))
      (synWbr (synCfv H (.cv u)) S (synCfv H (.cv v))) (synWbr (.cv u) R (.cv v))
      p0043
  have p0045 :=
    @gMpbird
      (synWa (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWa (.classMem (.cv u)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv v)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv (synCres H
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.cv u)) S (synCfv (synCres H
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.cv v))))
      (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv H (.cv u)) S (synCfv H (.cv v))))
      p0032 p0044
  have p0046 :=
    @gRalrimivva (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv (synCres H
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.cv u)) S (synCfv (synCres H
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.cv v))))
      u v (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0045
  have p0047 :=
    @gJca (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWf1o (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWral u (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synWral v (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv (synCres H (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv u)) S
              (synCfv (synCres H (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
                (.cv v))))))
      p0013 p0046
  have p0048 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso u v
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      R S
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0004
  have p0049 :=
    @gSylibr (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (synWf1o (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWral u (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synWral v (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synWb (synWbr (.cv u) R (.cv v)) (synWbr (synCfv (synCres H (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.cv u))
                S (synCfv (synCres H (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
                  (.cv v)))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0047 p0048
  have p0050 :=
    @gIsores1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      R S
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0051 :=
    @gSylib (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0049 p0050
  have p0052 :=
    @gIsores2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      S
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0053 :=
    @gSylib (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
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

/-- Checked nominal proof certificate identified upstream as `g_weisouniquecl`. -/
@[expose]
noncomputable def gWeisouniquecl (D : Class) (R : Class) (S : Class) (E : Class)
    (F : Class) (G : Class) (hyp_weisouniquecl_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_weisouniquecl_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classEq F G)) :=
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
      ((synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E)))).fv :=
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
    @gSimpr (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (synWa (synWiso F R S D E) (synWiso G R S D E))
  have p0001 := @gSimpl (synWiso F R S D E) (synWiso G R S D E)
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWa (synWiso F R S D E) (synWiso G R S D E)) (synWiso F R S D E) p0000 p0001
  have p0003 := @gIsof1o D E R S F
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWiso F R S D E) (synWf1o F D E) p0002 p0003
  have p0005 := @gF1ofn D E F
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf1o F D E) (synWfn F D) p0004 p0005
  have p0008 := @gSimpr (synWiso F R S D E) (synWiso G R S D E)
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWa (synWiso F R S D E) (synWiso G R S D E)) (synWiso G R S D E) p0000 p0008
  have p0010 := @gIsof1o D E R S G
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWiso G R S D E) (synWf1o G D E) p0009 p0010
  have p0012 := @gF1ofn D E G
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf1o G D E) (synWfn G D) p0011 p0012
  have p0014 :=
    @gSimpl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (.classMem (.cv x) D)
  have p0020 := @gF1of D E F
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf1o F D E) (synWf F D E) p0004 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf F D E) p0014 p0021
  have p0023 :=
    @gSimpr
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (.classMem (.cv x) D)
  have p0024 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWf F D E) (.classMem (.cv x) D) p0022 p0023
  have p0025 := @gFfvelrn D E (.cv x) F
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWf F D E) (.classMem (.cv x) D)) (.classMem (synCfv F (.cv x)) E)
      p0024 p0025
  have p0033 := @gF1of D E G
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf1o G D E) (synWf G D E) p0011 p0033
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWf G D E) p0014 p0034
  have p0037 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWf G D E) (.classMem (.cv x) D) p0035 p0023
  have p0038 := @gFfvelrn D E (.cv x) G
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWf G D E) (.classMem (.cv x) D)) (.classMem (synCfv G (.cv x)) E)
      p0037 p0038
  have p0040 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (synCfv F (.cv x)) E) (.classMem (synCfv G (.cv x)) E) p0026 p0039
  have p0042 :=
    @gSimpl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (synWa (synWiso F R S D E) (synWiso G R S D E))
  have p0043 := @gSimpr (.classMem F (synCvv)) (.classMem G (synCvv))
  have p0044 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWa (.classMem F (synCvv)) (.classMem G (synCvv))) (.classMem G (synCvv))
      p0042 p0043
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (.classMem G (synCvv)) p0014 p0044
  have p0046 := @gBrex R D (synCwe)
  have p0047 := Nominal.mp hyp_weisouniquecl_1 p0046
  have p0048 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0049 := Nominal.mp p0047 p0048
  have p0052 := @gSimpl (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0053 := Nominal.mp p0047 p0052
  have p0054 := @gIdex
  have p0055 := @gDifex R (synCid) p0053 p0054
  have p0056 := @gCnvex (synCdif R (synCid)) p0055
  have p0057 := @gSnex (.cv x)
  have p0058 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0056 p0057
  have p0059 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0049 p0058
  have p0060 :=
    @gA1i
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      p0059
  have p0061 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (.classMem G (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0045 p0060
  have p0062 :=
    @gResexg G (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCvv) (synCvv)
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (.classMem G (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)))
      (.classMem (synCres G
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      p0061 p0062
  have p0066 := @gSimpl (.classMem F (synCvv)) (.classMem G (synCvv))
  have p0067 :=
    @gSyl
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWa (.classMem F (synCvv)) (.classMem G (synCvv))) (.classMem F (synCvv))
      p0042 p0066
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (.classMem F (synCvv)) p0014 p0067
  have p0084 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (.classMem F (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0068 p0060
  have p0085 :=
    @gResexg F (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCvv) (synCvv)
  have p0086 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (.classMem F (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)))
      (.classMem (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      p0084 p0085
  have p0087 :=
    @gCnvexg
      (synCres F (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCvv)
  have p0088 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      (.classMem (synCcnv (synCres F
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      p0086 p0087
  have p0089 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (.classMem (synCres G
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      (.classMem (synCcnv (synCres F
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      p0063 p0088
  have p0090 :=
    @gCoexg
      (synCres G (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCcnv (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCvv) (synCvv)
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (.classMem (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCvv)) (.classMem (synCcnv (synCres F
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCvv)))
      (.classMem (synCcom (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCcnv (synCres F (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCvv))
      p0089 p0090
  have p0092 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (.classMem (synCfv F (.cv x)) E) (.classMem (synCfv G (.cv x)) E))
      (.classMem (synCcom (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCcnv (synCres F (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCvv))
      p0040 p0091
  have p0097 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWiso F R S D E) p0014 p0002
  have p0099 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWiso F R S D E) (.classMem (.cv x) D) p0097 p0023
  have p0100 := @gIsostrictsegresndv x D R S E F
  have p0101 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWiso F R S D E) (.classMem (.cv x) D))
      (synWiso (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x))))))
      p0099 p0100
  have p0102 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))))
      (synCres F (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0103 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWiso (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x))))))
      (synWiso (synCcnv (synCres F
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x))))))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0101 p0102
  have p0108 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      (synWiso G R S D E) p0014 p0009
  have p0110 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWiso G R S D E) (.classMem (.cv x) D) p0108 p0023
  have p0111 := @gIsostrictsegresndv x D R S E G
  have p0112 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWiso G R S D E) (.classMem (.cv x) D))
      (synWiso (synCres G
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv G (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x))))))
      p0110 p0111
  have p0113 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWiso (synCcnv (synCres F
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x))))))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (synCres G
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv G (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x))))))
      p0103 p0112
  have p0114 :=
    @gIsotr
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))))
      (synCres G (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCcnv (synCres F
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0115 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWiso (synCcnv (synCres F
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv F (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synWiso
          (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv G (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))))
      (synWiso (synCcom (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCcnv (synCres F (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x))))))) (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv G (.cv x))))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x))))))
      p0113 p0114
  have p0116 :=
    @gJca
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa (.classMem (synCfv F (.cv x)) E) (.classMem (synCfv G (.cv x)) E))
        (.classMem (synCcom (synCres G
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCcnv (synCres F (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCvv)))
      (synWiso (synCcom (synCres G
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCcnv (synCres F (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv F (.cv x))))))) (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv G (.cv x))))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x))))))
      p0092 p0115
  have p0117 :=
    @gWecutisoendpointseqclndv (synCfv F (.cv x)) (synCfv G (.cv x)) E S
      (synCcom (synCres G
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCcnv
          (synCres F
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      hyp_weisouniquecl_2
  have p0118 :=
    @gSyl
      (synWa (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
          (synWa (synWiso F R S D E) (synWiso G R S D E))) (.classMem (.cv x) D))
      (synWa (synWa
          (synWa (.classMem (synCfv F (.cv x)) E) (.classMem (synCfv G (.cv x)) E))
          (.classMem (synCcom (synCres G (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCcnv
                (synCres F (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
            (synCvv))) (synWiso (synCcom (synCres G
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCcnv (synCres F (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv F (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv G (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv F (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv G (.cv x)))))))
      (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))) p0116 p0117
  have p0119 :=
    @gEqfnfvd
      (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (synWa (synWiso F R S D E) (synWiso G R S D E)))
      x D F G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0013 p0118
  exact p0119

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniquecl`. -/
@[expose]
noncomputable def gWecutisouniquecl (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (E : Class) (F : Class) (G : Class)
    (hyp_wecutisouniquecl_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisouniquecl_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem F (synCvv)) (.classMem G (synCvv))) (synWa (synWiso F
              (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
              (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))) (synWiso G
              (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
              (synCin S (synCxp
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))))))
        (.classEq F G)) :=
  by
  have p0000 := @gId (synWbr R (synCwe) D)
  have p0001 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))
  have p0002 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) D)
      (synWbr R (synCwe) D) p0001
  have p0003 := @gBrex R D (synCwe)
  have p0004 := Nominal.mp hyp_wecutisouniquecl_1 p0003
  have p0005 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0006 := Nominal.mp p0004 p0005
  have p0009 := @gSimpl (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0010 := Nominal.mp p0004 p0009
  have p0011 := @gIdex
  have p0012 := @gDifex R (synCid) p0010 p0011
  have p0013 := @gCnvex (synCdif R (synCid)) p0012
  have p0014 := @gSnex B
  have p0015 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn B) p0013 p0014
  have p0016 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) p0006 p0015
  have p0017 :=
    @gA1i
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCvv))
      (synWbr R (synCwe) D) p0016
  have p0018 :=
    @gWerestrndv (synWbr R (synCwe) D)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) D R p0000 p0002
      p0017
  have p0019 := Nominal.mp hyp_wecutisouniquecl_1 p0018
  have p0020 := @gId (synWbr S (synCwe) E)
  have p0021 := @gInss1 E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))
  have p0022 :=
    @gA1i
      (synWss (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))) E)
      (synWbr S (synCwe) E) p0021
  have p0023 := @gBrex S E (synCwe)
  have p0024 := Nominal.mp hyp_wecutisouniquecl_2 p0023
  have p0025 := @gSimpr (.classMem S (synCvv)) (.classMem E (synCvv))
  have p0026 := Nominal.mp p0024 p0025
  have p0029 := @gSimpl (.classMem S (synCvv)) (.classMem E (synCvv))
  have p0030 := Nominal.mp p0024 p0029
  have p0032 := @gDifex S (synCid) p0030 p0011
  have p0033 := @gCnvex (synCdif S (synCid)) p0032
  have p0034 := @gSnex C
  have p0035 := @gImaex (synCcnv (synCdif S (synCid))) (synCsn C) p0033 p0034
  have p0036 :=
    @gInex E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)) p0026 p0035
  have p0037 :=
    @gA1i
      (.classMem (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))) (synCvv))
      (synWbr S (synCwe) E) p0036
  have p0038 :=
    @gWerestrndv (synWbr S (synCwe) E)
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))) E S p0020 p0022
      p0037
  have p0039 := Nominal.mp hyp_wecutisouniquecl_2 p0038
  have p0040 :=
    @gWeisouniquecl (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn C))) F G p0019 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end
