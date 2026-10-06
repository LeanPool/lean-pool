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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenfixedfwd`. -/
@[expose]
noncomputable def gWecutisogenfixedfwd (x : Var) (y : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (_dv_D_x : x ∉ D.fv)
    (dv_E_f : f ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_R_f : f ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_S_f : f ∉ S.fv) (_dv_S_y : y ∉ S.fv) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y)
    (hyp_wecutisogenfixedfwd_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisogenfixedfwd_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv f) (synCwecutisogen R D S E))) :=
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
  have dv_cache_0001 : f ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : f ∉ ((synChnwcutcode R D (.cv x))).fv :=
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
  have dv_cache_0004 : r ∉ ((synChnwcutcode R D (.cv x))).fv :=
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
  have dv_cache_0005 : f ∉ ((synChnwcutcode S E (.cv y))).fv :=
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
  have dv_cache_0006 : r ∉ ((synChnwcutcode S E (.cv y))).fv :=
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
  have dv_cache_0008 : r ∉ ((Wff.classMem (.cv f) (synCwecutisogen R D S E))).fv :=
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
      ((synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
              (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))).fv :=
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
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0001 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000
      p0001
  have p0003 := @gWecutisogencodeambient x D R hyp_wecutisogenfixedfwd_1
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D)
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv))) p0002 p0003
  have p0006 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0000
      p0006
  have p0008 := @gWecutisogencodeambient y E S hyp_wecutisogenfixedfwd_2
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) E)
      (.classMem (synChnwcutcode S E (.cv y)) (synChwcn (synCvv))) p0007 p0008
  have p0010 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv)))
      (.classMem (synChnwcutcode S E (.cv y)) (synChwcn (synCvv))) p0004 p0009
  have p0011 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0015 := @gWecutisogencodeparts x D R hyp_wecutisogenfixedfwd_1
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D)
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0002 p0015
  have p0017 :=
    @gSimpl
      (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0018 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0016 p0017
  have p0019 :=
    @gIsoeq2 (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
      (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
      (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
      (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.cv f)
  have p0020 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
          (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))))
      p0018 p0019
  have p0024 := @gWecutisogencodeparts y E S hyp_wecutisogenfixedfwd_2
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) E)
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0007 p0024
  have p0026 :=
    @gSimpl
      (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0027 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      p0025 p0026
  have p0028 :=
    @gIsoeq3 (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
      (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0029 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))))
      p0027 p0028
  have p0030 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      p0020 p0029
  have p0036 :=
    @gSimpr
      (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0037 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0016 p0036
  have p0038 :=
    @gIsoeq4 (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
      (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0039 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))))
      p0037 p0038
  have p0040 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      p0030 p0039
  have p0046 :=
    @gSimpr
      (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0047 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode S E (.cv y))) (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0025 p0046
  have p0048 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0049 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0047 p0048
  have p0050 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0040 p0049
  have p0051 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0011 p0050
  have p0052 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv)))
        (.classMem (synChnwcutcode S E (.cv y)) (synChwcn (synCvv))))
      (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode S E (.cv y))))
      p0010 p0051
  have p0053 :=
    @gWecutisogenrawcl (synCvv) (synChnwcutcode R D (.cv x))
      (synChnwcutcode S E (.cv y)) f r dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0054 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv)))
          (.classMem (synChnwcutcode S E (.cv y)) (synChwcn (synCvv))))
        (synWiso (.cv f) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
          (synCfv (synC1st) (synChnwcutcode S E (.cv y)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode S E (.cv y)))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      p0052 p0053
  have p0055 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
  have p0059 := @gWecutisogencodeinran x D R hyp_wecutisogenfixedfwd_1
  have p0060 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D)
      (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D))) p0002 p0059
  have p0064 := @gWecutisogencodeinran y E S hyp_wecutisogenfixedfwd_2
  have p0065 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) E)
      (.classMem (synChnwcutcode S E (.cv y)) (synCrn (synChnwcutrel S E))) p0007 p0064
  have p0066 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)))
      (.classMem (synChnwcutcode S E (.cv y)) (synCrn (synChnwcutrel S E))) p0060 p0065
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa
              (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)))
        (.classMem (synChnwcutcode S E (.cv y)) (synCrn (synChnwcutrel S E))))
      p0055 p0066
  have p0068 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
  have p0069 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa
              (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))))))
      (synWa (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)))
        (.classMem (synChnwcutcode S E (.cv y)) (synCrn (synChnwcutrel S E))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      p0067 p0068
  have p0070 :=
    @gWecutisogenrawmem (synChnwcutcode R D (.cv x)) (synChnwcutcode S E (.cv y)) D R S
      f E r
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa
              (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))))))
      (synWa (synWa (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)))
          (.classMem (synChnwcutcode S E (.cv y)) (synCrn (synChnwcutrel S E))))
        (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa
              (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))))))
      (.classMem (.cv f) (synCwecutisogen R D S E)) p0069 p0070
  have p0072 :=
    @gRexlimddv
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (.classMem (.cv f) (synCwecutisogen R D S E)) r (synCvv) dv_cache_0008
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisossgen`. -/
@[expose]
noncomputable def gWecutisossgen (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisossgen_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisossgen_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (synWss (synCwecutiso R D S E) (synCwecutisogen R D S E)) :=
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
  have dv_cache_0016 : x ∉ ((Wff.classMem (.cv f) (synCwecutisogen R D S E))).fv :=
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
  have dv_cache_0017 : y ∉ ((Wff.classMem (.cv f) (synCwecutisogen R D S E))).fv :=
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
  have dv_cache_0019 : f ∉ ((synCwecutiso R D S E)).fv :=
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
  have dv_cache_0020 : f ∉ ((synCwecutisogen R D S E)).fv :=
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
    @gElwecutiso x y D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @gBiimpi (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      p0000
  have p0002 :=
    @gWecutisogenfixedfwd x y D R S f E dv_cache_0012 dv_cache_0002 dv_cache_0013
      dv_cache_0003 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0007 dv_cache_0010
      dv_cache_0009 hyp_wecutisossgen_1 hyp_wecutisossgen_2
  have p0003 :=
    @gEx (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv f) (synCwecutisogen R D S E)) p0002
  have p0004 :=
    @gRexlimivv
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv f) (synCwecutisogen R D S E)) x y D E dv_cache_0001 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0003
  have p0005 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classMem (.cv f) (synCwecutisogen R D S E)) p0001 p0004
  have p0006 :=
    @gSsriv f (synCwecutiso R D S E) (synCwecutisogen R D S E) dv_cache_0019
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogensswecutiso`. -/
@[expose]
noncomputable def gWecutisogensswecutiso (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogensswecutiso_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisogensswecutiso_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (synWss (synCwecutisogen R D S E) (synCwecutiso R D S E)) :=
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
  have dv_cache_0006 : x ∉ ((synCop (.cv r) (synCdm (.cv f)))).fv :=
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
      ((synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f)))).fv :=
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
  have dv_cache_0025 : y ∉ ((Wff.classMem (.cv f) (synCwecutiso R D S E))).fv :=
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
      ((synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D) (.classEq (synCop (.cv r) (synCdm (.cv f)))
              (synChnwcutcode R D (.cv x)))))).fv :=
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
  have dv_cache_0027 : x ∉ ((Wff.classMem (.cv f) (synCwecutiso R D S E))).fv :=
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
      ((synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))).fv :=
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
  have dv_cache_0029 : r ∉ ((Wff.classMem (.cv f) (synCwecutiso R D S E))).fv :=
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
  have dv_cache_0030 : r ∉ ((Wff.classMem (.cv f) (synCwecutisogen R D S E))).fv :=
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
  have dv_cache_0031 : f ∉ ((synCwecutisogen R D S E)).fv :=
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
  have dv_cache_0032 : f ∉ ((synCwecutiso R D S E)).fv :=
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
    @gWecutisogenrawout D R S f E r dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gSimpr (.classMem (.cv f) (synCwecutisogen R D S E))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
  have p0002 :=
    @gSimpr (.classMem (.cv r) (synCvv))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
          (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))
  have p0003 :=
    @gSimpr
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
  have p0004 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
          (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      p0002 p0003
  have p0005 :=
    @gSimpl
      (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D))) p0004
      p0005
  have p0007 :=
    @gWecutisogenrangedecode x (synCop (.cv r) (synCdm (.cv f))) D R dv_cache_0006
      dv_cache_0007 dv_cache_0008 hyp_wecutisogensswecutiso_1
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
      (synWrex x D
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
      p0006 p0007
  have p0009 :=
    @gSimpl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (.cv x) D)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
  have p0013 :=
    @gSimpr
      (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))
  have p0014 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))
      p0004 p0013
  have p0015 :=
    @gWecutisogenrangedecode y
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      E S dv_cache_0009 dv_cache_0010 dv_cache_0011 hyp_wecutisogensswecutiso_2
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))
      (synWrex y E (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      p0014 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWrex y E (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      p0009 p0016
  have p0018 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (synWa (.classMem (.cv y) E) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (synChnwcutcode S E (.cv y))))
  have p0019 :=
    @gSimpr
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (.cv x) D)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (synWa (.classMem (.cv x) D)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
      p0018 p0019
  have p0021 :=
    @gSimpl (.classMem (.cv x) D)
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
      (.classMem (.cv x) D) p0020 p0021
  have p0023 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (synWa (.classMem (.cv y) E) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (synChnwcutcode S E (.cv y))))
  have p0024 :=
    @gSimpl (.classMem (.cv y) E)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv y) E) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (synChnwcutcode S E (.cv y))))
      (.classMem (.cv y) E) p0023 p0024
  have p0026 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (.classMem (.cv x) D) (.classMem (.cv y) E) p0022 p0025
  have p0029 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      p0018 p0009
  have p0031 :=
    @gSimpl
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
  have p0032 :=
    @gSyl
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
          (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0002 p0031
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0029 p0032
  have p0037 :=
    @gSimpr (.classMem (.cv x) D)
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
  have p0038 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) p0020
      p0037
  have p0040 :=
    @gSimpr (.classMem (.cv y) E)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv y) E) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (synChnwcutcode S E (.cv y))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
      p0023 p0040
  have p0042 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
      p0038 p0041
  have p0043 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      p0033 p0042
  have p0044 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      p0026 p0043
  have p0045 :=
    @gWecutisogenfixedrev x y D R S f E r dv_cache_0012 dv_cache_0001 dv_cache_0007
      dv_cache_0013 dv_cache_0014 dv_cache_0002 dv_cache_0015 dv_cache_0010 dv_cache_0016
      dv_cache_0003 dv_cache_0008 dv_cache_0017 dv_cache_0018 dv_cache_0004 dv_cache_0019
      dv_cache_0011 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                  (synCrn (synChnwcutrel R D))) (.classMem
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
          (synWa (.classMem (.cv x) D)
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
        (synWa (.classMem (.cv y) E) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classMem (.cv f) (synCwecutiso R D S E)) p0044 p0045
  have p0047 :=
    @gRexlimddv
      (synWa (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
        (synWa (.classMem (.cv x) D)
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
      (.classMem (.cv f) (synCwecutiso R D S E)) y E dv_cache_0025 dv_cache_0026 p0017
      p0046
  have p0048 :=
    @gRexlimddv
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
      (.classMem (.cv f) (synCwecutiso R D S E)) x D dv_cache_0027 dv_cache_0028 p0008
      p0047
  have p0049 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutisogen R D S E))
        (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (.classMem (.cv f) (synCwecutiso R D S E)) p0001 p0048
  have p0050 :=
    @gRexlimddv (.classMem (.cv f) (synCwecutisogen R D S E))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
          (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))
      (.classMem (.cv f) (synCwecutiso R D S E)) r (synCvv) dv_cache_0029 dv_cache_0030
      p0000 p0049
  have p0051 :=
    @gSsriv f (synCwecutisogen R D S E) (synCwecutiso R D S E) dv_cache_0031
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogeneq`. -/
@[expose]
noncomputable def gWecutisogeneq (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogeneq_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisogeneq_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (.classEq (synCwecutiso R D S E) (synCwecutisogen R D S E)) :=
  by
  have p0000 := @gWecutisossgen D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0001 := @gWecutisogensswecutiso D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0002 := @gEqssi (synCwecutiso R D S E) (synCwecutisogen R D S E) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenex`. -/
@[expose]
noncomputable def gWecutisogenex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisogenex_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisogenex_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (.classMem (synCwecutisogen R D S E) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwecutisogen R D S E))
  have p0001 := @gHwbijex
  have p0002 := @gVvex
  have p0003 := @gXpex (synChwbij) (synCvv) p0001 p0002
  have p0004 := @gHwgenex
  have p0005 := @gCnvex (synChwgen) p0004
  have p0006 := @gHnwcutrelex D R hyp_wecutisogenex_1
  have p0007 := @gRnex (synChnwcutrel R D) p0006
  have p0008 := @gHnwcutrelex E S hyp_wecutisogenex_2
  have p0009 := @gRnex (synChnwcutrel S E) p0008
  have p0010 :=
    @gXpex (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)) p0007 p0009
  have p0011 :=
    @gImaex (synCcnv (synChwgen))
      (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))) p0005 p0010
  have p0012 :=
    @gInex (synCxp (synChwbij) (synCvv))
      (synCima (synCcnv (synChwgen))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      p0003 p0011
  have p0013 :=
    @gDmex
      (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      p0012
  have p0014 :=
    @gEqeltri (synCwecutisogen R D S E)
      (synCdm (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synCvv) p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wecutisoex`. -/
@[expose]
noncomputable def gWecutisoex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisoex_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisoex_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (.classMem (synCwecutiso R D S E) (synCvv)) :=
  by
  have p0000 := @gWecutisogeneq D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0001 := @gWecutisogenex D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0002 :=
    @gEqeltri (synCwecutiso R D S E) (synCwecutisogen R D S E) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniex`. -/
@[expose]
noncomputable def gWecutisouniex (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisouniex_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisouniex_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv)) :=
  by
  have p0000 := @gWecutisoex D R S E hyp_wecutisouniex_1 hyp_wecutisouniex_2
  have p0001 := @gUniex (synCwecutiso R D S E) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfnfn`. -/
@[expose]
noncomputable def gWecutcardfnfn (D : Class) (R : Class) :
    Nominal.NPrf (synWfn (synCwecutcardfn R D) (synCpw1 (synCpw1 D))) :=
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
  have dv_cache_0003 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
    @gNcex
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfWecutcardfn D R q
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gFnmpti q (synCpw1 (synCpw1 D))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCwecutcardfn R D) dv_cache_0003 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfactorex`. -/
@[expose]
noncomputable def gWecutcardfactorex (D : Class) (R : Class)
    (hyp_wecutcardfactorex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synCwecutcardfactor R D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwecutcardfactor R D))
  have p0001 := @gEnex
  have p0002 := @gImageex (synCen) p0001
  have p0003 := @gN2ndex
  have p0004 := @gHnwcutrelex D R hyp_wecutcardfactorex_1
  have p0005 := @gCoex (synC2nd) (synChnwcutrel R D) p0003 p0004
  have p0006 := @gSiex (synCcom (synC2nd) (synChnwcutrel R D)) p0005
  have p0007 :=
    @gCoex (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
      p0002 p0006
  have p0008 :=
    @gEqeltri (synCwecutcardfactor R D)
      (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfactorfn`. -/
@[expose]
noncomputable def gWecutcardfactorfn (D : Class) (R : Class)
    (hyp_wecutcardfactorfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synCwecutcardfactor R D) (synCpw1 (synCpw1 D))) :=
  by
  have p0000 := @gEnex
  have p0001 := @gWppimagefn (synCen) p0000
  have p0002 := @gSsv (synCrn (synCimage (synCen)))
  have p0003 :=
    @gPm32i (synWfn (synCimage (synCen)) (synCvv))
      (synWss (synCrn (synCimage (synCen))) (synCvv)) p0001 p0002
  have p0004 := (Nominal.biimpRefl (synWf (synCimage (synCen)) (synCvv) (synCvv)))
  have p0005 :=
    @gMpbir (synWf (synCimage (synCen)) (synCvv) (synCvv))
      (synWa (synWfn (synCimage (synCen)) (synCvv))
        (synWss (synCrn (synCimage (synCen))) (synCvv)))
      p0003 p0004
  have p0006 := @gN2ndfo
  have p0007 := @gFof (synCvv) (synCvv) (synC2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gHnwcutrelfndv D R hyp_wecutcardfactorfn_1
  have p0010 := @gSsv (synChwcn D)
  have p0011 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synCvv)) p0009 p0010
  have p0012 := @gFss (synCpw1 D) (synChwcn D) (synCvv) (synChnwcutrel R D)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gPm32i (synWf (synC2nd) (synCvv) (synCvv))
      (synWf (synChnwcutrel R D) (synCpw1 D) (synCvv)) p0008 p0013
  have p0015 := @gFco (synCpw1 D) (synCvv) (synCvv) (synC2nd) (synChnwcutrel R D)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gSifmap (synCpw1 D) (synCvv) (synCcom (synC2nd) (synChnwcutrel R D))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gSsv (synCpw1 (synCvv))
  have p0020 :=
    @gPm32i
      (synWf (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (synCpw1 (synCpw1 D))
        (synCpw1 (synCvv)))
      (synWss (synCpw1 (synCvv)) (synCvv)) p0018 p0019
  have p0021 :=
    @gFss (synCpw1 (synCpw1 D)) (synCpw1 (synCvv)) (synCvv)
      (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gPm32i (synWf (synCimage (synCen)) (synCvv) (synCvv))
      (synWf (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (synCpw1 (synCpw1 D))
        (synCvv))
      p0005 p0022
  have p0024 :=
    @gFco (synCpw1 (synCpw1 D)) (synCvv) (synCvv) (synCimage (synCen))
      (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gFfn (synCpw1 (synCpw1 D)) (synCvv)
      (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (synCwecutcardfactor R D))
  have p0029 :=
    @gFneq1i (synCpw1 (synCpw1 D)) (synCwecutcardfactor R D)
      (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))
      p0028
  have p0030 :=
    @gMpbir (synWfn (synCwecutcardfactor R D) (synCpw1 (synCpw1 D)))
      (synWfn (synCcom (synCimage (synCen))
          (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))) (synCpw1 (synCpw1 D)))
      p0027 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_wecutcardhrelfn`. -/
@[expose]
noncomputable def gWecutcardhrelfn (D : Class) (R : Class)
    (hyp_wecutcardhrelfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synChnwcutrel R D) (synCpw1 D)) :=
  by
  have p0000 := @gHnwcutrelfndv D R hyp_wecutcardhrelfn_1
  have p0001 := @gSsv (synChwcn D)
  have p0002 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synCvv)) p0000 p0001
  have p0003 := @gFss (synCpw1 D) (synChwcn D) (synCvv) (synChnwcutrel R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gFfn (synCpw1 D) (synCvv) (synChnwcutrel R D)
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_wecutcardinnerf`. -/
@[expose]
noncomputable def gWecutcardinnerf (D : Class) (R : Class)
    (hyp_wecutcardinnerf_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (synWf (synCcom (synC2nd) (synChnwcutrel R D)) (synCpw1 D) (synCvv)) :=
  by
  have p0000 := @gN2ndfo
  have p0001 := @gFof (synCvv) (synCvv) (synC2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gHnwcutrelfndv D R hyp_wecutcardinnerf_1
  have p0004 := @gSsv (synChwcn D)
  have p0005 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synCvv)) p0003 p0004
  have p0006 := @gFss (synCpw1 D) (synChwcn D) (synCvv) (synChnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWf (synC2nd) (synCvv) (synCvv))
      (synWf (synChnwcutrel R D) (synCpw1 D) (synCvv)) p0002 p0007
  have p0009 := @gFco (synCpw1 D) (synCvv) (synCvv) (synC2nd) (synChnwcutrel R D)
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wecutcardsiliftfn`. -/
@[expose]
noncomputable def gWecutcardsiliftfn (D : Class) (R : Class)
    (hyp_wecutcardsiliftfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (synWfn (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (synCpw1 (synCpw1 D))) :=
  by
  have p0000 := @gN2ndfo
  have p0001 := @gFof (synCvv) (synCvv) (synC2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gHnwcutrelfndv D R hyp_wecutcardsiliftfn_1
  have p0004 := @gSsv (synChwcn D)
  have p0005 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synCvv)) p0003 p0004
  have p0006 := @gFss (synCpw1 D) (synChwcn D) (synCvv) (synChnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWf (synC2nd) (synCvv) (synCvv))
      (synWf (synChnwcutrel R D) (synCpw1 D) (synCvv)) p0002 p0007
  have p0009 := @gFco (synCpw1 D) (synCvv) (synCvv) (synC2nd) (synChnwcutrel R D)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gSifmap (synCpw1 D) (synCvv) (synCcom (synC2nd) (synChnwcutrel R D))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gFfn (synCpw1 (synCpw1 D)) (synCpw1 (synCvv))
      (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
  have p0014 := Nominal.mp p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfactorval`. -/
@[expose]
noncomputable def gWecutcardfactorval (D : Class) (R : Class) (q : Var)
    (_dv_D_q : q ∉ D.fv) (_dv_R_q : q ∉ R.fv)
    (hyp_wecutcardfactorval_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classEq (synCfv (synCwecutcardfactor R D) (.cv q)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwecutcardfactor R D))
  have p0001 :=
    @gFveq1i (.cv q) (synCwecutcardfactor R D)
      (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))
      p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwecutcardfactor R D) (.cv q)) (synCfv
          (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))
          (.cv q)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0001
  have p0003 := @gWecutcardsiliftfn D R hyp_wecutcardfactorval_1
  have p0004 :=
    @gA1i
      (synWfn (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0003
  have p0005 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0006 :=
    @gJca (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWfn (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0004 p0005
  have p0007 :=
    @gFvco2 (synCpw1 (synCpw1 D)) (.cv q) (synCimage (synCen))
      (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
  have p0008 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWa (synWfn (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
          (synCpw1 (synCpw1 D))) (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classEq (synCfv (synCcom (synCimage (synCen))
            (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))) (.cv q))
        (synCfv (synCimage (synCen))
          (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (.cv q))))
      p0006 p0007
  have p0009 := @gPw12argcl (.cv q) D
  have p0010 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0009
  have p0011 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q)))))
      (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) p0010
  have p0013 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0009
  have p0014 := @gSnelpw1 (synCuni (synCuni (.cv q))) D
  have p0015 :=
    @gBiimpri (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classMem (synCuni (synCuni (.cv q))) D) p0014
  have p0016 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D)) p0013 p0015
  have p0017 := @gWecutcardinnerf D R hyp_wecutcardfactorval_1
  have p0018 :=
    @gSifvald (synCpw1 D) (synCvv) (synCsn (synCuni (synCuni (.cv q))))
      (synCcom (synC2nd) (synChnwcutrel R D)) p0017
  have p0019 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classEq (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
          (synCsn (synCsn (synCuni (synCuni (.cv q)))))) (synCsn
          (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0016 p0018
  have p0020 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (.cv q))
      (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))
        (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0011 p0019
  have p0021 := @gWecutcardhrelfn D R hyp_wecutcardfactorval_1
  have p0022 :=
    @gA1i (synWfn (synChnwcutrel R D) (synCpw1 D))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0021
  have p0028 :=
    @gJca (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWfn (synChnwcutrel R D) (synCpw1 D))
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D)) p0022 p0016
  have p0029 :=
    @gFvco2 (synCpw1 D) (synCsn (synCuni (synCuni (.cv q)))) (synC2nd)
      (synChnwcutrel R D)
  have p0030 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWa (synWfn (synChnwcutrel R D) (synCpw1 D))
        (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D)))
      (.classEq (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
          (synCsn (synCuni (synCuni (.cv q))))) (synCfv (synC2nd)
          (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))))
      p0028 p0029
  have p0033 :=
    @gHnwcutrelvalcld (synCuni (synCuni (.cv q))) D R hyp_wecutcardfactorval_1
  have p0034 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
        (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      p0013 p0033
  have p0035 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synC2nd) p0034
  have p0036 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
        (synCsn (synCuni (synCuni (.cv q)))))
      (synCfv (synC2nd)
        (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q))))))
      (synCfv (synC2nd) (synChnwcutcode R D (synCuni (synCuni (.cv q))))) p0030 p0035
  have p0037 := (Nominal.classEqRefl (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
  have p0038 :=
    @gFveq2i (synChnwcutcode R D (synCuni (synCuni (.cv q))))
      (synCop (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))))
      (synC2nd) p0037
  have p0039 := @gBrex R D (synCwe)
  have p0040 := Nominal.mp hyp_wecutcardfactorval_1 p0039
  have p0041 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0040
  have p0044 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0040
  have p0048 := @gIdex
  have p0049 := @gDifex R (synCid) p0041 p0048
  have p0050 := @gCnvex (synCdif R (synCid)) p0049
  have p0051 := @gSnex (synCuni (synCuni (.cv q)))
  have p0052 :=
    @gImaex (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q))))
      p0050 p0051
  have p0053 :=
    @gInex D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))
      p0044 p0052
  have p0066 :=
    @gXpex
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0053 p0053
  have p0067 :=
    @gInex R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))))
      p0041 p0066
  have p0080 :=
    @gOpfv2nd
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q)))))) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0067 p0053
  have p0081 :=
    @gEqtri (synCfv (synC2nd) (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0038 p0080
  have p0082 :=
    @gA1i
      (.classEq (synCfv (synC2nd) (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0081
  have p0083 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
        (synCsn (synCuni (synCuni (.cv q)))))
      (synCfv (synC2nd) (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0036 p0082
  have p0084 :=
    @gSneqd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
        (synCsn (synCuni (synCuni (.cv q)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0083
  have p0085 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (.cv q))
      (synCsn (synCfv (synCcom (synC2nd) (synChnwcutrel R D))
          (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0020 p0084
  have p0086 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (.cv q))
      (synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCimage (synCen)) p0085
  have p0087 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synCimage (synCen))
          (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))) (.cv q))
      (synCfv (synCimage (synCen))
        (synCfv (synCsi (synCcom (synC2nd) (synChnwcutrel R D))) (.cv q)))
      (synCfv (synCimage (synCen)) (synCsn (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0008 p0086
  have p0088 := @gEnex
  have p0089 :=
    @gSnex
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
  have p0090 :=
    @gFvimagecl
      (synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCen) p0088 p0089
  have p0091 :=
    (Nominal.classEqRefl (synCec (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCen)))
  have p0092 :=
    @gEqcomi
      (synCec (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCen))
      (synCima (synCen) (synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0091
  have p0093 :=
    @gEqtri
      (synCfv (synCimage (synCen)) (synCsn (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCima (synCen) (synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCec (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCen))
      p0090 p0092
  have p0094 :=
    (Nominal.classEqRefl (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q))))))))
  have p0095 :=
    @gEqcomi
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCec (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCen))
      p0094
  have p0096 :=
    @gEqtri
      (synCfv (synCimage (synCen)) (synCsn (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCec (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))) (synCen))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0093 p0095
  have p0097 :=
    @gA1i
      (.classEq (synCfv (synCimage (synCen)) (synCsn (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0096
  have p0098 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synCimage (synCen))
          (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))) (.cv q))
      (synCfv (synCimage (synCen)) (synCsn (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0087 p0097
  have p0099 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCwecutcardfactor R D) (.cv q))
      (synCfv (synCcom (synCimage (synCen))
          (synCsi (synCcom (synC2nd) (synChnwcutrel R D)))) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0002 p0098
  exact p0099

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfnval`. -/
@[expose]
noncomputable def gWecutcardfnval (D : Class) (R : Class) (q : Var) (_dv_D_q : q ∉ D.fv)
    (_dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classEq (synCfv (synCwecutcardfn R D) (.cv q)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))))) :=
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
      ((synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q)))))))).fv :=
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
  have dv_cache_0005 : p ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0006 : p ∉ ((Wff.classMem (.cv q) (synCpw1 (synCpw1 D)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfWecutcardfn D R p
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gA1i
      (.classEq (synCwecutcardfn R D) (synCmpt p (synCpw1 (synCpw1 D)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv p)))))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0000
  have p0002 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q))
  have p0003 := @gUnieq (.cv p) (.cv q)
  have p0004 :=
    @gSyl (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (.classEq (.cv p) (.cv q)) (.classEq (synCuni (.cv p)) (synCuni (.cv q))) p0002
      p0003
  have p0005 :=
    @gUnieqd
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (synCuni (.cv p)) (synCuni (.cv q)) p0004
  have p0006 :=
    @gSneqd
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (synCuni (synCuni (.cv p))) (synCuni (synCuni (.cv q))) p0005
  have p0007 :=
    @gImaeq2d
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (synCsn (synCuni (synCuni (.cv p)))) (synCsn (synCuni (synCuni (.cv q))))
      (synCcnv (synCdif R (synCid))) p0006
  have p0008 :=
    @gIneq2d
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv p)))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))
      D p0007
  have p0009 :=
    @gNceqd
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv p) (.cv q)))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv p))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0008
  have p0010 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0011 :=
    @gNcex
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
  have p0012 :=
    @gA1i
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) (synCvv))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0011
  have p0013 :=
    @gFvmptd (.classMem (.cv q) (synCpw1 (synCpw1 D))) p (.cv q)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv p)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCpw1 (synCpw1 D)) (synCwecutcardfn R D) (synCvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0001 p0009 p0010 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfnfactor`. -/
@[expose]
noncomputable def gWecutcardfnfactor (D : Class) (R : Class)
    (hyp_wecutcardfnfactor_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classEq (synCwecutcardfn R D) (synCwecutcardfactor R D)) :=
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
  have dv_cache_0003 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0004 : q ∉ ((synCwecutcardfn R D)).fv :=
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
  have dv_cache_0005 : q ∉ ((synCwecutcardfactor R D)).fv :=
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
  have p0000 := @gWecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gWecutcardfactorval D R q dv_cache_0001 dv_cache_0002 hyp_wecutcardfnfactor_1
  have p0002 :=
    @gEqcomd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCwecutcardfactor R D) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0001
  have p0003 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCwecutcardfn R D) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCfv (synCwecutcardfactor R D) (.cv q)) p0000 p0002
  have p0004 :=
    @gRgen
      (.classEq (synCfv (synCwecutcardfn R D) (.cv q))
        (synCfv (synCwecutcardfactor R D) (.cv q)))
      q (synCpw1 (synCpw1 D)) p0003
  have p0005 := @gWecutcardfnfn D R
  have p0006 := @gWecutcardfactorfn D R hyp_wecutcardfnfactor_1
  have p0007 :=
    @gPm32i (synWfn (synCwecutcardfn R D) (synCpw1 (synCpw1 D)))
      (synWfn (synCwecutcardfactor R D) (synCpw1 (synCpw1 D))) p0005 p0006
  have p0008 :=
    @gEqfnfv q (synCpw1 (synCpw1 D)) (synCwecutcardfn R D) (synCwecutcardfactor R D)
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gMpbir (.classEq (synCwecutcardfn R D) (synCwecutcardfactor R D))
      (synWral q (synCpw1 (synCpw1 D)) (.classEq (synCfv (synCwecutcardfn R D) (.cv q))
          (synCfv (synCwecutcardfactor R D) (.cv q))))
      p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wecutcardfnex`. -/
@[expose]
noncomputable def gWecutcardfnex (D : Class) (R : Class)
    (hyp_wecutcardfnex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synCwecutcardfn R D) (synCvv)) :=
  by
  have p0000 := @gWecutcardfnfactor D R hyp_wecutcardfnex_1
  have p0001 := @gWecutcardfactorex D R hyp_wecutcardfnex_1
  have p0002 :=
    @gEqeltri (synCwecutcardfn R D) (synCwecutcardfactor R D) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wecutcardpreimandv`. -/
@[expose]
noncomputable def gWecutcardpreimandv (D : Class) (R : Class) (K : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (synWb (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K)) (.classMem
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K))) :=
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
  have dv_cache_0003 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
    @gNcex
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfWecutcardfn D R q
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gFnmpti q (synCpw1 (synCpw1 D))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCwecutcardfn R D) dv_cache_0003 p0000 p0001
  have p0003 := @gElpreima (synCpw1 (synCpw1 D)) (.cv q) K (synCwecutcardfn R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gA1i
      (synWb (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0004
  have p0006 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0007 :=
    @gBiantrurd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K) p0006
  have p0008 :=
    @gBicomd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K)
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K))
      p0007
  have p0009 :=
    @gBitrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K))
      (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K) p0005 p0008
  have p0010 := @gWecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0011 :=
    @gEleq1d (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCwecutcardfn R D) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      K p0010
  have p0012 :=
    @gBitrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (synCfv (synCwecutcardfn R D) (.cv q)) K)
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
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

/-- Checked nominal proof certificate identified upstream as `g_siorndv`. -/
@[expose]
noncomputable def gSiorndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) D) (synWbr (synCsi R) (synCstrict) (synCpw1 D))) :=
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
  have dv_cache_0001 : x ∉ ((synCpw1 D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0003 : z ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0004 : x ∉ ((synCsi R)).fv :=
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
  have dv_cache_0005 : y ∉ ((synCsi R)).fv :=
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
  have dv_cache_0006 : z ∉ ((synCsi R)).fv :=
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
  have dv_cache_0007 : x ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0008 : y ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0009 : z ∉ ((synWbr R (synCwe) D)).fv :=
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
  have p0000 := @gBrex R D (synCwe)
  have p0001 :=
    @gSimpld (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0000
  have p0002 := @gSiexg R (synCvv)
  have p0003 :=
    @gSyl (synWbr R (synCwe) D) (.classMem R (synCvv))
      (.classMem (synCsi R) (synCvv)) p0001 p0002
  have p0005 :=
    @gSimprd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0000
  have p0006 := @gPw1exg D (synCvv)
  have p0007 :=
    @gSyl (synWbr R (synCwe) D) (.classMem D (synCvv))
      (.classMem (synCpw1 D) (synCvv)) p0005 p0006
  have p0008 := @gSimpl (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
  have p0009 := @gWppweref D R
  have p0010 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (synWbr R (synCwe) D) (synWbr R (synCref) D) p0008 p0009
  have p0011 := @gSimpr (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
  have p0012 := @gHnwpw1argcl D x
  have p0013 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (.classMem (.cv x) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x)))))
      p0011 p0012
  have p0014 :=
    @gSimpld (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0013
  have p0015 :=
    @gRefd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))) D R
      (synCuni (.cv x)) p0010 p0014
  have p0019 :=
    @gSimprd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0013
  have p0024 :=
    @gBreq12d (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))) (.cv x)
      (synCsn (synCuni (.cv x))) (.cv x) (synCsn (synCuni (.cv x))) (synCsi R) p0019
      p0019
  have p0025 := @gVex x
  have p0026 := @gUniex (.cv x) p0025
  have p0029 := @gBrsnsi (synCuni (.cv x)) (synCuni (.cv x)) R p0026 p0026
  have p0030 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv x))))
        (synWbr (synCuni (.cv x)) R (synCuni (.cv x))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))) p0029
  have p0031 :=
    @gBitrd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (synWbr (.cv x) (synCsi R) (.cv x))
      (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv x))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv x))) p0024 p0030
  have p0032 :=
    @gBiimprd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (synWbr (.cv x) (synCsi R) (.cv x))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv x))) p0031
  have p0033 :=
    @gMpd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D)))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv x)))
      (synWbr (.cv x) (synCsi R) (.cv x)) p0015 p0032
  have p0034 :=
    @gSimp1 (synWbr R (synCwe) D)
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z)))
  have p0035 := @gWppwepo D R
  have p0036 := @gPorta D R
  have p0037 :=
    @gSimp2bi (synWbr R (synCpartial) D) (synWbr R (synCref) D)
      (synWbr R (synCtrans) D) (synWbr R (synCantisym) D) p0036
  have p0038 :=
    @gSyl (synWbr R (synCwe) D) (synWbr R (synCpartial) D) (synWbr R (synCtrans) D)
      p0035 p0037
  have p0039 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr R (synCwe) D) (synWbr R (synCtrans) D) p0034 p0038
  have p0040 :=
    @gSimp2 (synWbr R (synCwe) D)
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z)))
  have p0041 :=
    @gSimp1 (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
      (.classMem (.cv z) (synCpw1 D))
  have p0042 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (.classMem (.cv x) (synCpw1 D)) p0040 p0041
  have p0044 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (.cv x) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x)))))
      p0042 p0012
  have p0045 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0044
  have p0047 :=
    @gSimp2 (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
      (.classMem (.cv z) (synCpw1 D))
  have p0048 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (.classMem (.cv y) (synCpw1 D)) p0040 p0047
  have p0049 := @gHnwpw1argcl D y
  have p0050 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (.cv y) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y)))))
      p0048 p0049
  have p0051 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0050
  have p0053 :=
    @gSimp3 (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
      (.classMem (.cv z) (synCpw1 D))
  have p0054 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (.classMem (.cv z) (synCpw1 D)) p0040 p0053
  have p0055 := @gHnwpw1argcl D z
  have p0056 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (.cv z) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv z)) D) (.classEq (.cv z) (synCsn (synCuni (.cv z)))))
      p0054 p0055
  have p0057 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv z)) D) (.classEq (.cv z) (synCsn (synCuni (.cv z))))
      p0056
  have p0058 :=
    @gSimp3 (synWbr R (synCwe) D)
      (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
        (.classMem (.cv z) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z)))
  have p0059 :=
    @gSimpl (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z))
  have p0060 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z)))
      (synWbr (.cv x) (synCsi R) (.cv y)) p0058 p0059
  have p0066 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0044
  have p0072 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0050
  have p0073 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.cv x) (synCsn (synCuni (.cv x))) (.cv y) (synCsn (synCuni (.cv y)))
      (synCsi R) p0066 p0072
  have p0076 := @gVex y
  have p0077 := @gUniex (.cv y) p0076
  have p0078 := @gBrsnsi (synCuni (.cv x)) (synCuni (.cv y)) R p0026 p0077
  have p0079 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
        (synWbr (synCuni (.cv x)) R (synCuni (.cv y))))
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      p0078
  have p0080 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0073 p0079
  have p0081 :=
    @gBiimpd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0080
  have p0082 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0060 p0081
  have p0084 :=
    @gSimpr (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z))
  have p0085 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv z)))
      (synWbr (.cv y) (synCsi R) (.cv z)) p0058 p0084
  have p0097 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.classMem (synCuni (.cv z)) D) (.classEq (.cv z) (synCsn (synCuni (.cv z))))
      p0056
  have p0098 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.cv y) (synCsn (synCuni (.cv y))) (.cv z) (synCsn (synCuni (.cv z)))
      (synCsi R) p0072 p0097
  have p0101 := @gVex z
  have p0102 := @gUniex (.cv z) p0101
  have p0103 := @gBrsnsi (synCuni (.cv y)) (synCuni (.cv z)) R p0077 p0102
  have p0104 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv z))))
        (synWbr (synCuni (.cv y)) R (synCuni (.cv z))))
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      p0103
  have p0105 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv y) (synCsi R) (.cv z))
      (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv z))))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv z))) p0098 p0104
  have p0106 :=
    @gBiimpd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv y) (synCsi R) (.cv z))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv z))) p0105
  have p0107 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv y) (synCsi R) (.cv z))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv z))) p0085 p0106
  have p0108 :=
    @gTrd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      D R (synCuni (.cv x)) (synCuni (.cv y)) (synCuni (.cv z)) p0039 p0045 p0051 p0057
      p0082 p0107
  have p0121 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (.cv x) (synCsn (synCuni (.cv x))) (.cv z) (synCsn (synCuni (.cv z)))
      (synCsi R) p0066 p0097
  have p0126 := @gBrsnsi (synCuni (.cv x)) (synCuni (.cv z)) R p0026 p0102
  have p0127 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv z))))
        (synWbr (synCuni (.cv x)) R (synCuni (.cv z))))
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      p0126
  have p0128 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv x) (synCsi R) (.cv z))
      (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv z))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv z))) p0121 p0127
  have p0129 :=
    @gBiimprd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (.cv x) (synCsi R) (.cv z))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv z))) p0128
  have p0130 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D)
        (synW3a (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
          (.classMem (.cv z) (synCpw1 D))) (synWa (synWbr (.cv x) (synCsi R) (.cv y))
          (synWbr (.cv y) (synCsi R) (.cv z))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv z)))
      (synWbr (.cv x) (synCsi R) (.cv z)) p0108 p0129
  have p0131 :=
    @gSimp2 (synWbr R (synCwe) D)
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
  have p0132 := @gSimpl (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
  have p0133 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (.classMem (.cv x) (synCpw1 D)) p0131 p0132
  have p0135 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (.cv x) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x)))))
      p0133 p0012
  have p0136 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0135
  have p0137 :=
    @gSimp1 (synWbr R (synCwe) D)
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
  have p0138 := @gWppweantisym D R
  have p0139 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr R (synCwe) D) (synWbr R (synCantisym) D) p0137 p0138
  have p0145 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0135
  have p0147 := @gSimpr (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))
  have p0148 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (.classMem (.cv y) (synCpw1 D)) p0131 p0147
  have p0150 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (.cv y) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y)))))
      p0148 p0049
  have p0151 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0150
  have p0152 :=
    @gSimp3 (synWbr R (synCwe) D)
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
  have p0153 :=
    @gSimpl (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))
  have p0154 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      (synWbr (.cv x) (synCsi R) (.cv y)) p0152 p0153
  have p0166 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0150
  have p0167 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.cv x) (synCsn (synCuni (.cv x))) (.cv y) (synCsn (synCuni (.cv y)))
      (synCsi R) p0136 p0166
  have p0173 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
        (synWbr (synCuni (.cv x)) R (synCuni (.cv y))))
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      p0078
  have p0174 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0167 p0173
  have p0175 :=
    @gBiimpd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0174
  have p0176 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0154 p0175
  have p0178 :=
    @gSimpr (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))
  have p0179 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      (synWbr (.cv y) (synCsi R) (.cv x)) p0152 p0178
  have p0192 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.cv y) (synCsn (synCuni (.cv y))) (.cv x) (synCsn (synCuni (.cv x)))
      (synCsi R) p0166 p0136
  have p0197 := @gBrsnsi (synCuni (.cv y)) (synCuni (.cv x)) R p0077 p0026
  have p0198 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv x))))
        (synWbr (synCuni (.cv y)) R (synCuni (.cv x))))
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      p0197
  have p0199 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv x))))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0192 p0198
  have p0200 :=
    @gBiimpd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0199
  have p0201 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0179 p0200
  have p0202 :=
    @gAntid
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      D R (synCuni (.cv x)) (synCuni (.cv y)) p0139 p0145 p0151 p0176 p0201
  have p0203 :=
    @gSneqd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (synCuni (.cv x)) (synCuni (.cv y)) p0202
  have p0204 :=
    @gEqtrd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.cv x) (synCsn (synCuni (.cv x))) (synCsn (synCuni (.cv y))) p0136 p0203
  have p0211 :=
    @gEqcomd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.cv y) (synCsn (synCuni (.cv y))) p0166
  have p0212 :=
    @gEqtrd
      (synW3a (synWbr R (synCwe) D)
        (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
        (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
      (.cv x) (synCsn (synCuni (.cv y))) (.cv y) p0204 p0211
  have p0213 :=
    @gSimp1 (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
      (.classMem (.cv y) (synCpw1 D))
  have p0214 := @gWppweconnex D R
  have p0215 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr R (synCwe) D) (synWbr R (synCconnex) D) p0213 p0214
  have p0216 :=
    @gSimp2 (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
      (.classMem (.cv y) (synCpw1 D))
  have p0218 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (.cv x) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x)))))
      p0216 p0012
  have p0219 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0218
  have p0220 :=
    @gSimp3 (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
      (.classMem (.cv y) (synCpw1 D))
  have p0222 :=
    @gSyl
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (.cv y) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y)))))
      p0220 p0049
  have p0223 :=
    @gSimpld
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0222
  have p0224 :=
    @gConnexd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      D R (synCuni (.cv x)) (synCuni (.cv y)) p0215 p0219 p0223
  have p0228 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (synCuni (.cv x)) D) (.classEq (.cv x) (synCsn (synCuni (.cv x))))
      p0218
  have p0232 :=
    @gSimprd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.classMem (synCuni (.cv y)) D) (.classEq (.cv y) (synCsn (synCuni (.cv y))))
      p0222
  have p0233 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.cv x) (synCsn (synCuni (.cv x))) (.cv y) (synCsn (synCuni (.cv y)))
      (synCsi R) p0228 p0232
  have p0239 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
        (synWbr (synCuni (.cv x)) R (synCuni (.cv y))))
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      p0078
  have p0240 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCsn (synCuni (.cv x))) (synCsi R) (synCsn (synCuni (.cv y))))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0233 p0239
  have p0241 :=
    @gBiimprd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y))) p0240
  have p0242 :=
    @gOrc (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))
  have p0243 :=
    @gSyl6
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y)))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWo (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      p0241 p0242
  have p0252 :=
    @gBreq12d
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (.cv y) (synCsn (synCuni (.cv y))) (.cv x) (synCsn (synCuni (.cv x)))
      (synCsi R) p0232 p0228
  have p0258 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv x))))
        (synWbr (synCuni (.cv y)) R (synCuni (.cv x))))
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      p0197
  have p0259 :=
    @gBitrd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWbr (synCsn (synCuni (.cv y))) (synCsi R) (synCsn (synCuni (.cv x))))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0252 p0258
  have p0260 :=
    @gBiimprd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0259
  have p0261 :=
    @gOlc (synWbr (.cv y) (synCsi R) (.cv x)) (synWbr (.cv x) (synCsi R) (.cv y))
  have p0262 :=
    @gSyl6
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x)))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWo (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      p0260 p0261
  have p0263 :=
    @gJaod
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWbr (synCuni (.cv x)) R (synCuni (.cv y)))
      (synWo (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      (synWbr (synCuni (.cv y)) R (synCuni (.cv x))) p0243 p0262
  have p0264 :=
    @gMpd
      (synW3a (synWbr R (synCwe) D) (.classMem (.cv x) (synCpw1 D))
        (.classMem (.cv y) (synCpw1 D)))
      (synWo (synWbr (synCuni (.cv x)) R (synCuni (.cv y)))
        (synWbr (synCuni (.cv y)) R (synCuni (.cv x))))
      (synWo (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x)))
      p0224 p0263
  have p0265_e04_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWbr R (synCwe) D)
          (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
          (synWa (synWbr (.cv x) (synCsi R) (.cv y)) (synWbr (.cv y) (synCsi R) (.cv x))))
        (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synWex synCphi synCwe synCin synCstrict synCfound synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0212
  have p0265 :=
    @gSod (synWbr R (synCwe) D) x y z (synCpw1 D) (synCsi R) (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0003 p0007 p0033 p0130 p0265_e04_recanon p0264
  exact p0265


end NFChoice.DirectNominalPrf.WPPReplay

end
