/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisomemberrndownndv (w : Var) (v : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class)
    (hyp_wecutisomemberrndownndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
        (.classMem (.cv w) (syn_crn (.cv f)))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪
        ({ f } : Finset Var) ∪
      E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_w : x ≠ w := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
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
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
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
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
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
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
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
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
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
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
          (.classMem (.cv w) (syn_crn (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_ne_f, fresh_x_ne_w, fresh_x_not_E,
          fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((Wff.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
          (.classMem (.cv w) (syn_crn (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_v, fresh_u_ne_f, fresh_u_ne_w, fresh_u_not_E,
          fresh_u_not_S, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @g_elwecutisodmrn x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011
  have p0001 :=
    @g_a1i (syn_wbr S (syn_cwe) E)
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      hyp_wecutisomemberrndownndv_1
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wa (syn_wa (.classEq (syn_cdm (.cv f))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classEq (syn_crn (.cv f))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0003 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0002
      p0003
  have p0005 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E) p0001 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wa (syn_wa (.classEq (syn_cdm (.cv f))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classEq (syn_crn (.cv f))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0007 :=
    @g_simpr
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (syn_wa (.classEq (syn_cdm (.cv f))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classEq (syn_crn (.cv f))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
      p0006 p0007
  have p0009 :=
    @g_simpl (.classMem (.cv v) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
      (.classMem (.cv v) (syn_crn (.cv f))) p0008 p0009
  have p0012 :=
    @g_simpl
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (syn_wa (.classEq (syn_cdm (.cv f))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classEq (syn_crn (.cv f))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0006 p0012
  have p0014 :=
    @g_simpr
      (.classEq (syn_cdm (.cv f))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0013 p0014
  have p0016 :=
    @g_eleqtrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (.cv v) (syn_crn (.cv f))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0010
      p0015
  have p0020 :=
    @g_simpr (.classMem (.cv v) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) p0008 p0020
  have p0022 := @g_simpl (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) E)
      p0021 p0022
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (.classMem (.cv w) E) p0016 p0023
  have p0030 := @g_simpr (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
      (syn_wbr (.cv w) S (.cv v)) p0021 p0030
  have p0032 :=
    @g_n_3jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E))
      (syn_wa (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (.classMem (.cv w) E))
      (syn_wbr (.cv w) S (.cv v)) p0005 p0024 p0031
  have p0033 := @g_strictsegdown u v w E S
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (syn_w3a (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (.classMem (.cv w) E)) (syn_wbr (.cv w) S (.cv v)))
      (.classMem (.cv w)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0032 p0033
  have p0040 :=
    @g_eleqtrrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa
            (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
            (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))))
      (.cv w) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_crn (.cv f)) p0034 p0015
  have p0041 :=
    @g_exp32 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
      (.classMem (.cv w) (syn_crn (.cv f))) p0040
  have p0042 :=
    @g_rexlimivv
      (syn_wa (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (syn_crn (.cv f))))
      x u D E dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @g_syl (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex u E (syn_wa (.classEq (syn_cdm (.cv f))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classEq (syn_crn (.cv f)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))
      (.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (syn_crn (.cv f))))
      p0000 p0042
  have p0044 :=
    @g_imp (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
      (.classMem (.cv w) (syn_crn (.cv f))) p0043
  exact p0044

@[expose]
noncomputable def g_wecutisouniondmdownndv (y : Var) (z : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisouniondmdownndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))
        (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_y : f ≠ y := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_z : f ≠ z := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have dv_cache_0001 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_y, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((Wff.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))
          (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_z, fresh_f_not_D, fresh_f_ne_y, fresh_f_not_R,
          fresh_f_not_E, fresh_f_not_S, or_false, not_false_eq_true])
  have p0000 := @g_dmuni f (syn_cwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @g_eleq2i (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_ciun f (syn_cwecutiso R D S E) (syn_cdm (.cv f))) (.cv y) p0000
  have p0002 := @g_eliun f (.cv y) (syn_cwecutiso R D S E) (syn_cdm (.cv f)) dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv y) (syn_ciun f (syn_cwecutiso R D S E) (syn_cdm (.cv f))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f)))) p0001
      p0002
  have p0004 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f)))) p0003
  have p0005 := @g_wecutisomemberdmdownndv y z D R S f E hyp_wecutisouniondmdownndv_1
  have p0006 :=
    @g_simpl (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wa (.classMem (.cv y) (syn_cdm (.cv f)))
        (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))
  have p0007 := @g_elssuni (.cv f) (syn_cwecutiso R D S E)
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv y) (syn_cdm (.cv f)))
          (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))))
      (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) p0006 p0007
  have p0009 := @g_dmss (.cv f) (syn_cuni (syn_cwecutiso R D S E))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv y) (syn_cdm (.cv f)))
          (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))))
      (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E)))
      (syn_wss (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @g_ssel (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (.cv z)
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv y) (syn_cdm (.cv f)))
          (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))))
      (syn_wss (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.imp (.classMem (.cv z) (syn_cdm (.cv f)))
        (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      p0010 p0011
  have p0013 :=
    @g_mpd
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv y) (syn_cdm (.cv f)))
          (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))))
      (.classMem (.cv z) (syn_cdm (.cv f)))
      (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @g_exp32 (.classMem (.cv f) (syn_cwecutiso R D S E))
      (.classMem (.cv y) (syn_cdm (.cv f)))
      (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0013
  have p0015 :=
    @g_rexlimiv (.classMem (.cv y) (syn_cdm (.cv f)))
      (.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))
        (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      f (syn_cwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @g_syl (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f))))
      (.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))
        (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      p0004 p0015
  have p0017 :=
    @g_imp (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0016
  exact p0017

@[expose]
noncomputable def g_wecutisounionrndownndv (w : Var) (v : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisounionrndownndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_w : f ≠ w := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have dv_cache_0001 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_v, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((Wff.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
          (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_w, fresh_f_not_E, fresh_f_ne_v, fresh_f_not_S,
          fresh_f_not_D, fresh_f_not_R, or_false, not_false_eq_true])
  have p0000 := @g_rnuni f (syn_cwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @g_eleq2i (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_ciun f (syn_cwecutiso R D S E) (syn_crn (.cv f))) (.cv v) p0000
  have p0002 := @g_eliun f (.cv v) (syn_cwecutiso R D S E) (syn_crn (.cv f)) dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv v) (syn_ciun f (syn_cwecutiso R D S E) (syn_crn (.cv f))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f)))) p0001
      p0002
  have p0004 :=
    @g_biimpi (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f)))) p0003
  have p0005 := @g_wecutisomemberrndownndv w v D R S f E hyp_wecutisounionrndownndv_1
  have p0006 :=
    @g_simpl (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0007 := @g_elssuni (.cv f) (syn_cwecutiso R D S E)
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) p0006 p0007
  have p0009 := @g_rnss (.cv f) (syn_cuni (syn_cwecutiso R D S E))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E)))
      (syn_wss (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @g_ssel (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (.cv w)
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (syn_wss (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (.imp (.classMem (.cv w) (syn_crn (.cv f)))
        (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0010 p0011
  have p0013 :=
    @g_mpd
      (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (.classMem (.cv v) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
      (.classMem (.cv w) (syn_crn (.cv f)))
      (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @g_exp32 (.classMem (.cv f) (syn_cwecutiso R D S E))
      (.classMem (.cv v) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
      (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0013
  have p0015 :=
    @g_rexlimiv (.classMem (.cv v) (syn_crn (.cv f)))
      (.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
        (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      f (syn_cwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @g_syl (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f))))
      (.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
        (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0004 p0015
  have p0017 :=
    @g_imp (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
      (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisouniondmsscutndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_wecutisouniondmsscutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have dv_cache_0001 : y ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001
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
  have dv_cache_0003 :
    y ∉
      ((syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
  have p0001 := @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpli (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0001
  have p0003 := @g_sseli (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D (.cv y) p0002
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv y) D) p0000 p0003
  have p0005 := @g_id (syn_wbr (.cv y) R (.cv x))
  have p0006 :=
    @g_a1i (.imp (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      p0005
  have p0007 :=
    @g_simpl
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
  have p0008 :=
    @g_simpr (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0007 p0008
  have p0010 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv x) R (.cv y))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0010 p0000
  have p0015 :=
    @g_simpl (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv x) D) p0007 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv x) D) p0010 p0016
  have p0018 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv x) R (.cv y))
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv y)) p0017 p0018
  have p0020 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv y))) p0012 p0019
  have p0021 := @g_wecutisouniondmdownndv y x D R S E hyp_wecutisouniondmsscutndv_1
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wa (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv y))))
      (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0020 p0021
  have p0023 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0022
  have p0024 :=
    @g_mtod
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0009 p0023
  have p0025 :=
    @g_pm2_21d
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)) p0024
  have p0026 := @g_wppweconnex D R
  have p0027 := Nominal.mp hyp_wecutisouniondmsscutndv_1 p0026
  have p0028 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      p0027
  have p0037 :=
    @g_connexd
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      D R (.cv y) (.cv x) p0028 p0004 p0016
  have p0038 :=
    @g_mpjaod
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv x) R (.cv y))
      p0006 p0025 p0037
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0000 p0009
  have p0044 := @g_nelne2 (.cv y) (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wne (.cv y) (.cv x)) p0043 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0038 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0004 p0046
  have p0048 := @g_elstrictseg x y D R
  have p0049 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0047 p0048
  have p0050 :=
    @g_ex
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0049
  have p0051 :=
    @g_ssrdv
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      y (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0050
  exact p0051

@[expose]
noncomputable def g_wecutisounionrnsscutndv (u : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_wecutisounionrnsscutndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    v ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))).fv :=
    by
    clear dv_cache_0001
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
          Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_D, fresh_v_not_R,
          fresh_v_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
  have p0001 := @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpri (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0001
  have p0003 := @g_sseli (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E (.cv v) p0002
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv v) E) p0000 p0003
  have p0005 := @g_id (syn_wbr (.cv v) S (.cv u))
  have p0006 :=
    @g_a1i (.imp (syn_wbr (.cv v) S (.cv u)) (syn_wbr (.cv v) S (.cv u)))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0005
  have p0007 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
  have p0008 :=
    @g_simpr (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0007 p0008
  have p0010 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv u) S (.cv v))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv u) S (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0010 p0000
  have p0015 :=
    @g_simpl (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv u) E) p0007 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv u) S (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv u) E) p0010 p0016
  have p0018 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv u) S (.cv v))
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv u) S (.cv v)))
      (.classMem (.cv u) E) (syn_wbr (.cv u) S (.cv v)) p0017 p0018
  have p0020 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv u) S (.cv v)))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (.classMem (.cv u) E) (syn_wbr (.cv u) S (.cv v))) p0012 p0019
  have p0021 := @g_wecutisounionrndownndv u v D R S E hyp_wecutisounionrnsscutndv_1
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wbr (.cv u) S (.cv v)))
      (syn_wa (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wa (.classMem (.cv u) E) (syn_wbr (.cv u) S (.cv v))))
      (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0020 p0021
  have p0023 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv u) S (.cv v))
      (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0022
  have p0024 :=
    @g_mtod
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv u) S (.cv v))
      (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0009 p0023
  have p0025 :=
    @g_pm2_21d
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv u) S (.cv v)) (syn_wbr (.cv v) S (.cv u)) p0024
  have p0026 := @g_wppweconnex E S
  have p0027 := Nominal.mp hyp_wecutisounionrnsscutndv_1 p0026
  have p0028 :=
    @g_a1i (syn_wbr S (syn_cconnex) E)
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0027
  have p0037 :=
    @g_connexd
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      E S (.cv v) (.cv u) p0028 p0004 p0016
  have p0038 :=
    @g_mpjaod
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv v) S (.cv u)) (syn_wbr (.cv v) S (.cv u)) (syn_wbr (.cv u) S (.cv v))
      p0006 p0025 p0037
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0000 p0009
  have p0044 := @g_nelne2 (.cv v) (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wne (.cv v) (.cv u)) p0043 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)) p0038 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))
      p0004 p0046
  have p0048 := @g_elstrictseg u v E S
  have p0049 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wa (.classMem (.cv v) E)
        (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0047 p0048
  have p0050 :=
    @g_ex
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0049
  have p0051 :=
    @g_ssrdv
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      v (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0050
  exact p0051

@[expose]
noncomputable def g_wecutisouniondmexactcutndv (x : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisouniondmexactcutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x)))))
        (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have dv_cache_0002 : y ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima R (syn_csn (.cv x))))
  have p0001 := @g_wecutisouniondmsscutndv x D R S E hyp_wecutisouniondmexactcutndv_1
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0004 := @g_elstrictseg x y D R
  have p0005 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0003 p0004
  have p0006 :=
    @g_simprr (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (syn_wne (.cv y) (.cv x)) p0005 p0006
  have p0008 := @g_wppweantisym D R
  have p0009 := Nominal.mp hyp_wecutisouniondmexactcutndv_1 p0008
  have p0010 :=
    @g_a1i (syn_wbr R (syn_cantisym) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0015 :=
    @g_simpl (.classMem (.cv y) D)
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y) D) p0005 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y) D) p0011 p0016
  have p0019 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      p0011 p0019
  have p0022 :=
    @g_simpl (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv x) D) p0000 p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (.classMem (.cv x) D) p0020 p0023
  have p0029 :=
    @g_simprl (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (syn_wbr (.cv y) R (.cv x)) p0005 p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x)) p0011 p0030
  have p0035 :=
    @g_simpr
      (syn_wa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima R (syn_csn (.cv x))))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima R (syn_csn (.cv x))))
      p0020 p0035
  have p0044 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0017 p0044
  have p0046 := @g_eldif (.cv y) D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
  have p0047 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (.classMem (.cv y) D)
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0045
      p0046
  have p0048 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (syn_cima R (syn_csn (.cv x))) (.cv y) p0036 p0047
  have p0049 := @g_elimasn R (.cv x) (.cv y)
  have p0050 := (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y)))
  have p0051 :=
    @g_bitr4i (.classMem (.cv y) (syn_cima R (syn_csn (.cv x))))
      (.classMem (syn_cop (.cv x) (.cv y)) R) (syn_wbr (.cv x) R (.cv y)) p0049 p0050
  have p0052 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv y) (syn_cima R (syn_csn (.cv x)))) (syn_wbr (.cv x) R (.cv y)) p0048
      p0051
  have p0053 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      D R (.cv y) (.cv x) p0010 p0017 p0024 p0031 p0052
  have p0054 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.classEq (.cv y) (.cv x)) p0053
  have p0055 :=
    @g_necon3ad
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.cv y)
      (.cv x) p0054
  have p0056 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wne (.cv y) (.cv x))
      (.neg (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))) p0007
      p0055
  have p0057 :=
    @g_notnotrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv x))))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0056
  have p0058 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0057
  have p0059 :=
    @g_ssrdv
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      y (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0058
  have p0060 :=
    @g_eqssd
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv x)))))
      (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0002
      p0059
  exact p0060


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisounionrnexactcutndv (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisounionrnexactcutndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u)))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    v ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))).fv :=
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
          Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_D, fresh_v_not_R,
          fresh_v_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima S (syn_csn (.cv u))))
  have p0001 := @g_wecutisounionrnsscutndv u D R S E hyp_wecutisounionrnexactcutndv_1
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0004 := @g_elstrictseg u v E S
  have p0005 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wa (.classMem (.cv v) E)
        (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))))
      p0003 p0004
  have p0006 :=
    @g_simprr (.classMem (.cv v) E) (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) E)
        (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))))
      (syn_wne (.cv v) (.cv u)) p0005 p0006
  have p0008 := @g_wppweantisym E S
  have p0009 := Nominal.mp hyp_wecutisounionrnexactcutndv_1 p0008
  have p0010 :=
    @g_a1i (syn_wbr S (syn_cantisym) E)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0015 :=
    @g_simpl (.classMem (.cv v) E)
      (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) E)
        (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))))
      (.classMem (.cv v) E) p0005 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv v) E) p0011 p0016
  have p0019 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      p0011 p0019
  have p0022 :=
    @g_simpl (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv u) E) p0000 p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (.classMem (.cv u) E) p0020 p0023
  have p0029 :=
    @g_simprl (.classMem (.cv v) E) (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv v) E)
        (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))))
      (syn_wbr (.cv v) S (.cv u)) p0005 p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wbr (.cv v) S (.cv u)) p0011 p0030
  have p0035 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima S (syn_csn (.cv u))))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima S (syn_csn (.cv u))))
      p0020 p0035
  have p0044 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) E)
      (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0017 p0044
  have p0046 := @g_eldif (.cv v) E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
  have p0047 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wa (.classMem (.cv v) E)
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0045
      p0046
  have p0048 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_cima S (syn_csn (.cv u))) (.cv v) p0036 p0047
  have p0049 := @g_elimasn S (.cv u) (.cv v)
  have p0050 := (Nominal.biimpRefl (syn_wbr (.cv u) S (.cv v)))
  have p0051 :=
    @g_bitr4i (.classMem (.cv v) (syn_cima S (syn_csn (.cv u))))
      (.classMem (syn_cop (.cv u) (.cv v)) S) (syn_wbr (.cv u) S (.cv v)) p0049 p0050
  have p0052 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.classMem (.cv v) (syn_cima S (syn_csn (.cv u)))) (syn_wbr (.cv u) S (.cv v)) p0048
      p0051
  have p0053 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      E S (.cv v) (.cv u) p0010 p0017 p0024 p0031 p0052
  have p0054 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (.classEq (.cv v) (.cv u)) p0053
  have p0055 :=
    @g_necon3ad
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (.cv v)
      (.cv u) p0054
  have p0056 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wne (.cv v) (.cv u))
      (.neg (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) p0007
      p0055
  have p0057 :=
    @g_notnotrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0056
  have p0058 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (.classMem (.cv v)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0057
  have p0059 :=
    @g_ssrdv
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      v (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0058
  have p0060 :=
    @g_eqssd
      (syn_wa (syn_wa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0002
      p0059
  exact p0060

@[expose]
noncomputable def g_wecutisoaddpairf1ondv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wf1o (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))))) :=
  by
  have p0000 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0001 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S H
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0004 := @g_f1osng (.cv x) (.cv u) D E
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u)))
      p0003 p0004
  have p0006 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u)))
      p0002 p0005
  have p0007 := @g_strictsegnel x D R
  have p0008 :=
    @g_disjsn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (.cv x)
  have p0009 :=
    @g_mpbir
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_c0))
      (.neg (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0007 p0008
  have p0010 :=
    @g_a1i
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_c0))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0009
  have p0011 := @g_strictsegnel u E S
  have p0012 :=
    @g_disjsn (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (.cv u)
  have p0013 :=
    @g_mpbir
      (.classEq (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) (syn_c0))
      (.neg (.classMem (.cv u)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0011 p0012
  have p0014 :=
    @g_a1i
      (.classEq (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) (syn_c0))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_c0))
      (.classEq (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) (syn_c0))
      p0010 p0014
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wf1o H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u))))
      (syn_wa (.classEq (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) (syn_c0)) (.classEq (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) (syn_c0)))
      p0006 p0015
  have p0017 :=
    @g_f1oun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_csn (.cv x)) (syn_csn (.cv u)) H (syn_csn (syn_cop (.cv x) (.cv u)))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (syn_wf1o H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u))))
        (syn_wa (.classEq (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) (syn_c0)) (.classEq (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) (syn_c0))))
      (syn_wf1o (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0016 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisoaddpairisondv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
            (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))) (syn_wiso H R S
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_wiso (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) R S (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
              (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))) (syn_wiso H R S
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_not_S,
          fresh_z_not_E, fresh_z_ne_x, fresh_z_ne_u, fresh_z_not_H, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
            (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))) (syn_wiso H R S
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, fresh_y_not_S,
          fresh_y_not_E, fresh_y_ne_x, fresh_y_ne_u, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉
      ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_E, fresh_y_not_S, fresh_y_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_E, fresh_z_not_S, fresh_z_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_H, fresh_y_ne_x, fresh_y_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_H, fresh_z_ne_x, fresh_z_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0012 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0013 : y ∉ (S).fv :=
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
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0014 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  let syntaxFormula0000 : Wff :=
    (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)))
  let syntaxFormula0001 : Wff :=
    (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxFormula0002 : Wff := (syn_wa syntaxFormula0000 syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) syntaxFormula0001)
  let syntaxClass0004 : Class :=
    (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_csn (.cv x)))
  let syntaxClass0005 : Class :=
    (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_csn (.cv u)))
  let syntaxFormula0006 : Wff :=
    (syn_wf1o (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) syntaxClass0004 syntaxClass0005)
  let syntaxFormula0007 : Wff := (.classMem (.cv y) syntaxClass0004)
  let syntaxFormula0008 : Wff := (syn_wa syntaxFormula0002 syntaxFormula0007)
  let syntaxFormula0009 : Wff := (.classMem (.cv z) syntaxClass0004)
  let syntaxFormula0010 : Wff := (syn_wa syntaxFormula0008 syntaxFormula0009)
  let syntaxFormula0011 : Wff :=
    (.classMem (.cv y)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0012 : Wff := (syn_wa syntaxFormula0010 syntaxFormula0011)
  let syntaxFormula0013 : Wff :=
    (.classMem (.cv z)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0014 : Wff := (syn_wa syntaxFormula0012 syntaxFormula0013)
  let syntaxFormula0015 : Wff := (syn_wa syntaxFormula0011 syntaxFormula0013)
  let syntaxClass0016 : Class :=
    (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
  let syntaxFormula0017 : Wff :=
    (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      syntaxClass0016)
  let syntaxFormula0018 : Wff := (.classMem (.cv y) syntaxClass0016)
  let syntaxFormula0019 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv y) (syn_csn (.cv x)))))
  let syntaxFormula0020 : Wff := (.classMem (.cv z) syntaxClass0016)
  let syntaxFormula0021 : Wff :=
    (syn_wa (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv z) (syn_csn (.cv x)))))
  let syntaxFormula0022 : Wff :=
    (syn_wbr (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y)) S
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z)))
  let syntaxFormula0023 : Wff := (syn_wb (syn_wbr (.cv y) R (.cv z)) syntaxFormula0022)
  let syntaxFormula0024 : Wff := (syn_wa syntaxFormula0012 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0025 : Wff :=
    (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxFormula0026 : Wff :=
    (syn_wf H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxClass0027 : Class :=
    (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (.cv u)))) (syn_csn (.cv u)))
  let syntaxFormula0028 : Wff :=
    (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      syntaxClass0027)
  let syntaxFormula0029 : Wff :=
    (.classMem (syn_cfv H (.cv y)) (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (.cv u)))))
  let syntaxFormula0030 : Wff :=
    (.classMem (syn_cop (.cv x) (.cv u)) (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))))
  let syntaxFormula0031 : Wff :=
    (.classEq (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv x)) (.cv u))
  let syntaxFormula0032 : Wff := (.imp syntaxFormula0030 syntaxFormula0031)
  let syntaxFormula0033 : Wff := (syn_wo syntaxFormula0013 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0034 : Wff := (syn_wa syntaxFormula0010 (.classEq (.cv y) (.cv x)))
  let syntaxFormula0035 : Wff := (syn_wa syntaxFormula0034 syntaxFormula0013)
  let syntaxFormula0036 : Wff := (syn_wa syntaxFormula0035 (syn_wbr (.cv x) R (.cv z)))
  let syntaxFormula0037 : Wff :=
    (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
  let syntaxFormula0038 : Wff := (syn_wa syntaxFormula0026 syntaxFormula0013)
  let syntaxFormula0039 : Wff :=
    (.classMem (syn_cfv H (.cv z))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxFormula0040 : Wff := (.classMem (syn_cfv H (.cv z)) syntaxClass0027)
  let syntaxFormula0041 : Wff :=
    (.classMem (syn_cfv H (.cv z)) (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (.cv u)))))
  let syntaxFormula0042 : Wff :=
    (syn_wa syntaxFormula0041 (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u)))))
  let syntaxFormula0043 : Wff :=
    (syn_wa syntaxFormula0035 (syn_wbr (.cv u) S (syn_cfv H (.cv z))))
  let syntaxFormula0044 : Wff :=
    (syn_wa (.classMem (syn_cfv H (.cv z)) E)
      (.classMem (syn_cfv H (.cv z)) (syn_cima (syn_ccnv S) (syn_csn (.cv u)))))
  let syntaxFormula0045 : Wff := (syn_wa syntaxFormula0034 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0046 : Wff := (syn_wral z syntaxClass0004 syntaxFormula0023)
  let syntaxFormula0047 : Wff := (syn_wral y syntaxClass0004 syntaxFormula0046)
  have p0000 := @g_simpl syntaxFormula0000 syntaxFormula0001
  have p0001 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
  have p0002 :=
    @g_syl syntaxFormula0002 syntaxFormula0000
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) p0000 p0001
  have p0003 := @g_simpr syntaxFormula0000 syntaxFormula0001
  have p0004 :=
    @g_jca syntaxFormula0002 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      syntaxFormula0001 p0002 p0003
  have p0005 := @g_wecutisoaddpairf1ondv x u D R S E H
  have p0006 := @g_syl syntaxFormula0002 syntaxFormula0003 syntaxFormula0006 p0004 p0005
  have p0007 := @g_simpl syntaxFormula0012 syntaxFormula0013
  have p0008 := @g_simpl syntaxFormula0010 syntaxFormula0011
  have p0009 := @g_syl syntaxFormula0014 syntaxFormula0012 syntaxFormula0010 p0007 p0008
  have p0010 := @g_simpl syntaxFormula0008 syntaxFormula0009
  have p0011 := @g_simpl syntaxFormula0002 syntaxFormula0007
  have p0012 := @g_syl syntaxFormula0010 syntaxFormula0008 syntaxFormula0002 p0010 p0011
  have p0013 := @g_syl syntaxFormula0014 syntaxFormula0010 syntaxFormula0002 p0009 p0012
  have p0015 := @g_syl syntaxFormula0014 syntaxFormula0002 syntaxFormula0001 p0013 p0003
  have p0017 := @g_simpr syntaxFormula0010 syntaxFormula0011
  have p0018 := @g_syl syntaxFormula0014 syntaxFormula0012 syntaxFormula0011 p0007 p0017
  have p0019 := @g_simpr syntaxFormula0012 syntaxFormula0013
  have p0020 := @g_jca syntaxFormula0014 syntaxFormula0011 syntaxFormula0013 p0018 p0019
  have p0021 := @g_jca syntaxFormula0014 syntaxFormula0001 syntaxFormula0015 p0015 p0020
  have p0022 :=
    @g_isorel (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv y)
      (.cv z) R S H
  have p0023 :=
    @g_syl syntaxFormula0014 (syn_wa syntaxFormula0001 syntaxFormula0015)
      (syn_wb (syn_wbr (.cv y) R (.cv z)) (syn_wbr (syn_cfv H (.cv y)) S (syn_cfv H (.cv z))))
      p0021 p0022
  have p0037 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0038 :=
    @g_syl syntaxFormula0002 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (.cv x) D) p0002 p0037
  have p0039 := @g_elex (.cv x) D
  have p0040 :=
    @g_syl syntaxFormula0002 (.classMem (.cv x) D) (.classMem (.cv x) (syn_cvv)) p0038
      p0039
  have p0041 :=
    @g_syl syntaxFormula0014 syntaxFormula0002 (.classMem (.cv x) (syn_cvv)) p0013 p0040
  have p0042 := @g_strictsegdifiniclndv (.cv x) D R
  have p0043 :=
    @g_syl syntaxFormula0014 (.classMem (.cv x) (syn_cvv)) syntaxFormula0017 p0041 p0042
  have p0044 :=
    @g_eleq2d syntaxFormula0014
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      syntaxClass0016 (.cv y) p0043
  have p0045 := @g_mpbid syntaxFormula0014 syntaxFormula0011 syntaxFormula0018 p0018 p0044
  have p0046 :=
    @g_eldif (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_csn (.cv x))
  have p0047 := @g_sylib syntaxFormula0014 syntaxFormula0018 syntaxFormula0019 p0045 p0046
  have p0048 :=
    @g_simpr (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv y) (syn_csn (.cv x))))
  have p0049 :=
    @g_syl syntaxFormula0014 syntaxFormula0019
      (.neg (.classMem (.cv y) (syn_csn (.cv x)))) p0047 p0048
  have p0065 := @g_elsnc2g (.cv y) (.cv x) (syn_cvv)
  have p0066 :=
    @g_syl syntaxFormula0014 (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (.cv y) (syn_csn (.cv x))) (.classEq (.cv y) (.cv x))) p0041
      p0065
  have p0067 :=
    @g_notbid syntaxFormula0014 (.classMem (.cv y) (syn_csn (.cv x)))
      (.classEq (.cv y) (.cv x)) p0066
  have p0068 := (Nominal.biimpRefl (syn_wne (.cv y) (.cv x)))
  have p0069 :=
    @g_a1i (syn_wb (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      syntaxFormula0014 p0068
  have p0070 :=
    @g_bitr4d syntaxFormula0014 (.neg (.classMem (.cv y) (syn_csn (.cv x))))
      (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0067 p0069
  have p0071 :=
    @g_mpbid syntaxFormula0014 (.neg (.classMem (.cv y) (syn_csn (.cv x))))
      (syn_wne (.cv y) (.cv x)) p0049 p0070
  have p0072 := @g_necomd syntaxFormula0014 (.cv y) (.cv x) p0071
  have p0073 := @g_fvunsn H (.cv x) (.cv u) (.cv y)
  have p0074 :=
    @g_syl syntaxFormula0014 (syn_wne (.cv x) (.cv y))
      (.classEq (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
        (syn_cfv H (.cv y)))
      p0072 p0073
  have p0093 :=
    @g_eleq2d syntaxFormula0014
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      syntaxClass0016 (.cv z) p0043
  have p0094 := @g_mpbid syntaxFormula0014 syntaxFormula0013 syntaxFormula0020 p0019 p0093
  have p0095 :=
    @g_eldif (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_csn (.cv x))
  have p0096 := @g_sylib syntaxFormula0014 syntaxFormula0020 syntaxFormula0021 p0094 p0095
  have p0097 :=
    @g_simpr (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv z) (syn_csn (.cv x))))
  have p0098 :=
    @g_syl syntaxFormula0014 syntaxFormula0021
      (.neg (.classMem (.cv z) (syn_csn (.cv x)))) p0096 p0097
  have p0114 := @g_elsnc2g (.cv z) (.cv x) (syn_cvv)
  have p0115 :=
    @g_syl syntaxFormula0014 (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (.cv z) (syn_csn (.cv x))) (.classEq (.cv z) (.cv x))) p0041
      p0114
  have p0116 :=
    @g_notbid syntaxFormula0014 (.classMem (.cv z) (syn_csn (.cv x)))
      (.classEq (.cv z) (.cv x)) p0115
  have p0117 := (Nominal.biimpRefl (syn_wne (.cv z) (.cv x)))
  have p0118 :=
    @g_a1i (syn_wb (syn_wne (.cv z) (.cv x)) (.neg (.classEq (.cv z) (.cv x))))
      syntaxFormula0014 p0117
  have p0119 :=
    @g_bitr4d syntaxFormula0014 (.neg (.classMem (.cv z) (syn_csn (.cv x))))
      (.neg (.classEq (.cv z) (.cv x))) (syn_wne (.cv z) (.cv x)) p0116 p0118
  have p0120 :=
    @g_mpbid syntaxFormula0014 (.neg (.classMem (.cv z) (syn_csn (.cv x))))
      (syn_wne (.cv z) (.cv x)) p0098 p0119
  have p0121 := @g_necomd syntaxFormula0014 (.cv z) (.cv x) p0120
  have p0122 := @g_fvunsn H (.cv x) (.cv u) (.cv z)
  have p0123 :=
    @g_syl syntaxFormula0014 (syn_wne (.cv x) (.cv z))
      (.classEq (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
        (syn_cfv H (.cv z)))
      p0121 p0122
  have p0124 :=
    @g_breq12d syntaxFormula0014
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
      (syn_cfv H (.cv y))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
      (syn_cfv H (.cv z)) S p0074 p0123
  have p0125 :=
    @g_bitr4d syntaxFormula0014 (syn_wbr (.cv y) R (.cv z))
      (syn_wbr (syn_cfv H (.cv y)) S (syn_cfv H (.cv z))) syntaxFormula0022 p0023 p0124
  have p0126 := @g_ex syntaxFormula0012 syntaxFormula0013 syntaxFormula0023 p0125
  have p0127 := @g_simpl syntaxFormula0012 (.classEq (.cv z) (.cv x))
  have p0129 := @g_syl syntaxFormula0024 syntaxFormula0012 syntaxFormula0011 p0127 p0017
  have p0132 := @g_syl syntaxFormula0024 syntaxFormula0012 syntaxFormula0010 p0127 p0008
  have p0136 := @g_syl syntaxFormula0024 syntaxFormula0010 syntaxFormula0002 p0132 p0012
  have p0144 :=
    @g_syl syntaxFormula0024 syntaxFormula0002 (.classMem (.cv x) (syn_cvv)) p0136 p0040
  have p0146 :=
    @g_syl syntaxFormula0024 (.classMem (.cv x) (syn_cvv)) syntaxFormula0017 p0144 p0042
  have p0147 :=
    @g_eleq2d syntaxFormula0024
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      syntaxClass0016 (.cv y) p0146
  have p0148 := @g_mpbid syntaxFormula0024 syntaxFormula0011 syntaxFormula0018 p0129 p0147
  have p0150 := @g_sylib syntaxFormula0024 syntaxFormula0018 syntaxFormula0019 p0148 p0046
  have p0151 :=
    @g_simpl (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv y) (syn_csn (.cv x))))
  have p0152 :=
    @g_syl syntaxFormula0024 syntaxFormula0019
      (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0150
      p0151
  have p0153 := @g_elin (.cv y) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0154 :=
    @g_sylib syntaxFormula0024
      (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      p0152 p0153
  have p0155 :=
    @g_simpr (.classMem (.cv y) D)
      (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0156 :=
    @g_syl syntaxFormula0024
      (syn_wa (.classMem (.cv y) D)
        (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0154 p0155
  have p0157 := @g_eliniseg R (.cv x) (.cv y)
  have p0158 :=
    @g_sylib syntaxFormula0024
      (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_wbr (.cv y) R (.cv x)) p0156 p0157
  have p0159 := @g_simpr syntaxFormula0012 (.classEq (.cv z) (.cv x))
  have p0160 := @g_breq2d syntaxFormula0024 (.cv z) (.cv x) (.cv y) R p0159
  have p0161 :=
    @g_mpbird syntaxFormula0024 (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv y) R (.cv x))
      p0158 p0160
  have p0170 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S H
  have p0171 := @g_syl syntaxFormula0002 syntaxFormula0001 syntaxFormula0025 p0003 p0170
  have p0172 :=
    @g_f1of (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) H
  have p0173 := @g_syl syntaxFormula0002 syntaxFormula0025 syntaxFormula0026 p0171 p0172
  have p0174 := @g_syl syntaxFormula0024 syntaxFormula0002 syntaxFormula0026 p0136 p0173
  have p0178 := @g_jca syntaxFormula0024 syntaxFormula0026 syntaxFormula0011 p0174 p0129
  have p0179 :=
    @g_ffvelrn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv y) H
  have p0180 :=
    @g_syl syntaxFormula0024 (syn_wa syntaxFormula0026 syntaxFormula0011)
      (.classMem (syn_cfv H (.cv y))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0178 p0179
  have p0191 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0192 :=
    @g_syl syntaxFormula0002 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0002 p0191
  have p0193 := @g_elex (.cv u) E
  have p0194 :=
    @g_syl syntaxFormula0002 (.classMem (.cv u) E) (.classMem (.cv u) (syn_cvv)) p0192
      p0193
  have p0195 :=
    @g_syl syntaxFormula0024 syntaxFormula0002 (.classMem (.cv u) (syn_cvv)) p0136 p0194
  have p0196 := @g_strictsegdifiniclndv (.cv u) E S
  have p0197 :=
    @g_syl syntaxFormula0024 (.classMem (.cv u) (syn_cvv)) syntaxFormula0028 p0195 p0196
  have p0198 :=
    @g_eleq2d syntaxFormula0024
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      syntaxClass0027 (syn_cfv H (.cv y)) p0197
  have p0199 :=
    @g_mpbid syntaxFormula0024
      (.classMem (syn_cfv H (.cv y))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (.classMem (syn_cfv H (.cv y)) syntaxClass0027) p0180 p0198
  have p0200 :=
    @g_eldif (syn_cfv H (.cv y)) (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
      (syn_csn (.cv u))
  have p0201 :=
    @g_sylib syntaxFormula0024 (.classMem (syn_cfv H (.cv y)) syntaxClass0027)
      (syn_wa syntaxFormula0029 (.neg (.classMem (syn_cfv H (.cv y)) (syn_csn (.cv u)))))
      p0199 p0200
  have p0202 :=
    @g_simpl syntaxFormula0029 (.neg (.classMem (syn_cfv H (.cv y)) (syn_csn (.cv u))))
  have p0203 :=
    @g_syl syntaxFormula0024
      (syn_wa syntaxFormula0029 (.neg (.classMem (syn_cfv H (.cv y)) (syn_csn (.cv u)))))
      syntaxFormula0029 p0201 p0202
  have p0204 := @g_elin (syn_cfv H (.cv y)) E (syn_cima (syn_ccnv S) (syn_csn (.cv u)))
  have p0205 :=
    @g_sylib syntaxFormula0024 syntaxFormula0029
      (syn_wa (.classMem (syn_cfv H (.cv y)) E)
        (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv S) (syn_csn (.cv u)))))
      p0203 p0204
  have p0206 :=
    @g_simpr (.classMem (syn_cfv H (.cv y)) E)
      (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
  have p0207 :=
    @g_syl syntaxFormula0024
      (syn_wa (.classMem (syn_cfv H (.cv y)) E)
        (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv S) (syn_csn (.cv u)))))
      (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv S) (syn_csn (.cv u)))) p0205
      p0206
  have p0208 := @g_eliniseg S (.cv u) (syn_cfv H (.cv y))
  have p0209 :=
    @g_sylib syntaxFormula0024
      (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
      (syn_wbr (syn_cfv H (.cv y)) S (.cv u)) p0207 p0208
  have p0235 :=
    @g_syl syntaxFormula0024 syntaxFormula0019
      (.neg (.classMem (.cv y) (syn_csn (.cv x)))) p0150 p0048
  have p0252 :=
    @g_syl syntaxFormula0024 (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (.cv y) (syn_csn (.cv x))) (.classEq (.cv y) (.cv x))) p0144
      p0065
  have p0253 :=
    @g_notbid syntaxFormula0024 (.classMem (.cv y) (syn_csn (.cv x)))
      (.classEq (.cv y) (.cv x)) p0252
  have p0255 :=
    @g_a1i (syn_wb (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      syntaxFormula0024 p0068
  have p0256 :=
    @g_bitr4d syntaxFormula0024 (.neg (.classMem (.cv y) (syn_csn (.cv x))))
      (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0253 p0255
  have p0257 :=
    @g_mpbid syntaxFormula0024 (.neg (.classMem (.cv y) (syn_csn (.cv x))))
      (syn_wne (.cv y) (.cv x)) p0235 p0256
  have p0258 := @g_necomd syntaxFormula0024 (.cv y) (.cv x) p0257
  have p0260 :=
    @g_syl syntaxFormula0024 (syn_wne (.cv x) (.cv y))
      (.classEq (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
        (syn_cfv H (.cv y)))
      p0258 p0073
  have p0262 :=
    @g_fveq2d syntaxFormula0024 (.cv z) (.cv x)
      (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) p0159
  have p0273 := @g_opexg (.cv x) (.cv u) D E
  have p0274 :=
    @g_syl syntaxFormula0002 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (syn_cop (.cv x) (.cv u)) (syn_cvv)) p0002 p0273
  have p0275 := @g_snidg (syn_cop (.cv x) (.cv u)) (syn_cvv)
  have p0276 :=
    @g_syl syntaxFormula0002 (.classMem (syn_cop (.cv x) (.cv u)) (syn_cvv))
      (.classMem (syn_cop (.cv x) (.cv u)) (syn_csn (syn_cop (.cv x) (.cv u)))) p0274
      p0275
  have p0277 := @g_elun2 (syn_cop (.cv x) (.cv u)) (syn_csn (syn_cop (.cv x) (.cv u))) H
  have p0278 :=
    @g_syl syntaxFormula0002
      (.classMem (syn_cop (.cv x) (.cv u)) (syn_csn (syn_cop (.cv x) (.cv u))))
      syntaxFormula0030 p0276 p0277
  have p0286 :=
    @g_f1ofun syntaxClass0004 syntaxClass0005
      (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))
  have p0287 :=
    @g_syl syntaxFormula0002 syntaxFormula0006
      (syn_wfun (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))) p0006 p0286
  have p0288 := @g_funopfv (.cv x) (.cv u) (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))
  have p0289 :=
    @g_syl syntaxFormula0002 (syn_wfun (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))))
      syntaxFormula0032 p0287 p0288
  have p0290 := @g_mpd syntaxFormula0002 syntaxFormula0030 syntaxFormula0031 p0278 p0289
  have p0291 := @g_syl syntaxFormula0024 syntaxFormula0002 syntaxFormula0031 p0136 p0290
  have p0292 :=
    @g_eqtrd syntaxFormula0024
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0262
      p0291
  have p0293 :=
    @g_breq12d syntaxFormula0024
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
      (syn_cfv H (.cv y))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z)) (.cv u) S p0260
      p0292
  have p0294 :=
    @g_mpbird syntaxFormula0024 syntaxFormula0022 (syn_wbr (syn_cfv H (.cv y)) S (.cv u))
      p0209 p0293
  have p0295 :=
    @g_n_2thd syntaxFormula0024 (syn_wbr (.cv y) R (.cv z)) syntaxFormula0022 p0161 p0294
  have p0296 := @g_ex syntaxFormula0012 (.classEq (.cv z) (.cv x)) syntaxFormula0023 p0295
  have p0298 := @g_simpr syntaxFormula0008 syntaxFormula0009
  have p0299 :=
    @g_elun (.cv z)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_csn (.cv x))
  have p0300 := @g_elsn z (.cv x) dv_cache_0001
  have p0301 :=
    @g_orbi2i (.classMem (.cv z) (syn_csn (.cv x))) (.classEq (.cv z) (.cv x))
      syntaxFormula0013 p0300
  have p0302 :=
    @g_bitri syntaxFormula0009
      (syn_wo syntaxFormula0013 (.classMem (.cv z) (syn_csn (.cv x)))) syntaxFormula0033
      p0299 p0301
  have p0303 := @g_sylib syntaxFormula0010 syntaxFormula0009 syntaxFormula0033 p0298 p0302
  have p0304 := @g_syl syntaxFormula0012 syntaxFormula0010 syntaxFormula0033 p0008 p0303
  have p0305 :=
    @g_mpjaod syntaxFormula0012 syntaxFormula0013 syntaxFormula0023
      (.classEq (.cv z) (.cv x)) p0126 p0296 p0304
  have p0306 := @g_ex syntaxFormula0010 syntaxFormula0011 syntaxFormula0023 p0305
  have p0307 := @g_simpr syntaxFormula0034 syntaxFormula0013
  have p0308 := @g_simpl syntaxFormula0034 syntaxFormula0013
  have p0309 := @g_simpl syntaxFormula0010 (.classEq (.cv y) (.cv x))
  have p0310 := @g_syl syntaxFormula0035 syntaxFormula0034 syntaxFormula0010 p0308 p0309
  have p0314 := @g_syl syntaxFormula0035 syntaxFormula0010 syntaxFormula0002 p0310 p0012
  have p0322 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv x) (syn_cvv)) p0314 p0040
  have p0324 :=
    @g_syl syntaxFormula0035 (.classMem (.cv x) (syn_cvv)) syntaxFormula0017 p0322 p0042
  have p0325 :=
    @g_eleq2d syntaxFormula0035
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      syntaxClass0016 (.cv z) p0324
  have p0326 := @g_mpbid syntaxFormula0035 syntaxFormula0013 syntaxFormula0020 p0307 p0325
  have p0328 := @g_sylib syntaxFormula0035 syntaxFormula0020 syntaxFormula0021 p0326 p0095
  have p0330 :=
    @g_syl syntaxFormula0035 syntaxFormula0021
      (.neg (.classMem (.cv z) (syn_csn (.cv x)))) p0328 p0097
  have p0347 :=
    @g_syl syntaxFormula0035 (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (.cv z) (syn_csn (.cv x))) (.classEq (.cv z) (.cv x))) p0322
      p0114
  have p0348 :=
    @g_notbid syntaxFormula0035 (.classMem (.cv z) (syn_csn (.cv x)))
      (.classEq (.cv z) (.cv x)) p0347
  have p0350 :=
    @g_a1i (syn_wb (syn_wne (.cv z) (.cv x)) (.neg (.classEq (.cv z) (.cv x))))
      syntaxFormula0035 p0117
  have p0351 :=
    @g_bitr4d syntaxFormula0035 (.neg (.classMem (.cv z) (syn_csn (.cv x))))
      (.neg (.classEq (.cv z) (.cv x))) (syn_wne (.cv z) (.cv x)) p0348 p0350
  have p0352 :=
    @g_mpbid syntaxFormula0035 (.neg (.classMem (.cv z) (syn_csn (.cv x))))
      (syn_wne (.cv z) (.cv x)) p0330 p0351
  have p0353 := @g_simpl syntaxFormula0035 (syn_wbr (.cv x) R (.cv z))
  have p0362 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E))
  have p0363 :=
    @g_syl syntaxFormula0002 syntaxFormula0000
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)) p0000 p0362
  have p0364 := @g_simpl (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)
  have p0365 :=
    @g_syl syntaxFormula0002 (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wbr R (syn_cwe) D) p0363 p0364
  have p0366 := @g_wppweantisym D R
  have p0367 :=
    @g_syl syntaxFormula0002 (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cantisym) D) p0365
      p0366
  have p0368 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (syn_wbr R (syn_cantisym) D) p0314 p0367
  have p0369 :=
    @g_syl syntaxFormula0036 syntaxFormula0035 (syn_wbr R (syn_cantisym) D) p0353 p0368
  have p0393 :=
    @g_simpl (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv z) (syn_csn (.cv x))))
  have p0394 :=
    @g_syl syntaxFormula0035 syntaxFormula0021
      (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0328
      p0393
  have p0395 := @g_elin (.cv z) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0396 :=
    @g_sylib syntaxFormula0035
      (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      syntaxFormula0037 p0394 p0395
  have p0397 :=
    @g_simpl (.classMem (.cv z) D)
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0398 :=
    @g_syl syntaxFormula0035 syntaxFormula0037 (.classMem (.cv z) D) p0396 p0397
  have p0399 :=
    @g_syl syntaxFormula0036 syntaxFormula0035 (.classMem (.cv z) D) p0353 p0398
  have p0413 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv x) D) p0314 p0038
  have p0414 :=
    @g_syl syntaxFormula0036 syntaxFormula0035 (.classMem (.cv x) D) p0353 p0413
  have p0442 :=
    @g_simpr (.classMem (.cv z) D)
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0443 :=
    @g_syl syntaxFormula0035 syntaxFormula0037
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0396 p0442
  have p0444 := @g_eliniseg R (.cv x) (.cv z)
  have p0445 :=
    @g_sylib syntaxFormula0035
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_wbr (.cv z) R (.cv x)) p0443 p0444
  have p0446 :=
    @g_syl syntaxFormula0036 syntaxFormula0035 (syn_wbr (.cv z) R (.cv x)) p0353 p0445
  have p0447 := @g_simpr syntaxFormula0035 (syn_wbr (.cv x) R (.cv z))
  have p0448 :=
    @g_antid syntaxFormula0036 D R (.cv z) (.cv x) p0369 p0399 p0414 p0446 p0447
  have p0449 :=
    @g_ex syntaxFormula0035 (syn_wbr (.cv x) R (.cv z)) (.classEq (.cv z) (.cv x)) p0448
  have p0450 :=
    @g_necon3ad syntaxFormula0035 (syn_wbr (.cv x) R (.cv z)) (.cv z) (.cv x) p0449
  have p0451 :=
    @g_mpd syntaxFormula0035 (syn_wne (.cv z) (.cv x)) (.neg (syn_wbr (.cv x) R (.cv z)))
      p0352 p0450
  have p0453 := @g_simpr syntaxFormula0010 (.classEq (.cv y) (.cv x))
  have p0454 :=
    @g_syl syntaxFormula0035 syntaxFormula0034 (.classEq (.cv y) (.cv x)) p0308 p0453
  have p0455 := @g_breq1d syntaxFormula0035 (.cv y) (.cv x) (.cv z) R p0454
  have p0456 :=
    @g_notbid syntaxFormula0035 (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv x) R (.cv z))
      p0455
  have p0457 :=
    @g_mpbird syntaxFormula0035 (.neg (syn_wbr (.cv y) R (.cv z)))
      (.neg (syn_wbr (.cv x) R (.cv z))) p0451 p0456
  have p0470 := @g_syl syntaxFormula0035 syntaxFormula0002 syntaxFormula0026 p0314 p0173
  have p0472 := @g_jca syntaxFormula0035 syntaxFormula0026 syntaxFormula0013 p0470 p0307
  have p0473 :=
    @g_ffvelrn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv z) H
  have p0474 := @g_syl syntaxFormula0035 syntaxFormula0038 syntaxFormula0039 p0472 p0473
  have p0489 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv u) (syn_cvv)) p0314 p0194
  have p0491 :=
    @g_syl syntaxFormula0035 (.classMem (.cv u) (syn_cvv)) syntaxFormula0028 p0489 p0196
  have p0492 :=
    @g_eleq2d syntaxFormula0035
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      syntaxClass0027 (syn_cfv H (.cv z)) p0491
  have p0493 := @g_mpbid syntaxFormula0035 syntaxFormula0039 syntaxFormula0040 p0474 p0492
  have p0494 :=
    @g_eldif (syn_cfv H (.cv z)) (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
      (syn_csn (.cv u))
  have p0495 := @g_sylib syntaxFormula0035 syntaxFormula0040 syntaxFormula0042 p0493 p0494
  have p0496 :=
    @g_simpr syntaxFormula0041 (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u))))
  have p0497 :=
    @g_syl syntaxFormula0035 syntaxFormula0042
      (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u)))) p0495 p0496
  have p0513 := @g_elsnc2g (syn_cfv H (.cv z)) (.cv u) (syn_cvv)
  have p0514 :=
    @g_syl syntaxFormula0035 (.classMem (.cv u) (syn_cvv))
      (syn_wb (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u)))
        (.classEq (syn_cfv H (.cv z)) (.cv u)))
      p0489 p0513
  have p0515 :=
    @g_notbid syntaxFormula0035 (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u)))
      (.classEq (syn_cfv H (.cv z)) (.cv u)) p0514
  have p0516 := (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv z)) (.cv u)))
  have p0517 :=
    @g_a1i
      (syn_wb (syn_wne (syn_cfv H (.cv z)) (.cv u))
        (.neg (.classEq (syn_cfv H (.cv z)) (.cv u))))
      syntaxFormula0035 p0516
  have p0518 :=
    @g_bitr4d syntaxFormula0035 (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u))))
      (.neg (.classEq (syn_cfv H (.cv z)) (.cv u))) (syn_wne (syn_cfv H (.cv z)) (.cv u))
      p0515 p0517
  have p0519 :=
    @g_mpbid syntaxFormula0035 (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u))))
      (syn_wne (syn_cfv H (.cv z)) (.cv u)) p0497 p0518
  have p0520 := @g_simpl syntaxFormula0035 (syn_wbr (.cv u) S (syn_cfv H (.cv z)))
  have p0531 := @g_simpr (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)
  have p0532 :=
    @g_syl syntaxFormula0002 (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wbr S (syn_cwe) E) p0363 p0531
  have p0533 := @g_wppweantisym E S
  have p0534 :=
    @g_syl syntaxFormula0002 (syn_wbr S (syn_cwe) E) (syn_wbr S (syn_cantisym) E) p0532
      p0533
  have p0535 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (syn_wbr S (syn_cantisym) E) p0314 p0534
  have p0536 :=
    @g_syl syntaxFormula0043 syntaxFormula0035 (syn_wbr S (syn_cantisym) E) p0520 p0535
  have p0576 :=
    @g_simpl syntaxFormula0041 (.neg (.classMem (syn_cfv H (.cv z)) (syn_csn (.cv u))))
  have p0577 := @g_syl syntaxFormula0035 syntaxFormula0042 syntaxFormula0041 p0495 p0576
  have p0578 := @g_elin (syn_cfv H (.cv z)) E (syn_cima (syn_ccnv S) (syn_csn (.cv u)))
  have p0579 := @g_sylib syntaxFormula0035 syntaxFormula0041 syntaxFormula0044 p0577 p0578
  have p0580 :=
    @g_simpl (.classMem (syn_cfv H (.cv z)) E)
      (.classMem (syn_cfv H (.cv z)) (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
  have p0581 :=
    @g_syl syntaxFormula0035 syntaxFormula0044 (.classMem (syn_cfv H (.cv z)) E) p0579
      p0580
  have p0582 :=
    @g_syl syntaxFormula0043 syntaxFormula0035 (.classMem (syn_cfv H (.cv z)) E) p0520
      p0581
  have p0596 :=
    @g_syl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv u) E) p0314 p0192
  have p0597 :=
    @g_syl syntaxFormula0043 syntaxFormula0035 (.classMem (.cv u) E) p0520 p0596
  have p0641 :=
    @g_simpr (.classMem (syn_cfv H (.cv z)) E)
      (.classMem (syn_cfv H (.cv z)) (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
  have p0642 :=
    @g_syl syntaxFormula0035 syntaxFormula0044
      (.classMem (syn_cfv H (.cv z)) (syn_cima (syn_ccnv S) (syn_csn (.cv u)))) p0579
      p0641
  have p0643 := @g_eliniseg S (.cv u) (syn_cfv H (.cv z))
  have p0644 :=
    @g_sylib syntaxFormula0035
      (.classMem (syn_cfv H (.cv z)) (syn_cima (syn_ccnv S) (syn_csn (.cv u))))
      (syn_wbr (syn_cfv H (.cv z)) S (.cv u)) p0642 p0643
  have p0645 :=
    @g_syl syntaxFormula0043 syntaxFormula0035 (syn_wbr (syn_cfv H (.cv z)) S (.cv u))
      p0520 p0644
  have p0646 := @g_simpr syntaxFormula0035 (syn_wbr (.cv u) S (syn_cfv H (.cv z)))
  have p0647 :=
    @g_antid syntaxFormula0043 E S (syn_cfv H (.cv z)) (.cv u) p0536 p0582 p0597 p0645
      p0646
  have p0648 :=
    @g_ex syntaxFormula0035 (syn_wbr (.cv u) S (syn_cfv H (.cv z)))
      (.classEq (syn_cfv H (.cv z)) (.cv u)) p0647
  have p0649 :=
    @g_necon3ad syntaxFormula0035 (syn_wbr (.cv u) S (syn_cfv H (.cv z)))
      (syn_cfv H (.cv z)) (.cv u) p0648
  have p0650 :=
    @g_mpd syntaxFormula0035 (syn_wne (syn_cfv H (.cv z)) (.cv u))
      (.neg (syn_wbr (.cv u) S (syn_cfv H (.cv z)))) p0519 p0649
  have p0654 :=
    @g_fveq2d syntaxFormula0035 (.cv y) (.cv x)
      (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) p0454
  have p0683 := @g_syl syntaxFormula0035 syntaxFormula0002 syntaxFormula0031 p0314 p0290
  have p0684 :=
    @g_eqtrd syntaxFormula0035
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0654
      p0683
  have p0731 := @g_necomd syntaxFormula0035 (.cv z) (.cv x) p0352
  have p0733 :=
    @g_syl syntaxFormula0035 (syn_wne (.cv x) (.cv z))
      (.classEq (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
        (syn_cfv H (.cv z)))
      p0731 p0122
  have p0734 :=
    @g_breq12d syntaxFormula0035
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y)) (.cv u)
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
      (syn_cfv H (.cv z)) S p0684 p0733
  have p0735 :=
    @g_notbid syntaxFormula0035 syntaxFormula0022 (syn_wbr (.cv u) S (syn_cfv H (.cv z)))
      p0734
  have p0736 :=
    @g_mpbird syntaxFormula0035 (.neg syntaxFormula0022)
      (.neg (syn_wbr (.cv u) S (syn_cfv H (.cv z)))) p0650 p0735
  have p0737 :=
    @g_n_2falsed syntaxFormula0035 (syn_wbr (.cv y) R (.cv z)) syntaxFormula0022 p0457
      p0736
  have p0738 := @g_ex syntaxFormula0034 syntaxFormula0013 syntaxFormula0023 p0737
  have p0739 := @g_simpl syntaxFormula0034 (.classEq (.cv z) (.cv x))
  have p0741 := @g_syl syntaxFormula0045 syntaxFormula0034 syntaxFormula0010 p0739 p0309
  have p0745 := @g_syl syntaxFormula0045 syntaxFormula0010 syntaxFormula0002 p0741 p0012
  have p0751 := @g_wppweref D R
  have p0752 :=
    @g_syl syntaxFormula0002 (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cref) D) p0365 p0751
  have p0758 := @g_refd syntaxFormula0002 D R (.cv x) p0752 p0038
  have p0759 :=
    @g_syl syntaxFormula0045 syntaxFormula0002 (syn_wbr (.cv x) R (.cv x)) p0745 p0758
  have p0762 :=
    @g_syl syntaxFormula0045 syntaxFormula0034 (.classEq (.cv y) (.cv x)) p0739 p0453
  have p0763 := @g_simpr syntaxFormula0034 (.classEq (.cv z) (.cv x))
  have p0764 := @g_breq12d syntaxFormula0045 (.cv y) (.cv x) (.cv z) (.cv x) R p0762 p0763
  have p0765 :=
    @g_mpbird syntaxFormula0045 (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv x) R (.cv x))
      p0759 p0764
  have p0778 := @g_wppweref E S
  have p0779 :=
    @g_syl syntaxFormula0002 (syn_wbr S (syn_cwe) E) (syn_wbr S (syn_cref) E) p0532 p0778
  have p0785 := @g_refd syntaxFormula0002 E S (.cv u) p0779 p0192
  have p0786 :=
    @g_syl syntaxFormula0045 syntaxFormula0002 (syn_wbr (.cv u) S (.cv u)) p0745 p0785
  have p0790 :=
    @g_fveq2d syntaxFormula0045 (.cv y) (.cv x)
      (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) p0762
  have p0819 := @g_syl syntaxFormula0045 syntaxFormula0002 syntaxFormula0031 p0745 p0290
  have p0820 :=
    @g_eqtrd syntaxFormula0045
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0790
      p0819
  have p0822 :=
    @g_fveq2d syntaxFormula0045 (.cv z) (.cv x)
      (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) p0763
  have p0852 :=
    @g_eqtrd syntaxFormula0045
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z))
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0822
      p0819
  have p0853 :=
    @g_breq12d syntaxFormula0045
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv y)) (.cv u)
      (syn_cfv (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (.cv z)) (.cv u) S p0820
      p0852
  have p0854 :=
    @g_mpbird syntaxFormula0045 syntaxFormula0022 (syn_wbr (.cv u) S (.cv u)) p0786 p0853
  have p0855 :=
    @g_n_2thd syntaxFormula0045 (syn_wbr (.cv y) R (.cv z)) syntaxFormula0022 p0765 p0854
  have p0856 := @g_ex syntaxFormula0034 (.classEq (.cv z) (.cv x)) syntaxFormula0023 p0855
  have p0864 := @g_syl syntaxFormula0034 syntaxFormula0010 syntaxFormula0033 p0309 p0303
  have p0865 :=
    @g_mpjaod syntaxFormula0034 syntaxFormula0013 syntaxFormula0023
      (.classEq (.cv z) (.cv x)) p0738 p0856 p0864
  have p0866 := @g_ex syntaxFormula0010 (.classEq (.cv y) (.cv x)) syntaxFormula0023 p0865
  have p0868 := @g_simpr syntaxFormula0002 syntaxFormula0007
  have p0869 := @g_syl syntaxFormula0010 syntaxFormula0008 syntaxFormula0007 p0010 p0868
  have p0870 :=
    @g_elun (.cv y)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_csn (.cv x))
  have p0871 := @g_elsn y (.cv x) dv_cache_0002
  have p0872 :=
    @g_orbi2i (.classMem (.cv y) (syn_csn (.cv x))) (.classEq (.cv y) (.cv x))
      syntaxFormula0011 p0871
  have p0873 :=
    @g_bitri syntaxFormula0007
      (syn_wo syntaxFormula0011 (.classMem (.cv y) (syn_csn (.cv x))))
      (syn_wo syntaxFormula0011 (.classEq (.cv y) (.cv x))) p0870 p0872
  have p0874 :=
    @g_sylib syntaxFormula0010 syntaxFormula0007
      (syn_wo syntaxFormula0011 (.classEq (.cv y) (.cv x))) p0869 p0873
  have p0875 :=
    @g_mpjaod syntaxFormula0010 syntaxFormula0011 syntaxFormula0023
      (.classEq (.cv y) (.cv x)) p0306 p0866 p0874
  have p0876 :=
    @g_ralrimiva syntaxFormula0008 syntaxFormula0023 z syntaxClass0004 dv_cache_0003 p0875
  have p0877 :=
    @g_ralrimiva syntaxFormula0002 syntaxFormula0046 y syntaxClass0004 dv_cache_0004 p0876
  have p0878 := @g_jca syntaxFormula0002 syntaxFormula0006 syntaxFormula0047 p0006 p0877
  have p0879 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso y z
      syntaxClass0004 syntaxClass0005 R S (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u))))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0880 :=
    @g_sylibr syntaxFormula0002 (syn_wa syntaxFormula0006 syntaxFormula0047)
      (syn_wiso (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) R S syntaxClass0004
        syntaxClass0005)
      p0878 p0879
  exact p0880


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wedifleastssndv (x : Var) (y : Var) (C : Class) (D : Class)
    (R : Class) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (_dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_wedifleastssndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wedifleastssndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wrex x D (.neg (.classMem (.cv x) C))) (syn_wrex y D
          (syn_wa (.neg (.classMem (.cv y) C))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0004 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.neg (.classMem (.cv y) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wrex x D (.neg (.classMem (.cv x) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_y, (Ne.symm dv_x_y), dv_C_y, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wrex x D (.neg (.classMem (.cv x) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_x, fresh_z_not_C, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.neg (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.neg (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.neg (.classMem (.cv z) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0016 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0017 :
    z ∉ ((Wff.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_C, fresh_z_ne_y, fresh_z_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cdif D C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          Finset.mem_union, fresh_w_not_D, fresh_w_not_C, or_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((syn_cima R (syn_csn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_R, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0020 :
    w ∉
      ((syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_D, fresh_w_ne_z,
          fresh_w_not_C, fresh_w_ne_y, fresh_w_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_notab (.classMem (.cv x) C) x
  have p0001 := @g_abid2 x C dv_cache_0001
  have p0002 := @g_difeq2i (.cab x (.classMem (.cv x) C)) C (syn_cvv) p0001
  have p0003 :=
    @g_eqtri (.cab x (.neg (.classMem (.cv x) C)))
      (syn_cdif (syn_cvv) (.cab x (.classMem (.cv x) C))) (syn_cdif (syn_cvv) C) p0000
      p0002
  have p0004 := @g_vvex
  have p0005 := @g_difex (syn_cvv) C p0004 hyp_wedifleastssndv_2
  have p0006 :=
    @g_eqeltri (.cab x (.neg (.classMem (.cv x) C))) (syn_cdif (syn_cvv) C) (syn_cvv)
      p0003 p0005
  have p0007 := @g_eleq1 (.cv x) (.cv y) C
  have p0008 :=
    @g_notbid (.classEq (.cv x) (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C) p0007
  have p0009 := @g_eleq1 (.cv x) (.cv z) C
  have p0010 :=
    @g_notbid (.classEq (.cv x) (.cv z)) (.classMem (.cv x) C) (.classMem (.cv z) C) p0009
  have p0011 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wrex x D (.neg (.classMem (.cv x) C)))
      hyp_wedifleastssndv_1
  have p0012 := @g_id (syn_wrex x D (.neg (.classMem (.cv x) C)))
  have p0013_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv y) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0013_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (syn_wb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0013 :=
    @g_weds (syn_wrex x D (.neg (.classMem (.cv x) C))) (.neg (.classMem (.cv x) C))
      (.neg (.classMem (.cv y) C)) (.neg (.classMem (.cv z) C)) x y z D R dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0006 p0013_e01_recanon p0013_e02_recanon p0011 p0012
  have p0014 :=
    @g_simpl (.neg (.classMem (.cv y) C))
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
  have p0015 :=
    @g_simpr (.neg (.classMem (.cv y) C))
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
  have p0016 :=
    @g_simpr
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (syn_cdif D C))
  have p0017 := @g_eldif (.cv w) D C
  have p0018 :=
    @g_sylib
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (.classMem (.cv w) (syn_cdif D C))
      (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) p0016 p0017
  have p0019 := @g_simpr (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C)))
      (.neg (.classMem (.cv w) C)) p0018 p0019
  have p0024 := @g_simpl (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) (.classMem (.cv w) D)
      p0018 p0024
  have p0026 :=
    @g_simpl
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (syn_cdif D C))
  have p0027 :=
    @g_jca
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (.classMem (.cv w) D)
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) p0025
      p0026
  have p0028 := @g_eleq1 (.cv z) (.cv w) C
  have p0029 :=
    @g_notbid (.classEq (.cv z) (.cv w)) (.classMem (.cv z) C) (.classMem (.cv w) C) p0028
  have p0030 := @g_breq2 (.cv z) (.cv w) (.cv y) R
  have p0031 :=
    @g_imbi12d (.classEq (.cv z) (.cv w)) (.neg (.classMem (.cv z) C))
      (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv y) R (.cv w))
      p0029 p0030
  have p0032 :=
    @g_rspcva (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))
      (.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w))) z (.cv w) D
      dv_cache_0016 dv_cache_0004 dv_cache_0017 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (syn_wa (.classMem (.cv w) D)
        (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))))
      (.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w))) p0027 p0032
  have p0034 :=
    @g_mpd
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w)) p0020 p0033
  have p0035 := @g_elimasn R (.cv y) (.cv w)
  have p0036 := (Nominal.biimpRefl (syn_wbr (.cv y) R (.cv w)))
  have p0037 :=
    @g_bitr4i (.classMem (.cv w) (syn_cima R (syn_csn (.cv y))))
      (.classMem (syn_cop (.cv y) (.cv w)) R) (syn_wbr (.cv y) R (.cv w)) p0035 p0036
  have p0038 :=
    @g_sylibr
      (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (syn_cdif D C)))
      (syn_wbr (.cv y) R (.cv w)) (.classMem (.cv w) (syn_cima R (syn_csn (.cv y)))) p0034
      p0037
  have p0039 :=
    @g_ex (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (syn_cdif D C))
      (.classMem (.cv w) (syn_cima R (syn_csn (.cv y)))) p0038
  have p0040 :=
    @g_ssrdv
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) w
      (syn_cdif D C) (syn_cima R (syn_csn (.cv y))) dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0039
  have p0041 :=
    @g_syl
      (syn_wa (.neg (.classMem (.cv y) C))
        (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))))
      (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y)))) p0015 p0040
  have p0042 :=
    @g_jca
      (syn_wa (.neg (.classMem (.cv y) C))
        (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))))
      (.neg (.classMem (.cv y) C)) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y))))
      p0014 p0041
  have p0043 :=
    @g_reximi
      (syn_wa (.neg (.classMem (.cv y) C))
        (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))))
      (syn_wa (.neg (.classMem (.cv y) C))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y)))))
      y D p0042
  have p0044 :=
    @g_syl (syn_wrex x D (.neg (.classMem (.cv x) C)))
      (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) C))
          (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))))
      (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) C))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y))))))
      p0013 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_weincsegsscutndv (x : Var) (y : Var) (D : Class) (R : Class)
    (_dv_x_y : x ≠ y) (hyp_weincsegsscutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wss (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    z ∉
      ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
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
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
              (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_D, fresh_z_ne_y, fresh_z_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv z) (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv z) (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
  have p0003 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0002
      p0003
  have p0005 := @g_strictsegdifinindv x D R
  have p0006 :=
    @g_uneq1i (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
      (syn_csn (.cv x)) p0005
  have p0007 :=
    @g_a1i
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_cun
          (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
          (syn_csn (.cv x))))
      (.classMem (.cv x) D) p0006
  have p0008 := @g_id (.classMem (.cv x) D)
  have p0009 := @g_wppweref D R
  have p0010 := Nominal.mp hyp_weincsegsscutndv_1 p0009
  have p0011 := @g_a1i (syn_wbr R (syn_cref) D) (.classMem (.cv x) D) p0010
  have p0013 := @g_refd (.classMem (.cv x) D) D R (.cv x) p0011 p0008
  have p0014 := @g_eliniseg R (.cv x) (.cv x)
  have p0015 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv x))
      (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0013 p0014
  have p0016 :=
    @g_jca (.classMem (.cv x) D) (.classMem (.cv x) D)
      (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0008 p0015
  have p0017 := @g_elin (.cv x) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0018 :=
    @g_sylibr (.classMem (.cv x) D)
      (syn_wa (.classMem (.cv x) D)
        (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0016
      p0017
  have p0019 :=
    @g_nnsucelrlem4 (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0020 :=
    @g_syl (.classMem (.cv x) D)
      (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classEq (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
            (syn_csn (.cv x))) (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      p0018 p0019
  have p0021 :=
    @g_eqtrd (.classMem (.cv x) D)
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      (syn_cun
        (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))
        (syn_csn (.cv x)))
      (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0007 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv x) D)
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      p0004 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      p0001 p0022
  have p0024 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (.cv z)
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0000 p0023
  have p0025 := @g_elin (.cv z) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0026 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      p0024 p0025
  have p0027 :=
    @g_simpl (.classMem (.cv z) D)
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classMem (.cv z) D) p0026 p0027
  have p0029 := @g_wppwepo D R
  have p0030 := Nominal.mp hyp_weincsegsscutndv_1 p0029
  have p0031 := @g_porta D R
  have p0032 :=
    @g_simp2bi (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cref) D)
      (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0031
  have p0033 := Nominal.mp p0030 p0032
  have p0034 :=
    @g_a1i (syn_wbr R (syn_ctrans) D)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0033
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv x) D) p0001 p0004
  have p0071 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0002
      p0071
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv y) D) p0001 p0072
  have p0101 :=
    @g_simpr (.classMem (.cv z) D)
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0102 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0026 p0101
  have p0103 := @g_eliniseg R (.cv x) (.cv z)
  have p0104 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_wbr (.cv z) R (.cv x)) p0102 p0103
  have p0106 := @g_wppweconnex D R
  have p0107 := Nominal.mp hyp_weincsegsscutndv_1 p0106
  have p0108 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      p0107
  have p0115 :=
    @g_connexd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      D R (.cv x) (.cv y) p0108 p0004 p0072
  have p0116 := @g_id (syn_wbr (.cv x) R (.cv y))
  have p0117 :=
    @g_a1i (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      p0116
  have p0118 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
  have p0140 :=
    @g_neleqtrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (.cv y) p0118 p0022
  have p0141 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x))
  have p0145 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv y) D) p0141 p0072
  have p0146 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x))
  have p0147 := @g_eliniseg R (.cv x) (.cv y)
  have p0148 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0146 p0147
  have p0149 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      p0145 p0148
  have p0150 := @g_elin (.cv y) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0151 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))
      (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0149
      p0150
  have p0152 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0151
  have p0153 :=
    @g_con3d
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0152
  have p0154 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))))
      (.neg (syn_wbr (.cv y) R (.cv x))) p0140 p0153
  have p0155 :=
    @g_pm2_21d
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv x) R (.cv y)) p0154
  have p0156 :=
    @g_jaod
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))
      p0117 p0155
  have p0157 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv x) R (.cv y)) p0115 p0156
  have p0158 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wbr (.cv x) R (.cv y)) p0001 p0157
  have p0159 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      D R (.cv z) (.cv x) (.cv y) p0034 p0028 p0068 p0073 p0104 p0158
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0001 p0118
  have p0164 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0000 p0163
  have p0165 :=
    @g_nelne2 (.cv z) (.cv y)
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
  have p0166 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))) (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wne (.cv z) (.cv y)) p0164 p0165
  have p0167 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y)) p0159 p0166
  have p0168 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y)))
      p0028 p0167
  have p0169 := @g_elstrictseg y z D R
  have p0170 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0168 p0169
  have p0171 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.classMem (.cv z) (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0170
  have p0172 :=
    @g_ssrdv
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      z
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0171
  exact p0172


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wedownexactcutndv (x : Var) (C : Class) (D : Class) (R : Class)
    (hyp_wedownexactcutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classEq C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
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
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0001 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))))
      (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0004 := @g_elstrictseg x y D R
  have p0005 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0003 p0004
  have p0006 :=
    @g_simprr (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (syn_wne (.cv y) (.cv x)) p0005 p0006
  have p0008 := @g_wppweantisym D R
  have p0009 := Nominal.mp hyp_wedownexactcutndv_1 p0008
  have p0010 :=
    @g_a1i (syn_wbr R (syn_cantisym) D)
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) C))
  have p0015 :=
    @g_simpl (.classMem (.cv y) D)
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y) D) p0005 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y) D) p0011 p0016
  have p0019 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0020 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))))
      (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))))
      p0019 p0020
  have p0022 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
      (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) p0021 p0022
  have p0024 := @g_simpl (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) D)
      p0023 p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv x) D) p0011 p0025
  have p0031 :=
    @g_simprl (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (syn_wbr (.cv y) R (.cv x)) p0005 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv y) R (.cv x)) p0011 p0032
  have p0038 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
      (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))))
      (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))) p0021 p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))) p0011 p0039
  have p0048 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) C))
  have p0049 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) D) (.neg (.classMem (.cv y) C)) p0017 p0048
  have p0050 := @g_eldif (.cv y) D C
  have p0051 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) (syn_cdif D C)) p0049 p0050
  have p0052 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (syn_cdif D C) (syn_cima R (syn_csn (.cv x))) (.cv y) p0040 p0051
  have p0053 := @g_elimasn R (.cv x) (.cv y)
  have p0054 := (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y)))
  have p0055 :=
    @g_bitr4i (.classMem (.cv y) (syn_cima R (syn_csn (.cv x))))
      (.classMem (syn_cop (.cv x) (.cv y)) R) (syn_wbr (.cv x) R (.cv y)) p0053 p0054
  have p0056 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) (syn_cima R (syn_csn (.cv x)))) (syn_wbr (.cv x) R (.cv y)) p0052
      p0055
  have p0057 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      D R (.cv y) (.cv x) p0010 p0017 p0026 p0033 p0056
  have p0058 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) C)) (.classEq (.cv y) (.cv x)) p0057
  have p0059 :=
    @g_necon3ad
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classMem (.cv y) C)) (.cv y) (.cv x) p0058
  have p0060 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wne (.cv y) (.cv x)) (.neg (.neg (.classMem (.cv y) C))) p0007 p0059
  have p0061 :=
    @g_notnotrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y) C) p0060
  have p0062 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv y) C) p0061
  have p0063 :=
    @g_ssrdv
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      y (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) C
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0062
  have p0064 :=
    @g_eqssd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0002
      p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
