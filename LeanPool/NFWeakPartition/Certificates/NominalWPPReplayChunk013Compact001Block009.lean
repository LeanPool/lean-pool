/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem3`. -/
@[expose]
noncomputable def gEnprmaplem3 (x : Var) (y : Var) (A : Class) (B : Class) (W : Class)
    (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x)
    (hyp_enprmaplem3_1 : Nominal.NPrf (.classEq W (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x)))))) :
    Nominal.NPrf
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWfun (synCcnv W))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪
      ({ r } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p := Ne.symm fresh_p_ne_r
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_W : q ∉ W.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_q : r ≠ q := Ne.symm fresh_q_ne_r
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_w : p ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_p : w ≠ p := Ne.symm fresh_p_ne_w
  have fresh_q_ne_w : q ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_q : w ≠ q := Ne.symm fresh_q_ne_w
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0002 : r ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_r, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_p, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synCima (synCcnv (.cv p)) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_p, dv_r_x, or_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((synCo A (synCmap) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, dv_A_r,
          dv_B_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_q, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((synCima (synCcnv (.cv q)) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_q, dv_r_x, or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_q, not_false_eq_true])
  have dv_cache_0010 :
    w ∉
      ((synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_q, fresh_w_ne_y,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    w ∉
      ((synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
            (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
              (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
                (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
          (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, fresh_w_not_B,
          fresh_w_ne_p, fresh_w_ne_q, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv p)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_q, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B,
          fresh_z_ne_p, fresh_z_ne_q, or_false, not_false_eq_true])
  have dv_cache_0016 :
    q ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0017 :
    z ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0018 :
    p ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_W,
          not_false_eq_true])
  have dv_cache_0020 : p ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_p_not_W,
          not_false_eq_true])
  have dv_cache_0021 : q ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_q_not_W,
          not_false_eq_true])
  have dv_cache_0022 : z ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show z ≠ p from (by exact fresh_z_ne_p))
  have dv_cache_0023 : z ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show z ≠ q from (by exact fresh_z_ne_q))
  have dv_cache_0024 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 := @gBrcnv (.cv z) (.cv p) W
  have p0001 := @gBrcnv (.cv z) (.cv q) W
  have p0002 := @gBreldm (.cv p) (.cv z) W
  have p0003 := @gEnprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem3_1
  have p0004 := @gFndm (synCo A (synCmap) B) W
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gSyl6eleq (synWbr (.cv p) W (.cv z)) (.cv p) (synCdm W) (synCo A (synCmap) B)
      p0002 p0005
  have p0007 := @gFnfun (synCo A (synCmap) B) W
  have p0008 := Nominal.mp p0003 p0007
  have p0009 := @gFunbrfv (.cv p) (.cv z) W
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gCnveq (.cv r) (.cv p)
  have p0012_e00_recanon :
    Nominal.NPrf (.imp (.objEq r p) (.classEq (synCcnv (.cv r)) (synCcnv (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCcnv synCopab synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gImaeq1d (.objEq r p) (synCcnv (.cv r)) (synCcnv (.cv p)) (synCsn (.cv x))
      p0012_e00_recanon
  have p0013 := @gVex p
  have p0014 := @gCnvex (.cv p) p0013
  have p0015 := @gSnex (.cv x)
  have p0016 := @gImaex (synCcnv (.cv p)) (synCsn (.cv x)) p0014 p0015
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv p)) (.classEq (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv p)) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCima synWrex synWex synWa synWbr synCop synCun synCnin synWnan
          synCcompl synCcnv synCopab synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0017 :=
    @gFvmpt r (.cv p) (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
      (synCima (synCcnv (.cv p)) (synCsn (.cv x))) (synCo A (synCmap) B) W
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0017_e00_recanon hyp_enprmaplem3_1 p0016
  have p0018 :=
    @gSyl (synWbr (.cv p) W (.cv z)) (.classMem (.cv p) (synCo A (synCmap) B))
      (.classEq (synCfv W (.cv p)) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))) p0006
      p0017
  have p0019 :=
    @gEqtr3d (synWbr (.cv p) W (.cv z)) (synCfv W (.cv p)) (.cv z)
      (synCima (synCcnv (.cv p)) (synCsn (.cv x))) p0010 p0018
  have p0020 :=
    @gJca (synWbr (.cv p) W (.cv z)) (.classMem (.cv p) (synCo A (synCmap) B))
      (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))) p0006 p0019
  have p0021 := @gBreldm (.cv q) (.cv z) W
  have p0022 :=
    @gSyl6eleq (synWbr (.cv q) W (.cv z)) (.cv q) (synCdm W) (synCo A (synCmap) B)
      p0021 p0005
  have p0023 := @gFunbrfv (.cv q) (.cv z) W
  have p0024 := Nominal.mp p0008 p0023
  have p0025 := @gCnveq (.cv r) (.cv q)
  have p0026_e00_recanon :
    Nominal.NPrf (.imp (.objEq r q) (.classEq (synCcnv (.cv r)) (synCcnv (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCcnv synCopab synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @gImaeq1d (.objEq r q) (synCcnv (.cv r)) (synCcnv (.cv q)) (synCsn (.cv x))
      p0026_e00_recanon
  have p0027 := @gVex q
  have p0028 := @gCnvex (.cv q) p0027
  have p0029 := @gImaex (synCcnv (.cv q)) (synCsn (.cv x)) p0028 p0015
  have p0030_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv q)) (.classEq (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv q)) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCima synWrex synWex synWa synWbr synCop synCun synCnin synWnan
          synCcompl synCcnv synCopab synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0030 :=
    @gFvmpt r (.cv q) (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
      (synCima (synCcnv (.cv q)) (synCsn (.cv x))) (synCo A (synCmap) B) W
      dv_cache_0006 dv_cache_0007 dv_cache_0005 p0030_e00_recanon hyp_enprmaplem3_1 p0029
  have p0031 :=
    @gSyl (synWbr (.cv q) W (.cv z)) (.classMem (.cv q) (synCo A (synCmap) B))
      (.classEq (synCfv W (.cv q)) (synCima (synCcnv (.cv q)) (synCsn (.cv x)))) p0022
      p0030
  have p0032 :=
    @gEqtr3d (synWbr (.cv q) W (.cv z)) (synCfv W (.cv q)) (.cv z)
      (synCima (synCcnv (.cv q)) (synCsn (.cv x))) p0024 p0031
  have p0033 :=
    @gJca (synWbr (.cv q) W (.cv z)) (.classMem (.cv q) (synCo A (synCmap) B))
      (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x)))) p0022 p0032
  have p0034 :=
    @gAnim12i (synWbr (.cv p) W (.cv z))
      (synWa (.classMem (.cv p) (synCo A (synCmap) B))
        (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))))
      (synWbr (.cv q) W (.cv z))
      (synWa (.classMem (.cv q) (synCo A (synCmap) B))
        (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      p0020 p0033
  have p0035 :=
    @gSyl2anb (synWbr (.cv z) (synCcnv W) (.cv p)) (synWbr (.cv p) W (.cv z))
      (synWbr (.cv q) W (.cv z))
      (synWa (synWa (.classMem (.cv p) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))))
        (synWa (.classMem (.cv q) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWbr (.cv z) (synCcnv W) (.cv q)) p0000 p0001 p0034
  have p0036 := @gElmapi (.cv p) A B
  have p0037 := @gElmapi (.cv q) A B
  have p0038 :=
    @gAnim12i (.classMem (.cv p) (synCo A (synCmap) B)) (synWf (.cv p) B A)
      (.classMem (.cv q) (synCo A (synCmap) B)) (synWf (.cv q) B A) p0036 p0037
  have p0039 :=
    @gEqtr2 (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
      (synCima (synCcnv (.cv q)) (synCsn (.cv x)))
  have p0040 :=
    @gSimprll (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWf (.cv p) B A) (synWf (.cv q) B A)
      (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
        (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
  have p0041 := @gFfn B A (.cv p)
  have p0042 :=
    @gSyl
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWf (.cv p) B A) (synWfn (.cv p) B) p0040 p0041
  have p0043 :=
    @gSimprlr (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWf (.cv p) B A) (synWf (.cv q) B A)
      (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
        (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
  have p0044 := @gFfn B A (.cv q)
  have p0045 :=
    @gSyl
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWf (.cv q) B A) (synWfn (.cv q) B) p0043 p0044
  have p0046 := @gFfvelrn B A (.cv z) (.cv p)
  have p0047 :=
    @gSylan
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWf (.cv p) B A) (.classMem (.cv z) B) (.classMem (synCfv (.cv p) (.cv z)) A)
      p0040 p0046
  have p0048 :=
    @gSimpllr (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
        (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      (.classMem (.cv z) B)
  have p0049 :=
    @gEleq2d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      A (synCpr (.cv x) (.cv y)) (synCfv (.cv p) (.cv z)) p0048
  have p0050 := @gFvex (.cv z) (.cv p)
  have p0051 := @gElpr (synCfv (.cv p) (.cv z)) (.cv x) (.cv y) p0050
  have p0052 :=
    @gSyl6bb
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (synCfv (.cv p) (.cv z)) A)
      (.classMem (synCfv (.cv p) (.cv z)) (synCpr (.cv x) (.cv y)))
      (synWo (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
        (.classEq (synCfv (.cv p) (.cv z)) (.cv y)))
      p0049 p0051
  have p0053 :=
    @gSimprr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
  have p0054 :=
    @gSimplrr (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
      (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
        (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
      (.classMem (.cv z) B)
  have p0055 :=
    @gEleq2d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
      (synCima (synCcnv (.cv q)) (synCsn (.cv x))) (.cv z) p0054
  have p0056 := @gEliniseg (.cv p) (.cv x) (.cv z)
  have p0057 := @gEliniseg (.cv q) (.cv x) (.cv z)
  have p0058 :=
    @gN3bitr3g
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x))))
      (.classMem (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
      (synWbr (.cv z) (.cv p) (.cv x)) (synWbr (.cv z) (.cv q) (.cv x)) p0055 p0056
      p0057
  have p0059 :=
    @gBiimpd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv x)) (synWbr (.cv z) (.cv q) (.cv x)) p0058
  have p0060 := @gFnbrfvb B (.cv z) (.cv x) (.cv p)
  have p0061 :=
    @gSylan
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWfn (.cv p) B) (.classMem (.cv z) B)
      (synWb (.classEq (synCfv (.cv p) (.cv z)) (.cv x)) (synWbr (.cv z) (.cv p) (.cv x)))
      p0042 p0060
  have p0062 := @gFnbrfvb B (.cv z) (.cv x) (.cv q)
  have p0063 :=
    @gSylan
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWfn (.cv q) B) (.classMem (.cv z) B)
      (synWb (.classEq (synCfv (.cv q) (.cv z)) (.cv x)) (synWbr (.cv z) (.cv q) (.cv x)))
      p0045 p0062
  have p0064 :=
    @gN3imtr4d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv x)) (synWbr (.cv z) (.cv q) (.cv x))
      (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
      (.classEq (synCfv (.cv q) (.cv z)) (.cv x)) p0059 p0061 p0063
  have p0065 :=
    @gImpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
      (.classEq (synCfv (.cv q) (.cv z)) (.cv x)) p0064
  have p0066 :=
    @gEqtr4d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv x))))
      (synCfv (.cv p) (.cv z)) (.cv x) (synCfv (.cv q) (.cv z)) p0053 p0065
  have p0067 :=
    @gExpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
      (.classEq (synCfv (.cv p) (.cv z)) (synCfv (.cv q) (.cv z))) p0066
  have p0068 :=
    @gSimprr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv y))
  have p0069 :=
    @gSimplll (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
        (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y)))
  have p0070 :=
    @gNeneqd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.cv x) (.cv y) p0069
  have p0071 :=
    @gAdantr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWf (.cv p) B A) (.classMem (.cv z) B) p0040
  have p0072 := @gFfun B A (.cv p)
  have p0073 := @gFununiq (.cv z) (.cv x) (.cv y) (.cv p)
  have p0074_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun (.cv p)) (synWbr (.cv z) (.cv p) (.cv x))
          (synWbr (.cv z) (.cv p) (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWfun synWss synCin synCcompl synCnin synWnan
          synCcom synCopab synWex synCcnv synCid synWbr synCop synCun synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0073
  have p0074 :=
    @gN3expib (synWfun (.cv p)) (synWbr (.cv z) (.cv p) (.cv x))
      (synWbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074_e00_recanon
  have p0075 :=
    @gAncomsd (synWfun (.cv p)) (synWbr (.cv z) (.cv p) (.cv x))
      (synWbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074
  have p0076 :=
    @gN3syl
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWf (.cv p) B A) (synWfun (.cv p))
      (.imp (synWa (synWbr (.cv z) (.cv p) (.cv y)) (synWbr (.cv z) (.cv p) (.cv x)))
        (.objEq x y))
      p0071 p0072 p0075
  have p0077 :=
    @gExp3a
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv y)) (synWbr (.cv z) (.cv p) (.cv x)) (.objEq x y)
      p0076
  have p0078 :=
    @gImpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))
      (.imp (synWbr (.cv z) (.cv p) (.cv x)) (.objEq x y)) p0077
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa
            (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
            (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
              (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
                (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
          (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
        (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0070
  have p0079 :=
    @gMtod
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWbr (.cv z) (.cv p) (.cv x)) (.objEq x y) p0079_e00_recanon p0078
  have p0080 :=
    @gExpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))
      (.neg (synWbr (.cv z) (.cv p) (.cv x))) p0079
  have p0081 :=
    @gBiimprd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv x)) (synWbr (.cv z) (.cv q) (.cv x)) p0058
  have p0082 :=
    @gNsyld
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv y)) (synWbr (.cv z) (.cv p) (.cv x))
      (synWbr (.cv z) (.cv q) (.cv x)) p0080 p0081
  have p0083 :=
    @gImpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))
      (.neg (synWbr (.cv z) (.cv q) (.cv x))) p0082
  have p0084 :=
    @gSimprl
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))
  have p0085 :=
    @gAdantr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWf (.cv q) B A)
      (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))) p0043
  have p0086 := @gFdm B A (.cv q)
  have p0087 :=
    @gSyl
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWf (.cv q) B A) (.classEq (synCdm (.cv q)) B) p0085 p0086
  have p0088 :=
    @gEleqtrrd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.cv z) B (synCdm (.cv q)) p0084 p0087
  have p0089 := @gEldm w (.cv z) (.cv q) dv_cache_0008 dv_cache_0009
  have p0090 := @gBrelrn (.cv z) (.cv w) (.cv q)
  have p0091 := @gFrn B A (.cv q)
  have p0092 :=
    @gSyl
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWf (.cv q) B A) (synWss (synCrn (.cv q)) A) p0085 p0091
  have p0093 :=
    @gSseld
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synCrn (.cv q)) A (.cv w) p0092
  have p0094 :=
    @gSyl5 (synWbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) (synCrn (.cv q)))
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) p0090 p0093
  have p0095 :=
    @gSimpllr (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
        (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y)))
  have p0096 :=
    @gEleq2d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      A (synCpr (.cv x) (.cv y)) (.cv w) p0095
  have p0097 := @gVex w
  have p0098 := @gElpr (.cv w) (.cv x) (.cv y) p0097
  have p0099 := @gBreq2 (.cv w) (.cv x) (.cv z) (.cv q)
  have p0100_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x)
        (synWb (synWbr (.cv z) (.cv q) (.cv w)) (synWbr (.cv z) (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @gBiimpcd (.objEq w x) (synWbr (.cv z) (.cv q) (.cv w))
      (synWbr (.cv z) (.cv q) (.cv x)) p0100_e00_recanon
  have p0101 := @gBreq2 (.cv w) (.cv y) (.cv z) (.cv q)
  have p0102_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y)
        (synWb (synWbr (.cv z) (.cv q) (.cv w)) (synWbr (.cv z) (.cv q) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0101
  have p0102 :=
    @gBiimpcd (.objEq w y) (synWbr (.cv z) (.cv q) (.cv w))
      (synWbr (.cv z) (.cv q) (.cv y)) p0102_e00_recanon
  have p0103 :=
    @gOrim12d (synWbr (.cv z) (.cv q) (.cv w)) (.objEq w x)
      (synWbr (.cv z) (.cv q) (.cv x)) (.objEq w y) (synWbr (.cv z) (.cv q) (.cv y))
      p0100 p0102
  have p0104 :=
    @gCom12 (synWbr (.cv z) (.cv q) (.cv w)) (synWo (.objEq w x) (.objEq w y))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) p0103
  have p0105_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w) (synCpr (.cv x) (.cv y)))
        (synWo (.objEq w x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpr synCun synCnin synWnan synWa synCcompl synCsn synWo
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0098
  have p0105 :=
    @gSylbi (.classMem (.cv w) (synCpr (.cv x) (.cv y)))
      (synWo (.objEq w x) (.objEq w y))
      (.imp (synWbr (.cv z) (.cv q) (.cv w))
        (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))))
      p0105_e00_recanon p0104
  have p0106 :=
    @gSyl6bi
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) (.classMem (.cv w) (synCpr (.cv x) (.cv y)))
      (.imp (synWbr (.cv z) (.cv q) (.cv w))
        (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))))
      p0096 p0105
  have p0107 :=
    @gCom23
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) (synWbr (.cv z) (.cv q) (.cv w))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) p0106
  have p0108 :=
    @gMpdd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) A)
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) p0094
      p0107
  have p0109 :=
    @gExlimdv
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWbr (.cv z) (.cv q) (.cv w))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) w
      dv_cache_0010 dv_cache_0011 p0108
  have p0110 :=
    @gSyl5bi (.classMem (.cv z) (synCdm (.cv q)))
      (synWex w (synWbr (.cv z) (.cv q) (.cv w)))
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) p0089
      p0109
  have p0111 :=
    @gMpd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv z) (synCdm (.cv q)))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))) p0088
      p0110
  have p0112 :=
    @gOrel1 (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y))
  have p0113 :=
    @gSylc
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))))
      (.neg (synWbr (.cv z) (.cv q) (.cv x)))
      (synWo (synWbr (.cv z) (.cv q) (.cv x)) (synWbr (.cv z) (.cv q) (.cv y)))
      (synWbr (.cv z) (.cv q) (.cv y)) p0083 p0111 p0112
  have p0114 :=
    @gExpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (synWbr (.cv z) (.cv p) (.cv y))
      (synWbr (.cv z) (.cv q) (.cv y)) p0113
  have p0115 := @gFnbrfvb B (.cv z) (.cv y) (.cv p)
  have p0116 :=
    @gSylan
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWfn (.cv p) B) (.classMem (.cv z) B)
      (synWb (.classEq (synCfv (.cv p) (.cv z)) (.cv y)) (synWbr (.cv z) (.cv p) (.cv y)))
      p0042 p0115
  have p0117 := @gFnbrfvb B (.cv z) (.cv y) (.cv q)
  have p0118 :=
    @gSylan
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWfn (.cv q) B) (.classMem (.cv z) B)
      (synWb (.classEq (synCfv (.cv q) (.cv z)) (.cv y)) (synWbr (.cv z) (.cv q) (.cv y)))
      p0045 p0117
  have p0119 :=
    @gN3imtr4d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (synWbr (.cv z) (.cv p) (.cv y)) (synWbr (.cv z) (.cv q) (.cv y))
      (.classEq (synCfv (.cv p) (.cv z)) (.cv y))
      (.classEq (synCfv (.cv q) (.cv z)) (.cv y)) p0114 p0116 p0118
  have p0120 :=
    @gImpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv y))
      (.classEq (synCfv (.cv q) (.cv z)) (.cv y)) p0119
  have p0121 :=
    @gEqtr4d
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
        (synWa (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv y))))
      (synCfv (.cv p) (.cv z)) (.cv y) (synCfv (.cv q) (.cv z)) p0068 p0120
  have p0122 :=
    @gExpr
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (synCfv (.cv p) (.cv z)) (.cv y))
      (.classEq (synCfv (.cv p) (.cv z)) (synCfv (.cv q) (.cv z))) p0121
  have p0123 :=
    @gJaod
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
      (.classEq (synCfv (.cv p) (.cv z)) (synCfv (.cv q) (.cv z)))
      (.classEq (synCfv (.cv p) (.cv z)) (.cv y)) p0067 p0122
  have p0124 :=
    @gSylbid
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (synCfv (.cv p) (.cv z)) A)
      (synWo (.classEq (synCfv (.cv p) (.cv z)) (.cv x))
        (.classEq (synCfv (.cv p) (.cv z)) (.cv y)))
      (.classEq (synCfv (.cv p) (.cv z)) (synCfv (.cv q) (.cv z))) p0052 p0123
  have p0125 :=
    @gMpd
      (synWa (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (synCfv (.cv p) (.cv z)) A)
      (.classEq (synCfv (.cv p) (.cv z)) (synCfv (.cv q) (.cv z))) p0047 p0124
  have p0126 :=
    @gEqfnfvd
      (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
          (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
            (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      z B (.cv p) (.cv q) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0042
      p0045 p0125
  have p0127_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
          (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
            (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
              (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))) (.objEq p q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0126
  have p0127 :=
    @gExpcom (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWa (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
        (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      (.objEq p q) p0127_e00_recanon
  have p0128 :=
    @gSyl2an
      (synWa (.classMem (.cv p) (synCo A (synCmap) B))
        (.classMem (.cv q) (synCo A (synCmap) B)))
      (synWa (synWf (.cv p) B A) (synWf (.cv q) B A))
      (.classEq (synCima (synCcnv (.cv p)) (synCsn (.cv x)))
        (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (.objEq p q))
      (synWa (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x))))
        (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x)))))
      p0038 p0039 p0127
  have p0129 :=
    @gAn4s (.classMem (.cv p) (synCo A (synCmap) B))
      (.classMem (.cv q) (synCo A (synCmap) B))
      (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x))))
      (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x))))
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (.objEq p q))
      p0128
  have p0130 :=
    @gCom12
      (synWa (synWa (.classMem (.cv p) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))))
        (synWa (.classMem (.cv q) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.objEq p q) p0129
  have p0131 :=
    @gSyl5
      (synWa (synWbr (.cv z) (synCcnv W) (.cv p)) (synWbr (.cv z) (synCcnv W) (.cv q)))
      (synWa (synWa (.classMem (.cv p) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv p)) (synCsn (.cv x)))))
        (synWa (.classMem (.cv q) (synCo A (synCmap) B))
          (.classEq (.cv z) (synCima (synCcnv (.cv q)) (synCsn (.cv x))))))
      (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.objEq p q) p0035 p0130
  have p0132 :=
    @gAlrimiv (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.imp (synWa (synWbr (.cv z) (synCcnv W) (.cv p))
          (synWbr (.cv z) (synCcnv W) (.cv q))) (.objEq p q))
      q dv_cache_0016 p0131
  have p0133 :=
    @gAlrimivv (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.all q (.imp (synWa (synWbr (.cv z) (synCcnv W) (.cv p))
            (synWbr (.cv z) (synCcnv W) (.cv q))) (.objEq p q)))
      z p dv_cache_0017 dv_cache_0018 p0132
  have p0134 :=
    @gDffun2 z p q (synCcnv W) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0135 :=
    @gSylibr (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.all z (.all p (.all q (.imp (synWa (synWbr (.cv z) (synCcnv W) (.cv p))
                (synWbr (.cv z) (synCcnv W) (.cv q))) (.objEq p q)))))
      (synWfun (synCcnv W)) p0133 p0134
  exact p0135


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem4`. -/
@[expose]
noncomputable def gEnprmaplem4 (x : Var) (y : Var) (u : Var) (B : Class) (R : Class)
    (p : Var) (dv_B_u : u ∉ B.fv) (dv_p_u : p ≠ u) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (hyp_enprmaplem4_1 :
      Nominal.NPrf (.classEq R (synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y)))))
    (hyp_enprmaplem4_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem R (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ B.fv ∪ R.fv ∪
      ({ p } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_u, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((synCcnv (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
            (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_p_u), dv_u_x, dv_u_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synCcnv (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
            (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_x, fresh_z_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0004 : z ∉ ((synCif (.objMem u p) (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_u, fresh_z_ne_p,
          or_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have p0000 :=
    @gElun (synCop (.cv u) (synCsn (.cv z))) (synCxp (.cv p) (synCpw1 (.cv x)))
      (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))
  have p0001 := @gOpelxp (.cv u) (synCsn (.cv z)) (.cv p) (synCpw1 (.cv x))
  have p0002 := @gSnelpw1 (.cv z) (.cv x)
  have p0003_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gAnbi2i (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))) (.objMem z x) (.objMem u p)
      p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv u) (synCsn (.cv z)))
          (synCxp (.cv p) (synCpw1 (.cv x))))
        (synWa (.objMem u p) (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCxp synCopab synCpw1 synCin synCpw synWss synC1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0004 :=
    @gBitri
      (.classMem (synCop (.cv u) (synCsn (.cv z))) (synCxp (.cv p) (synCpw1 (.cv x))))
      (synWa (.objMem u p) (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))))
      (synWa (.objMem u p) (.objMem z x)) p0004_e00_recanon p0003
  have p0005 :=
    @gOpelxp (.cv u) (synCsn (.cv z)) (synCcompl (.cv p)) (synCpw1 (.cv y))
  have p0006 := @gVex u
  have p0007 := @gElcompl (.cv u) (.cv p) p0006
  have p0008 := @gSnelpw1 (.cv z) (.cv y)
  have p0009_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv u) (synCcompl (.cv p))) (.neg (.objMem u p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gAnbi12i (.classMem (.cv u) (synCcompl (.cv p))) (.neg (.objMem u p))
      (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) (.objMem z y) p0009_e00_recanon
      p0009_e01_recanon
  have p0010 :=
    @gBitri
      (.classMem (synCop (.cv u) (synCsn (.cv z)))
        (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))
      (synWa (.classMem (.cv u) (synCcompl (.cv p)))
        (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))))
      (synWa (.neg (.objMem u p)) (.objMem z y)) p0005 p0009
  have p0011 :=
    @gOrbi12i
      (.classMem (synCop (.cv u) (synCsn (.cv z))) (synCxp (.cv p) (synCpw1 (.cv x))))
      (synWa (.objMem u p) (.objMem z x))
      (.classMem (synCop (.cv u) (synCsn (.cv z)))
        (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))
      (synWa (.neg (.objMem u p)) (.objMem z y)) p0004 p0010
  have p0012 :=
    @gBitri
      (.classMem (synCop (.cv u) (synCsn (.cv z)))
        (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
          (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))
      (synWo (.classMem (synCop (.cv u) (synCsn (.cv z)))
          (synCxp (.cv p) (synCpw1 (.cv x)))) (.classMem (synCop (.cv u) (synCsn (.cv z)))
          (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))
      (synWo (synWa (.objMem u p) (.objMem z x)) (synWa (.neg (.objMem u p)) (.objMem z y)))
      p0000 p0011
  have p0013 :=
    @gOpelcnv (synCsn (.cv z)) (.cv u)
      (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
        (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))
  have p0014 := @gElif (.objMem u p) (.cv z) (.cv x) (.cv y)
  have p0015_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCif (.objMem u p) (.cv x) (.cv y)))
        (synWo (synWa (.objMem u p) (.objMem z x))
          (synWa (.neg (.objMem u p)) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCif synWo synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @gN3bitr4i
      (.classMem (synCop (.cv u) (synCsn (.cv z)))
        (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
          (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))
      (synWo (synWa (.objMem u p) (.objMem z x)) (synWa (.neg (.objMem u p)) (.objMem z y)))
      (.classMem (synCop (synCsn (.cv z)) (.cv u)) (synCcnv
          (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
            (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))))
      (.classMem (.cv z) (synCif (.objMem u p) (.cv x) (.cv y))) p0012 p0013
      p0015_e02_recanon
  have p0016 :=
    @gReleqmpt u z B
      (synCcnv (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
          (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))
      (synCif (.objMem u p) (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0015
  have p0017 :=
    @gEqtr4i R (synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y)))
      (synCin (synCxp B (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCcnv
                    (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
                      (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))))) (synC1c)))))
      hyp_enprmaplem4_1 p0016
  have p0018 := @gVex p
  have p0019 := @gVex x
  have p0020 := @gPw1ex (.cv x) p0019
  have p0021 := @gXpex (.cv p) (synCpw1 (.cv x)) p0018 p0020
  have p0022 := @gComplex (.cv p) p0018
  have p0023 := @gVex y
  have p0024 := @gPw1ex (.cv y) p0023
  have p0025 := @gXpex (synCcompl (.cv p)) (synCpw1 (.cv y)) p0022 p0024
  have p0026 :=
    @gUnex (synCxp (.cv p) (synCpw1 (.cv x)))
      (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))) p0021 p0025
  have p0027 :=
    @gCnvex
      (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
        (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))
      p0026
  have p0028 :=
    @gMptexlem B
      (synCcnv (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
          (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y)))))
      hyp_enprmaplem4_2 p0027
  have p0029 :=
    @gEqeltri R
      (synCin (synCxp B (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCcnv
                    (synCun (synCxp (.cv p) (synCpw1 (.cv x)))
                      (synCxp (synCcompl (.cv p)) (synCpw1 (.cv y))))))) (synC1c)))))
      (synCvv) p0017 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem5`. -/
@[expose]
noncomputable def gEnprmaplem5 (x : Var) (y : Var) (u : Var) (A : Class) (B : Class)
    (R : Class) (W : Class) (r : Var) (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_r : r ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_B_r : r ∉ B.fv) (dv_B_u : u ∉ B.fv)
    (dv_R_r : r ∉ R.fv) (dv_W_p : p ∉ W.fv) (dv_p_u : p ≠ u) (dv_p_x : p ≠ x)
    (dv_p_y : p ≠ y) (dv_r_x : r ≠ x) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (hyp_enprmaplem5_1 : Nominal.NPrf (.classEq W (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x))))))
    (hyp_enprmaplem5_2 :
      Nominal.NPrf (.classEq R (synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y)))))
    (hyp_enprmaplem5_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWss (synCpw B) (synCrn W))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ B.fv ∪
            R.fv ∪
          W.fv ∪
        ({ r } : Finset Var) ∪
      ({ p } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
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
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ ((Wff.classEq A (synCpr (.cv x) (.cv y)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_u, dv_u_x, dv_u_y, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_u, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0004 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show p ≠ u from (by exact dv_p_u))
  have dv_cache_0005 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0006 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0007 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_r, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((synCima (synCcnv R) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_R_r, dv_r_x, or_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((synCo A (synCmap) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, dv_A_r,
          dv_B_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_z, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((synCif (.objMem z p) (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, dv_u_x, dv_u_y, fresh_u_ne_z, (Ne.symm dv_p_u), or_false,
          not_false_eq_true])
  have dv_cache_0012 : z ∉ ((synCima (synCcnv R) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv p)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_p, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y,
          fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0015 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0016 : r ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_r, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((synCpw B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, dv_B_p,
          not_false_eq_true])
  have dv_cache_0018 : p ∉ ((synCrn W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, dv_W_p,
          not_false_eq_true])
  have dv_cache_0019 :
    p ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, dv_p_x, dv_p_y, dv_A_p, or_false, not_false_eq_true])
  have p0000 := @gVex p
  have p0001 := @gElpw (.cv p) B p0000
  have p0002 := @gIfeqor (.objMem u p) (.cv x) (.cv y)
  have p0003 := @gVex x
  have p0004 := @gVex y
  have p0005 := @gIfex (.objMem u p) (.cv x) (.cv y) p0003 p0004
  have p0006 := @gElpr (synCif (.objMem u p) (.cv x) (.cv y)) (.cv x) (.cv y) p0005
  have p0007 :=
    @gMpbir (.classMem (synCif (.objMem u p) (.cv x) (.cv y)) (synCpr (.cv x) (.cv y)))
      (synWo (.classEq (synCif (.objMem u p) (.cv x) (.cv y)) (.cv x))
        (.classEq (synCif (.objMem u p) (.cv x) (.cv y)) (.cv y)))
      p0002 p0006
  have p0008 := @gId (.classEq A (synCpr (.cv x) (.cv y)))
  have p0009 :=
    @gSyl5eleqr (.classEq A (synCpr (.cv x) (.cv y)))
      (synCif (.objMem u p) (.cv x) (.cv y)) (synCpr (.cv x) (.cv y)) A p0007 p0008
  have p0010 :=
    @gRalrimivw (.classEq A (synCpr (.cv x) (.cv y)))
      (.classMem (synCif (.objMem u p) (.cv x) (.cv y)) A) u B dv_cache_0001 p0009
  have p0011 :=
    @gFmpt u B A (synCif (.objMem u p) (.cv x) (.cv y)) R dv_cache_0002 dv_cache_0003
      hyp_enprmaplem5_2
  have p0012 :=
    @gSylib (.classEq A (synCpr (.cv x) (.cv y)))
      (synWral u B (.classMem (synCif (.objMem u p) (.cv x) (.cv y)) A)) (synWf R B A)
      p0010 p0011
  have p0013 := @gPrex (.cv x) (.cv y)
  have p0014 := @gEleq1 A (synCpr (.cv x) (.cv y)) (synCvv)
  have p0015 :=
    @gMpbiri (.classEq A (synCpr (.cv x) (.cv y))) (.classMem A (synCvv))
      (.classMem (synCpr (.cv x) (.cv y)) (synCvv)) p0013 p0014
  have p0016 :=
    @gEnprmaplem4 x y u B R p dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_enprmaplem5_2 hyp_enprmaplem5_3
  have p0017 := @gElmapg A B R (synCvv) (synCvv) (synCvv)
  have p0018 :=
    @gMp3an23 (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem R (synCvv))
      (synWb (.classMem R (synCo A (synCmap) B)) (synWf R B A)) hyp_enprmaplem5_3
      p0016 p0017
  have p0019 :=
    @gSyl (.classEq A (synCpr (.cv x) (.cv y))) (.classMem A (synCvv))
      (synWb (.classMem R (synCo A (synCmap) B)) (synWf R B A)) p0015 p0018
  have p0020 :=
    @gMpbird (.classEq A (synCpr (.cv x) (.cv y))) (.classMem R (synCo A (synCmap) B))
      (synWf R B A) p0012 p0019
  have p0021 :=
    @gN3ad2ant2 (.classEq A (synCpr (.cv x) (.cv y))) (synWne (.cv x) (.cv y))
      (.classMem R (synCo A (synCmap) B)) (synWss (.cv p) B) p0020
  have p0022 := @gCnveq (.cv r) R
  have p0023 :=
    @gImaeq1d (.classEq (.cv r) R) (synCcnv (.cv r)) (synCcnv R) (synCsn (.cv x))
      p0022
  have p0024 := @gCnvex R p0016
  have p0025 := @gSnex (.cv x)
  have p0026 := @gImaex (synCcnv R) (synCsn (.cv x)) p0024 p0025
  have p0027 :=
    @gFvmpt r R (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
      (synCima (synCcnv R) (synCsn (.cv x))) (synCo A (synCmap) B) W dv_cache_0007
      dv_cache_0008 dv_cache_0009 p0023 hyp_enprmaplem5_1 p0026
  have p0028 :=
    @gSyl
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.classMem R (synCo A (synCmap) B))
      (.classEq (synCfv W R) (synCima (synCcnv R) (synCsn (.cv x)))) p0021 p0027
  have p0029 := @gEliniseg R (.cv x) (.cv z)
  have p0030 := @gBreldm (.cv z) (.cv x) R
  have p0031 :=
    @gFnmpt u B (synCif (.objMem u p) (.cv x) (.cv y)) R (synCvv) dv_cache_0002
      hyp_enprmaplem5_2
  have p0032 :=
    @gA1i (.classMem (synCif (.objMem u p) (.cv x) (.cv y)) (synCvv))
      (.classMem (.cv u) B) p0005
  have p0033 :=
    @gMprg (.classMem (synCif (.objMem u p) (.cv x) (.cv y)) (synCvv)) (synWfn R B) u
      B p0031 p0032
  have p0034 := @gFndm B R
  have p0035 := Nominal.mp p0033 p0034
  have p0036 := @gSyl6eleq (synWbr (.cv z) R (.cv x)) (.cv z) (synCdm R) B p0030 p0035
  have p0037 := @gFnbrfvb B (.cv z) (.cv x) R
  have p0038 :=
    @gMpan (synWfn R B) (.classMem (.cv z) B)
      (synWb (.classEq (synCfv R (.cv z)) (.cv x)) (synWbr (.cv z) R (.cv x))) p0033
      p0037
  have p0039 :=
    @gBiimprd (.classMem (.cv z) B) (.classEq (synCfv R (.cv z)) (.cv x))
      (synWbr (.cv z) R (.cv x)) p0038
  have p0040 :=
    @gCom12 (.classMem (.cv z) B) (synWbr (.cv z) R (.cv x))
      (.classEq (synCfv R (.cv z)) (.cv x)) p0039
  have p0041 :=
    @gJcai (synWbr (.cv z) R (.cv x)) (.classMem (.cv z) B)
      (.classEq (synCfv R (.cv z)) (.cv x)) p0036 p0040
  have p0042 := @gEleq1 (.cv u) (.cv z) (.cv p)
  have p0043_e00_recanon :
    Nominal.NPrf (.imp (.objEq u z) (synWb (.objMem u p) (.objMem z p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0042
  have p0043 :=
    @gIfbid (.objEq u z) (.objMem u p) (.objMem z p) (.cv x) (.cv y) p0043_e00_recanon
  have p0044 := @gIfex (.objMem z p) (.cv x) (.cv y) p0003 p0004
  have p0045_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv u) (.cv z)) (.classEq (synCif (.objMem u p) (.cv x) (.cv y))
          (synCif (.objMem z p) (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCif synWo synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0045 :=
    @gFvmpt u (.cv z) (synCif (.objMem u p) (.cv x) (.cv y))
      (synCif (.objMem z p) (.cv x) (.cv y)) B R dv_cache_0010 dv_cache_0011
      dv_cache_0002 p0045_e00_recanon hyp_enprmaplem5_2 p0044
  have p0046 :=
    @gEqeq1d (.classMem (.cv z) B) (synCfv R (.cv z))
      (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0045
  have p0047 :=
    @gBiimpd (.classMem (.cv z) B) (.classEq (synCfv R (.cv z)) (.cv x))
      (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0046
  have p0048 :=
    @gImp (.classMem (.cv z) B) (.classEq (synCfv R (.cv z)) (.cv x))
      (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0047
  have p0049 :=
    @gSimpl1 (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (synWss (.cv p) B) (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x))
  have p0050 := (Nominal.biimpRefl (synWne (.cv x) (.cv y)))
  have p0051_e01_recanon :
    Nominal.NPrf (synWb (synWne (.cv x) (.cv y)) (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @gSylib
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x)))
      (synWne (.cv x) (.cv y)) (.neg (.objEq x y)) p0049 p0051_e01_recanon
  have p0052 := @gIffalse (.objMem z p) (.cv x) (.cv y)
  have p0053 :=
    @gEqeq2d (.neg (.objMem z p)) (synCif (.objMem z p) (.cv x) (.cv y)) (.cv y) (.cv x)
      p0052
  have p0054_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem z p))
        (synWb (.classEq (.cv x) (synCif (.objMem z p) (.cv x) (.cv y))) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCif synWo synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0053
  have p0054 :=
    @gBiimpd (.neg (.objMem z p))
      (.classEq (.cv x) (synCif (.objMem z p) (.cv x) (.cv y))) (.objEq x y)
      p0054_e00_recanon
  have p0055 :=
    @gCom12 (.neg (.objMem z p))
      (.classEq (.cv x) (synCif (.objMem z p) (.cv x) (.cv y))) (.objEq x y) p0054
  have p0056 :=
    @gEqcoms (.imp (.neg (.objMem z p)) (.objEq x y)) (.cv x)
      (synCif (.objMem z p) (.cv x) (.cv y)) p0055
  have p0057 :=
    @gAdantl (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (.imp (.neg (.objMem z p)) (.objEq x y))
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      p0056
  have p0058 :=
    @gMt3d
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x)))
      (.objMem z p) (.objEq x y) p0051 p0057
  have p0059 :=
    @gEx
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (.objMem z p) p0058
  have p0060 :=
    @gSyl5 (synWa (.classMem (.cv z) B) (.classEq (synCfv R (.cv z)) (.cv x)))
      (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.objMem z p) p0048 p0059
  have p0061 :=
    @gSyl5 (synWbr (.cv z) R (.cv x))
      (synWa (.classMem (.cv z) B) (.classEq (synCfv R (.cv z)) (.cv x)))
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.objMem z p) p0041 p0060
  have p0062 := @gSsel2 (.cv p) B (.cv z)
  have p0063_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWss (.cv p) B) (.objMem z p)) (.classMem (.cv z) B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWss synCin synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0062
  have p0063 :=
    @gN3ad2antl3 (synWss (.cv p) B) (synWne (.cv x) (.cv y)) (.objMem z p)
      (.classMem (.cv z) B) (.classEq A (synCpr (.cv x) (.cv y))) p0063_e00_recanon
  have p0064 :=
    @gSyl
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.objMem z p))
      (.classMem (.cv z) B)
      (.classEq (synCfv R (.cv z)) (synCif (.objMem z p) (.cv x) (.cv y))) p0063 p0045
  have p0065 := @gIftrue (.objMem z p) (.cv x) (.cv y)
  have p0066 :=
    @gAdantl (.objMem z p) (.classEq (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      p0065
  have p0067 :=
    @gEqtrd
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.objMem z p))
      (synCfv R (.cv z)) (synCif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0064 p0066
  have p0068 :=
    @gSyl
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.objMem z p))
      (.classMem (.cv z) B)
      (synWb (.classEq (synCfv R (.cv z)) (.cv x)) (synWbr (.cv z) R (.cv x))) p0063
      p0038
  have p0069 :=
    @gMpbid
      (synWa (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B)) (.objMem z p))
      (.classEq (synCfv R (.cv z)) (.cv x)) (synWbr (.cv z) R (.cv x)) p0067 p0068
  have p0070 :=
    @gEx
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.objMem z p) (synWbr (.cv z) R (.cv x)) p0069
  have p0071 :=
    @gImpbid
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (synWbr (.cv z) R (.cv x)) (.objMem z p) p0061 p0070
  have p0072 :=
    @gSyl5bb (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
      (synWbr (.cv z) R (.cv x))
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.objMem z p) p0029 p0071
  have p0073_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
          (synWss (.cv p) B))
        (synWb (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
          (.classMem (.cv z) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWne synCpr synCun synCnin synWnan synCcompl synCsn
          synWss synCin synWb synCima synWrex synWex synWbr synCop synCcnv
          synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0072
  have p0073 :=
    @gEqrdv
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      z (synCima (synCcnv R) (synCsn (.cv x))) (.cv p) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0073_e00_recanon
  have p0074 :=
    @gEqtrd
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (synCfv W R) (synCima (synCcnv R) (synCsn (.cv x))) (.cv p) p0028 p0073
  have p0075 := @gEnprmaplem2 x A B W r dv_cache_0015 dv_cache_0016 hyp_enprmaplem5_1
  have p0076 := @gFnbrfvb (synCo A (synCmap) B) R (.cv p) W
  have p0077 :=
    @gMpan (synWfn W (synCo A (synCmap) B)) (.classMem R (synCo A (synCmap) B))
      (synWb (.classEq (synCfv W R) (.cv p)) (synWbr R W (.cv p))) p0075 p0076
  have p0078 :=
    @gSyl
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.classMem R (synCo A (synCmap) B))
      (synWb (.classEq (synCfv W R) (.cv p)) (synWbr R W (.cv p))) p0021 p0077
  have p0079 :=
    @gMpbid
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (synWss (.cv p) B))
      (.classEq (synCfv W R) (.cv p)) (synWbr R W (.cv p)) p0074 p0078
  have p0080 :=
    @gN3expia (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (synWss (.cv p) B) (synWbr R W (.cv p)) p0079
  have p0081 := @gBrelrn R (.cv p) W
  have p0082 :=
    @gSyl6 (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWss (.cv p) B) (synWbr R W (.cv p)) (.classMem (.cv p) (synCrn W)) p0080
      p0081
  have p0083 :=
    @gSyl5bi (.classMem (.cv p) (synCpw B)) (synWss (.cv p) B)
      (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.classMem (.cv p) (synCrn W)) p0001 p0082
  have p0084 :=
    @gSsrdv (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))) p
      (synCpw B) (synCrn W) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0083
  exact p0084


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem6`. -/
@[expose]
noncomputable def gEnprmaplem6 (x : Var) (y : Var) (A : Class) (B : Class) (W : Class)
    (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y)
    (hyp_enprmaplem6_1 : Nominal.NPrf (.classEq W (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x))))))
    (hyp_enprmaplem6_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (.classEq (synCrn W) (synCpw B))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪
      ({ r } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p := Ne.symm fresh_p_ne_r
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_s_ne_y : s ≠ y := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_W : s ∉ W.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_r : s ≠ r := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_s : r ≠ s := Ne.symm fresh_s_ne_r
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u := Ne.symm fresh_u_ne_r
  have fresh_p_ne_s : p ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_p : s ≠ p := Ne.symm fresh_p_ne_s
  have fresh_p_ne_u : p ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0002 : r ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_r, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_s, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synCima (synCcnv (.cv s)) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_s, dv_r_x, or_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((synCo A (synCmap) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, dv_A_r,
          dv_B_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((synWss (.cv p) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_p, fresh_s_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 :
    s ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_x, fresh_s_ne_y, fresh_s_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0008 : s ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_p, not_false_eq_true])
  have dv_cache_0009 : s ∉ (W).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_W, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCrn W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_p_not_W,
          not_false_eq_true])
  have dv_cache_0011 : p ∉ ((synCpw B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_p_not_B,
          not_false_eq_true])
  have dv_cache_0012 :
    p ∉ ((synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0013 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0014 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0015 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0016 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0017 : r ∉ ((synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, dv_B_r, dv_r_x, dv_r_y, fresh_r_ne_u,
          fresh_r_ne_p, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ (W).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_W, not_false_eq_true])
  have dv_cache_0019 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0020 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0021 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0022 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0023 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0024 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have p0000 := @gBreldm (.cv s) (.cv p) W
  have p0001 := @gEnprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem6_1
  have p0002 := @gFndm (synCo A (synCmap) B) W
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gSyl6eleq (synWbr (.cv s) W (.cv p)) (.cv s) (synCdm W) (synCo A (synCmap) B)
      p0000 p0003
  have p0005 := @gFnbrfvb (synCo A (synCmap) B) (.cv s) (.cv p) W
  have p0006 :=
    @gSylancr (synWbr (.cv s) W (.cv p)) (synWfn W (synCo A (synCmap) B))
      (.classMem (.cv s) (synCo A (synCmap) B))
      (synWb (.classEq (synCfv W (.cv s)) (.cv p)) (synWbr (.cv s) W (.cv p))) p0001
      p0004 p0005
  have p0007 :=
    @gIbir (synWbr (.cv s) W (.cv p)) (.classEq (synCfv W (.cv s)) (.cv p)) p0006
  have p0008 :=
    @gJca (synWbr (.cv s) W (.cv p)) (.classMem (.cv s) (synCo A (synCmap) B))
      (.classEq (synCfv W (.cv s)) (.cv p)) p0004 p0007
  have p0009 := @gCnveq (.cv r) (.cv s)
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.objEq r s) (.classEq (synCcnv (.cv r)) (synCcnv (.cv s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCcnv synCopab synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gImaeq1d (.objEq r s) (synCcnv (.cv r)) (synCcnv (.cv s)) (synCsn (.cv x))
      p0010_e00_recanon
  have p0011 := @gVex s
  have p0012 := @gCnvex (.cv s) p0011
  have p0013 := @gSnex (.cv x)
  have p0014 := @gImaex (synCcnv (.cv s)) (synCsn (.cv x)) p0012 p0013
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv s)) (.classEq (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
          (synCima (synCcnv (.cv s)) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCima synWrex synWex synWa synWbr synCop synCun synCnin synWnan
          synCcompl synCcnv synCopab synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0015 :=
    @gFvmpt r (.cv s) (synCima (synCcnv (.cv r)) (synCsn (.cv x)))
      (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (synCo A (synCmap) B) W
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0015_e00_recanon hyp_enprmaplem6_1 p0014
  have p0016 :=
    @gEqeq1d (.classMem (.cv s) (synCo A (synCmap) B)) (synCfv W (.cv s))
      (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (.cv p) p0015
  have p0017 :=
    @gN3ad2ant3 (.classMem (.cv s) (synCo A (synCmap) B)) (synWne (.cv x) (.cv y))
      (synWb (.classEq (synCfv W (.cv s)) (.cv p))
        (.classEq (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (.cv p)))
      (.classEq A (synCpr (.cv x) (.cv y))) p0016
  have p0018 := @gImassrn (synCcnv (.cv s)) (synCsn (.cv x))
  have p0019 := (Nominal.classEqRefl (synCdm (.cv s)))
  have p0020 := @gElmapi (.cv s) A B
  have p0021 := @gFdm B A (.cv s)
  have p0022 := @gEqimss (synCdm (.cv s)) B
  have p0023 :=
    @gN3syl (.classMem (.cv s) (synCo A (synCmap) B)) (synWf (.cv s) B A)
      (.classEq (synCdm (.cv s)) B) (synWss (synCdm (.cv s)) B) p0020 p0021 p0022
  have p0024 :=
    @gSyl5eqssr (.classMem (.cv s) (synCo A (synCmap) B)) (synCrn (synCcnv (.cv s)))
      (synCdm (.cv s)) B p0019 p0023
  have p0025 :=
    @gSyl5ss (.classMem (.cv s) (synCo A (synCmap) B))
      (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (synCrn (synCcnv (.cv s))) B p0018
      p0024
  have p0026 :=
    @gN3ad2ant3 (.classMem (.cv s) (synCo A (synCmap) B)) (synWne (.cv x) (.cv y))
      (synWss (synCima (synCcnv (.cv s)) (synCsn (.cv x))) B)
      (.classEq A (synCpr (.cv x) (.cv y))) p0025
  have p0027 := @gSseq1 (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (.cv p) B
  have p0028 :=
    @gSyl5ibcom
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (.classMem (.cv s) (synCo A (synCmap) B)))
      (synWss (synCima (synCcnv (.cv s)) (synCsn (.cv x))) B)
      (.classEq (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (.cv p))
      (synWss (.cv p) B) p0026 p0027
  have p0029 :=
    @gSylbid
      (synW3a (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
        (.classMem (.cv s) (synCo A (synCmap) B)))
      (.classEq (synCfv W (.cv s)) (.cv p))
      (.classEq (synCima (synCcnv (.cv s)) (synCsn (.cv x))) (.cv p))
      (synWss (.cv p) B) p0017 p0028
  have p0030 :=
    @gN3expia (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))
      (.classMem (.cv s) (synCo A (synCmap) B))
      (.imp (.classEq (synCfv W (.cv s)) (.cv p)) (synWss (.cv p) B)) p0029
  have p0031 :=
    @gImp3a (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (.classMem (.cv s) (synCo A (synCmap) B)) (.classEq (synCfv W (.cv s)) (.cv p))
      (synWss (.cv p) B) p0030
  have p0032 :=
    @gSyl5 (synWbr (.cv s) W (.cv p))
      (synWa (.classMem (.cv s) (synCo A (synCmap) B))
        (.classEq (synCfv W (.cv s)) (.cv p)))
      (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWss (.cv p) B) p0008 p0031
  have p0033 :=
    @gExlimdv (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWbr (.cv s) W (.cv p)) (synWss (.cv p) B) s dv_cache_0006 dv_cache_0007 p0032
  have p0034 := @gElrn s (.cv p) W dv_cache_0008 dv_cache_0009
  have p0035 := @gVex p
  have p0036 := @gElpw (.cv p) B p0035
  have p0037 :=
    @gN3imtr4g (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWex s (synWbr (.cv s) W (.cv p))) (synWss (.cv p) B)
      (.classMem (.cv p) (synCrn W)) (.classMem (.cv p) (synCpw B)) p0033 p0034 p0036
  have p0038 :=
    @gSsrdv (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))) p
      (synCrn W) (synCpw B) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0037
  have p0039 := @gEqid (synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y)))
  have p0040 :=
    @gEnprmaplem5 x y u A B (synCmpt u B (synCif (.objMem u p) (.cv x) (.cv y))) W r p
      dv_cache_0013 dv_cache_0001 dv_cache_0014 dv_cache_0015 dv_cache_0002 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 hyp_enprmaplem6_1 p0039 hyp_enprmaplem6_2
  have p0041 :=
    @gEqssd (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synCrn W) (synCpw B) p0038 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_enprmap`. -/
@[expose]
noncomputable def gEnprmap (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_enprmap_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
        (synWbr (synCo A (synCmap) B) (synCen) (synCpw B))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_B, not_false_eq_true])
  have dv_cache_0003 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0004 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have p0000 :=
    @gEqid
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
  have p0001 :=
    @gEnprmaplem2 x A B
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      r dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @gA1i
      (synWfn (synCmpt r (synCo A (synCmap) B)
          (synCima (synCcnv (.cv r)) (synCsn (.cv x)))) (synCo A (synCmap) B))
      (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y)))) p0001
  have p0003 :=
    @gEnprmaplem3 x y A B
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0004 :=
    @gEnprmaplem6 x y A B
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 hyp_enprmap_1
  have p0005 :=
    @gDff1o2 (synCo A (synCmap) B) (synCpw B)
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
  have p0006 :=
    @gSyl3anbrc (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWfn (synCmpt r (synCo A (synCmap) B)
          (synCima (synCcnv (.cv r)) (synCsn (.cv x)))) (synCo A (synCmap) B))
      (synWfun (synCcnv (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x))))))
      (.classEq (synCrn (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x))))) (synCpw B))
      (synWf1o (synCmpt r (synCo A (synCmap) B)
          (synCima (synCcnv (.cv r)) (synCsn (.cv x)))) (synCo A (synCmap) B) (synCpw B))
      p0002 p0003 p0004 p0005
  have p0007 :=
    @gEnprmaplem1 x A B
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0008 :=
    @gF1oen (synCo A (synCmap) B) (synCpw B)
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      p0007
  have p0009 :=
    @gSyl (synWa (synWne (.cv x) (.cv y)) (.classEq A (synCpr (.cv x) (.cv y))))
      (synWf1o (synCmpt r (synCo A (synCmap) B)
          (synCima (synCcnv (.cv r)) (synCsn (.cv x)))) (synCo A (synCmap) B) (synCpw B))
      (synWbr (synCo A (synCmap) B) (synCen) (synCpw B)) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_enprmapc`. -/
@[expose]
noncomputable def gEnprmapc (A : Class) (B : Class) (C : Class) (P : Class)
    (hyp_enprmapc_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_enprmapc_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_enprmapc_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWne A B) (.classEq P (synCpr A B)))
        (synWbr (synCo P (synCmap) C) (synCen) (synCpw C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ P.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_P : x ∉ P.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_P : y ∉ P.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0002 :
    y ∉
      ((Wff.imp (synWa (synWne (.cv x) B) (.classEq P (synCpr (.cv x) B)))
          (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_not_P, fresh_y_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (synWa (synWne A B) (.classEq P (synCpr A B)))
          (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_P, fresh_x_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gNeeq1 (.cv x) A B
  have p0001 := @gPreq1 (.cv x) A B
  have p0002 := @gEqeq2d (.classEq (.cv x) A) (synCpr (.cv x) B) (synCpr A B) P p0001
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A) (synWne (.cv x) B) (synWne A B)
      (.classEq P (synCpr (.cv x) B)) (.classEq P (synCpr A B)) p0000 p0002
  have p0004 :=
    @gImbi1d (.classEq (.cv x) A)
      (synWa (synWne (.cv x) B) (.classEq P (synCpr (.cv x) B)))
      (synWa (synWne A B) (.classEq P (synCpr A B)))
      (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)) p0003
  have p0005 := @gNeeq2 (.cv y) B (.cv x)
  have p0006 := @gPreq2 (.cv y) B (.cv x)
  have p0007 :=
    @gEqeq2d (.classEq (.cv y) B) (synCpr (.cv x) (.cv y)) (synCpr (.cv x) B) P p0006
  have p0008 :=
    @gAnbi12d (.classEq (.cv y) B) (synWne (.cv x) (.cv y)) (synWne (.cv x) B)
      (.classEq P (synCpr (.cv x) (.cv y))) (.classEq P (synCpr (.cv x) B)) p0005 p0007
  have p0009 :=
    @gImbi1d (.classEq (.cv y) B)
      (synWa (synWne (.cv x) (.cv y)) (.classEq P (synCpr (.cv x) (.cv y))))
      (synWa (synWne (.cv x) B) (.classEq P (synCpr (.cv x) B)))
      (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)) p0008
  have p0010 := @gEnprmap x y P C hyp_enprmapc_3
  have p0011 :=
    @gVtocl
      (.imp (synWa (synWne (.cv x) (.cv y)) (.classEq P (synCpr (.cv x) (.cv y))))
        (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))
      (.imp (synWa (synWne (.cv x) B) (.classEq P (synCpr (.cv x) B)))
        (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))
      y B dv_cache_0001 dv_cache_0002 hyp_enprmapc_2 p0009 p0010
  have p0012 :=
    @gVtocl
      (.imp (synWa (synWne (.cv x) B) (.classEq P (synCpr (.cv x) B)))
        (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))
      (.imp (synWa (synWne A B) (.classEq P (synCpr A B)))
        (synWbr (synCo P (synCmap) C) (synCen) (synCpw C)))
      x A dv_cache_0003 dv_cache_0004 hyp_enprmapc_1 p0004 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_enpw`. -/
@[expose]
noncomputable def gEnpw (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWbr A (synCen) B) (synWbr (synCpw A) (synCen) (synCpw B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : a ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0003 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0004 :
    b ∉
      ((Wff.imp (synWbr A (synCen) B) (synWbr (synCpw A) (synCen) (synCpw B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    a ∉
      ((Wff.imp (synWbr A (synCen) (.cv b))
          (synWbr (synCpw A) (synCen) (synCpw (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCen)
  have p0001 := @gBreq1 (.cv a) A (.cv b) (synCen)
  have p0002 := @gPweq (.cv a) A
  have p0003 :=
    @gBreq1d (.classEq (.cv a) A) (synCpw (.cv a)) (synCpw A) (synCpw (.cv b))
      (synCen) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv a) A) (synWbr (.cv a) (synCen) (.cv b))
      (synWbr A (synCen) (.cv b))
      (synWbr (synCpw (.cv a)) (synCen) (synCpw (.cv b)))
      (synWbr (synCpw A) (synCen) (synCpw (.cv b))) p0001 p0003
  have p0005 := @gBreq2 (.cv b) B A (synCen)
  have p0006 := @gPweq (.cv b) B
  have p0007 :=
    @gBreq2d (.classEq (.cv b) B) (synCpw (.cv b)) (synCpw B) (synCpw A) (synCen)
      p0006
  have p0008 :=
    @gImbi12d (.classEq (.cv b) B) (synWbr A (synCen) (.cv b)) (synWbr A (synCen) B)
      (synWbr (synCpw A) (synCen) (synCpw (.cv b)))
      (synWbr (synCpw A) (synCen) (synCpw B)) p0005 p0007
  have p0009 := @gEnmap2 (.cv a) (.cv b) (synCpr (synCvv) (synC0))
  have p0010 := @gVn0
  have p0011 := @gEqid (synCpr (synCvv) (synC0))
  have p0012 := @gVvex
  have p0013 := @gN0ex
  have p0014 := @gVex a
  have p0015 :=
    @gEnprmapc (synCvv) (synC0) (.cv a) (synCpr (synCvv) (synC0)) p0012 p0013 p0014
  have p0016 :=
    @gMp2an (synWne (synCvv) (synC0))
      (.classEq (synCpr (synCvv) (synC0)) (synCpr (synCvv) (synC0)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCpw (.cv a)))
      p0010 p0011 p0015
  have p0017 :=
    @gEnsym (synCpw (.cv a)) (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a))
  have p0018 :=
    @gMpbir
      (synWbr (synCpw (.cv a)) (synCen)
        (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCpw (.cv a)))
      p0016 p0017
  have p0022 := @gVex b
  have p0023 :=
    @gEnprmapc (synCvv) (synC0) (.cv b) (synCpr (synCvv) (synC0)) p0012 p0013 p0022
  have p0024 :=
    @gMp2an (synWne (synCvv) (synC0))
      (.classEq (synCpr (synCvv) (synC0)) (synCpr (synCvv) (synC0)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)) (synCen)
        (synCpw (.cv b)))
      p0010 p0011 p0023
  have p0025 :=
    @gEntr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a))
      (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)) (synCpw (.cv b))
  have p0026 :=
    @gMpan2
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)) (synCen)
        (synCpw (.cv b)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCpw (.cv b)))
      p0024 p0025
  have p0027 :=
    @gEntr (synCpw (.cv a)) (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a))
      (synCpw (.cv b))
  have p0028 :=
    @gSylancr
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)))
      (synWbr (synCpw (.cv a)) (synCen)
        (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCpw (.cv b)))
      (synWbr (synCpw (.cv a)) (synCen) (synCpw (.cv b))) p0018 p0026 p0027
  have p0029 :=
    @gSyl (synWbr (.cv a) (synCen) (.cv b))
      (synWbr (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv a)) (synCen)
        (synCo (synCpr (synCvv) (synC0)) (synCmap) (.cv b)))
      (synWbr (synCpw (.cv a)) (synCen) (synCpw (.cv b))) p0009 p0028
  have p0030 :=
    @gVtocl2g
      (.imp (synWbr (.cv a) (synCen) (.cv b))
        (synWbr (synCpw (.cv a)) (synCen) (synCpw (.cv b))))
      (.imp (synWbr A (synCen) (.cv b)) (synWbr (synCpw A) (synCen) (synCpw (.cv b))))
      (.imp (synWbr A (synCen) B) (synWbr (synCpw A) (synCen) (synCpw B))) a b A B
      (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0004 p0008 p0029
  have p0031 :=
    @gMpcom (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWbr A (synCen) B) (synWbr (synCpw A) (synCen) (synCpw B)) p0000 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_nceq`. -/
@[expose]
noncomputable def gNceq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCnc A) (synCnc B))) :=
  by
  have p0000 := @gEceq1 A B (synCen)
  have p0001 := (Nominal.classEqRefl (synCnc A))
  have p0002 := (Nominal.classEqRefl (synCnc B))
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCec A (synCen)) (synCec B (synCen)) (synCnc A)
      (synCnc B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nceqi`. -/
@[expose]
noncomputable def gNceqi (A : Class) (B : Class)
    (hyp_nceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCnc A) (synCnc B)) :=
  by
  have p0000 := @gNceq A B
  have p0001 := Nominal.mp hyp_nceqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nceqd`. -/
@[expose]
noncomputable def gNceqd (ph : Wff) (A : Class) (B : Class)
    (hyp_nceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCnc A) (synCnc B))) :=
  by
  have p0000 := @gNceq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCnc A) (synCnc B)) hyp_nceqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ncsex`. -/
@[expose]
noncomputable def gNcsex : Nominal.NPrf (.classMem (synCncs) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCncs))
  have p0001 := @gEnex
  have p0002 := @gVvex
  have p0003 := @gQsex (synCvv) (synCen) p0001 p0002
  have p0004 := @gEqeltri (synCncs) (synCqs (synCvv) (synCen)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_brlecg`. -/
@[expose]
noncomputable def gBrlecg (x : Var) (y : Var) (A : Class) (B : Class) (V : Class)
    (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (synWb (synWbr A (synClec) B)
          (synWrex x A (synWrex y B (synWss (.cv x) (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let b : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_a : b ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv b) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_b, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0007 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0008 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0010 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0012 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0013 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0014 : a ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0015 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((synWrex x A (synWrex y B (synWss (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_not_B, fresh_a_ne_x, fresh_a_ne_y,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((synWrex x A (synWrex y B (synWss (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_x, fresh_b_ne_y,
          or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gRexeq (synWrex y (.cv b) (synWss (.cv x) (.cv y))) x (.cv a) A dv_cache_0001
      dv_cache_0002
  have p0001 := @gRexeq (synWss (.cv x) (.cv y)) y (.cv b) B dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gRexbidv (.classEq (.cv b) B) (synWrex y (.cv b) (synWss (.cv x) (.cv y)))
      (synWrex y B (synWss (.cv x) (.cv y))) x A dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLec x y a b
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    @gBrabg (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y))))
      (synWrex x A (synWrex y (.cv b) (synWss (.cv x) (.cv y))))
      (synWrex x A (synWrex y B (synWss (.cv x) (.cv y)))) a b A B V W (synClec)
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0006 p0000 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brlec`. -/
@[expose]
noncomputable def gBrlec (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_brlec_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brlec_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr A (synClec) B)
        (synWrex x A (synWrex y B (synWss (.cv x) (.cv y))))) :=
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
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gBrlecg x y A B (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr A (synClec) B) (synWrex x A (synWrex y B (synWss (.cv x) (.cv y)))))
      hyp_brlec_1 hyp_brlec_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brltc`. -/
@[expose]
noncomputable def gBrltc (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCltc) B) (synWa (synWbr A (synClec) B) (synWne A B))) :=
  by
  have p0000 := @gBrex A B (synCltc)
  have p0001 :=
    @gSimprd (synWbr A (synCltc) B) (.classMem A (synCvv)) (.classMem B (synCvv))
      p0000
  have p0002 := @gBrex A B (synClec)
  have p0003 :=
    @gSimprd (synWbr A (synClec) B) (.classMem A (synCvv)) (.classMem B (synCvv))
      p0002
  have p0004 :=
    @gAdantr (synWbr A (synClec) B) (.classMem B (synCvv)) (synWne A B) p0003
  have p0005 := (Nominal.classEqRefl (synCltc))
  have p0006 := @gBreqi A B (synCltc) (synCdif (synClec) (synCid)) p0005
  have p0007 := @gBrdif A B (synClec) (synCid)
  have p0008 :=
    @gBitri (synWbr A (synCltc) B) (synWbr A (synCdif (synClec) (synCid)) B)
      (synWa (synWbr A (synClec) B) (.neg (synWbr A (synCid) B))) p0006 p0007
  have p0009 := @gIdeqg A B (synCvv)
  have p0010 := @gNecon3bbid (.classMem B (synCvv)) (synWbr A (synCid) B) A B p0009
  have p0011 :=
    @gAnbi2d (.classMem B (synCvv)) (.neg (synWbr A (synCid) B)) (synWne A B)
      (synWbr A (synClec) B) p0010
  have p0012 :=
    @gSyl5bb (synWbr A (synCltc) B)
      (synWa (synWbr A (synClec) B) (.neg (synWbr A (synCid) B)))
      (.classMem B (synCvv)) (synWa (synWbr A (synClec) B) (synWne A B)) p0008 p0011
  have p0013 :=
    @gPm521nii (synWbr A (synCltc) B) (.classMem B (synCvv))
      (synWa (synWbr A (synClec) B) (synWne A B)) p0001 p0004 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_lecex`. -/
@[expose]
noncomputable def gLecex : Nominal.NPrf (.classMem (synClec) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_u : a ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_u : b ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have dv_cache_0001 : y ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : t ∉ ((synWss (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((synWss (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0006 : u ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_x,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0008 : u ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_y,
          not_false_eq_true])
  have dv_cache_0009 :
    u ∉
      ((synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
          (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_a, fresh_u_ne_y, fresh_u_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    t ∉
      ((synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_u, fresh_t_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0012 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_b, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((synCcom (synCsset) (synCsi (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((synCcnv (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 : u ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_t, not_false_eq_true])
  have dv_cache_0020 : u ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_b, not_false_eq_true])
  have dv_cache_0021 : u ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 : u ∉ ((synCsi (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv u)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((synCsset)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0029 : u ∉ ((synWbr (.cv t) (synCsset) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0030 :
    x ∉
      ((synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_u, fresh_x_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 :
    y ∉
      ((synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, fresh_y_ne_u, fresh_y_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((synClec)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((synClec)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0034 :
    a ∉
      ((synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 :
    b ∉
      ((synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @gR2ex (synWss (.cv x) (.cv y)) x y (.cv a) (.cv b) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gN1941vv
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synWss (.cv x) (.cv y)) t u dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAnass
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
      (synWss (.cv x) (.cv y))
  have p0003 :=
    @gN2exbii
      (synWa (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
            (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))))) (synWss (.cv x) (.cv y)))
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa
          (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
          (synWss (.cv x) (.cv y))))
      t u p0002
  have p0004 :=
    @gAncom
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
  have p0005 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))))
  have p0006 :=
    @gBitr4i
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      p0004 p0005
  have p0007 :=
    @gN2exbii
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      t u p0006
  have p0008 := @gSnex (.cv x)
  have p0009 := @gSnex (.cv y)
  have p0010 := @gBreq1 (.cv t) (synCsn (.cv x)) (.cv a) (synCsset)
  have p0011 :=
    @gAnbi1d (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) (synCsset) (.cv a))
      (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
      (synWbr (.cv u) (synCsset) (.cv b)) p0010
  have p0012 := @gBreq1 (.cv u) (synCsn (.cv y)) (.cv b) (synCsset)
  have p0013 :=
    @gAnbi2d (.classEq (.cv u) (synCsn (.cv y))) (synWbr (.cv u) (synCsset) (.cv b))
      (synWbr (synCsn (.cv y)) (synCsset) (.cv b))
      (synWbr (synCsn (.cv x)) (synCsset) (.cv a)) p0012
  have p0014 :=
    @gCeqsex2v
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))
      t u (synCsn (.cv x)) (synCsn (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008 p0009 p0011 p0013
  have p0015 := @gVex x
  have p0016 := @gVex a
  have p0017 := @gBrssetsn (.cv x) (.cv a) p0015 p0016
  have p0018 := @gVex y
  have p0019 := @gVex b
  have p0020 := @gBrssetsn (.cv y) (.cv b) p0018 p0019
  have p0021_e00_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv x)) (synCsset) (.cv a)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0021_e01_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv y)) (synCsset) (.cv b)) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @gAnbi12i (synWbr (synCsn (.cv x)) (synCsset) (.cv a)) (.objMem x a)
      (synWbr (synCsn (.cv y)) (synCsset) (.cv b)) (.objMem y b) p0021_e00_recanon
      p0021_e01_recanon
  have p0022 :=
    @gN3bitri
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b)))
            (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))))))
      (synWex t (synWex u (synW3a (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))) (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))))))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))
      (synWa (.objMem x a) (.objMem y b)) p0007 p0014 p0021
  have p0023 :=
    @gAnbi1i
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b)))
            (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))))))
      (synWa (.objMem x a) (.objMem y b)) (synWss (.cv x) (.cv y)) p0022
  have p0024 :=
    @gN3bitr3i
      (synWex t (synWex u (synWa (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b)))
              (synWa (.classEq (.cv t) (synCsn (.cv x)))
                (.classEq (.cv u) (synCsn (.cv y))))) (synWss (.cv x) (.cv y)))))
      (synWa (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b)))
              (synWa (.classEq (.cv t) (synCsn (.cv x)))
                (.classEq (.cv u) (synCsn (.cv y))))))) (synWss (.cv x) (.cv y)))
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      (synWa (synWa (.objMem x a) (.objMem y b)) (synWss (.cv x) (.cv y))) p0001 p0003
      p0023
  have p0025 :=
    @gN2exbii
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      (synWa (synWa (.objMem x a) (.objMem y b)) (synWss (.cv x) (.cv y))) x y p0024
  have p0026_e00_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y)))) (synWex x
          (synWex y
            (synWa (synWa (.objMem x a) (.objMem y b)) (synWss (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0026 :=
    @gBitr4i (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y))))
      (synWex x (synWex y
          (synWa (synWa (.objMem x a) (.objMem y b)) (synWss (.cv x) (.cv y)))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      p0026_e00_recanon p0025
  have p0027 :=
    @gBrlec x y (.cv a) (.cv b) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0002
      p0016 p0019
  have p0028 :=
    @gBrco t (.cv a) (.cv b) (synCcom (synCsset) (synCsi (synCsset)))
      (synCcnv (synCsset)) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0029 := @gBrcnv (.cv a) (.cv t) (synCsset)
  have p0030 :=
    @gBrco u (.cv t) (.cv b) (synCsset) (synCsi (synCsset)) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0031 :=
    @gBrsi x y (.cv t) (.cv u) (synCsset) dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0002
  have p0032 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWbr (.cv x) (synCsset) (.cv y))))
  have p0033 := @gBrsset (.cv x) (.cv y) p0015 p0018
  have p0034 :=
    @gAnbi2i (synWbr (.cv x) (synCsset) (.cv y)) (synWss (.cv x) (.cv y))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
      p0033
  have p0035 :=
    @gBitri
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWbr (.cv x) (synCsset) (.cv y)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWbr (.cv x) (synCsset) (.cv y)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWss (.cv x) (.cv y)))
      p0032 p0034
  have p0036 :=
    @gN2exbii
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWbr (.cv x) (synCsset) (.cv y)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWss (.cv x) (.cv y)))
      x y p0035
  have p0037 :=
    @gBitri (synWbr (.cv t) (synCsi (synCsset)) (.cv u))
      (synWex x (synWex y (synW3a (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))) (synWbr (.cv x) (synCsset) (.cv y)))))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))
      p0031 p0036
  have p0038 :=
    @gAnbi2ci (synWbr (.cv t) (synCsi (synCsset)) (.cv u))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))
      (synWbr (.cv u) (synCsset) (.cv b)) p0037
  have p0039 :=
    @gExbii
      (synWa (synWbr (.cv t) (synCsi (synCsset)) (.cv u))
        (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      u p0038
  have p0040 :=
    @gBitri (synWbr (.cv t) (synCcom (synCsset) (synCsi (synCsset))) (.cv b))
      (synWex u (synWa (synWbr (.cv t) (synCsi (synCsset)) (.cv u))
          (synWbr (.cv u) (synCsset) (.cv b))))
      (synWex u (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      p0030 p0039
  have p0041 :=
    @gAnbi12i (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
      (synWbr (.cv t) (synCsset) (.cv a))
      (synWbr (.cv t) (synCcom (synCsset) (synCsi (synCsset))) (.cv b))
      (synWex u (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      p0029 p0040
  have p0042 :=
    @gN1942v (synWbr (.cv t) (synCsset) (.cv a))
      (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      u dv_cache_0029
  have p0043 :=
    @gN1942vv
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWss (.cv x) (.cv y)))
      x y dv_cache_0030 dv_cache_0031
  have p0044 :=
    @gAnass (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))
  have p0045 :=
    @gBitr2i
      (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      (synWa (synWbr (.cv t) (synCsset) (.cv a))
        (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      p0043 p0044
  have p0046 :=
    @gExbii
      (synWa (synWbr (.cv t) (synCsset) (.cv a))
        (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWss (.cv x) (.cv y))))))
      u p0045
  have p0047 :=
    @gN3bitr2i
      (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
        (synWbr (.cv t) (synCcom (synCsset) (synCsi (synCsset))) (.cv b)))
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWex u
          (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      (synWex u (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      (synWex u (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      p0041 p0042 p0046
  have p0048 :=
    @gExbii
      (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
        (synWbr (.cv t) (synCcom (synCsset) (synCsi (synCsset))) (.cv b)))
      (synWex u (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y)))))))
      t p0047
  have p0049 :=
    @gExrot4
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa
          (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
          (synWss (.cv x) (.cv y))))
      t u x y
  have p0050 :=
    @gN3bitri
      (synWbr (.cv a)
        (synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset))) (.cv b))
      (synWex t (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
          (synWbr (.cv t) (synCcom (synCsset) (synCsi (synCsset))) (.cv b))))
      (synWex t (synWex u (synWex x (synWex y (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      p0028 p0048 p0049
  have p0051 :=
    @gN3bitr4i (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWss (.cv x) (.cv y))))))))
      (synWbr (.cv a) (synClec) (.cv b))
      (synWbr (.cv a)
        (synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset))) (.cv b))
      p0026 p0027 p0050
  have p0052 :=
    @gEqbrriv a b (synClec)
      (synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset)))
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0051
  have p0053 := @gSsetex
  have p0055 := @gSiex (synCsset) p0053
  have p0056 := @gCoex (synCsset) (synCsi (synCsset)) p0053 p0055
  have p0058 := @gCnvex (synCsset) p0053
  have p0059 :=
    @gCoex (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset)) p0056
      p0058
  have p0060 :=
    @gEqeltri (synClec)
      (synCcom (synCcom (synCsset) (synCsi (synCsset))) (synCcnv (synCsset)))
      (synCvv) p0052 p0059
  exact p0060

/-- Checked nominal proof certificate identified upstream as `g_ltcex`. -/
@[expose]
noncomputable def gLtcex : Nominal.NPrf (.classMem (synCltc) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCltc))
  have p0001 := @gLecex
  have p0002 := @gIdex
  have p0003 := @gDifex (synClec) (synCid) p0001 p0002
  have p0004 :=
    @gEqeltri (synCltc) (synCdif (synClec) (synCid)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ncex`. -/
@[expose]
noncomputable def gNcex (A : Class) : Nominal.NPrf (.classMem (synCnc A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCnc A))
  have p0001 := @gEnex
  have p0002 := @gEcexg A (synCvv) (synCen)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gEqeltri (synCnc A) (synCec A (synCen)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nulnnc`. -/
@[expose]
noncomputable def gNulnnc : Nominal.NPrf (.neg (.classMem (synC0) (synCncs))) :=
  by
  have p0000 := @gEqid (synC0)
  have p0001 := @gDmen
  have p0002 := @gElqsn0 (synCvv) (synC0) (synCen)
  have p0003 :=
    @gMpan (.classEq (synCdm (synCen)) (synCvv))
      (.classMem (synC0) (synCqs (synCvv) (synCen))) (synWne (synC0) (synC0)) p0001
      p0002
  have p0004 := (Nominal.classEqRefl (synCncs))
  have p0005 :=
    @gEleq2s (synWne (synC0) (synC0)) (synC0) (synCqs (synCvv) (synCen))
      (synCncs) p0003 p0004
  have p0006 := @gNecon2bi (.classMem (synC0) (synCncs)) (synC0) (synC0) p0005
  have p0007 := Nominal.mp p0000 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elncs`. -/
@[expose]
noncomputable def gElncs (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))) :=
  by
  have dv_cache_0001 : x ∉ ((Wff.classMem A (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCncs))
  have p0001 := @gEleq2i (synCncs) (synCqs (synCvv) (synCen)) A p0000
  have p0002 := @gElex A (synCqs (synCvv) (synCen))
  have p0003 := @gNcex (.cv x)
  have p0004 := @gEleq1 A (synCnc (.cv x)) (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A (synCnc (.cv x))) (.classMem A (synCvv))
      (.classMem (synCnc (.cv x)) (synCvv)) p0003 p0004
  have p0006 :=
    @gExlimiv (.classEq A (synCnc (.cv x))) (.classMem A (synCvv)) x dv_cache_0001
      p0005
  have p0007 :=
    @gElqsg x (synCvv) A (synCen) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 := (Nominal.classEqRefl (synCnc (.cv x)))
  have p0009 := @gEqeq2i (synCnc (.cv x)) (synCec (.cv x) (synCen)) A p0008
  have p0010 :=
    @gExbii (.classEq A (synCnc (.cv x))) (.classEq A (synCec (.cv x) (synCen))) x
      p0009
  have p0011 := @gRexv (.classEq A (synCec (.cv x) (synCen))) x
  have p0012 :=
    @gBitr4i (synWex x (.classEq A (synCnc (.cv x))))
      (synWex x (.classEq A (synCec (.cv x) (synCen))))
      (synWrex x (synCvv) (.classEq A (synCec (.cv x) (synCen)))) p0010 p0011
  have p0013 :=
    @gSyl6bbr (.classMem A (synCvv)) (.classMem A (synCqs (synCvv) (synCen)))
      (synWrex x (synCvv) (.classEq A (synCec (.cv x) (synCen))))
      (synWex x (.classEq A (synCnc (.cv x)))) p0007 p0012
  have p0014 :=
    @gPm521nii (.classMem A (synCqs (synCvv) (synCen))) (.classMem A (synCvv))
      (synWex x (.classEq A (synCnc (.cv x)))) p0002 p0006 p0013
  have p0015 :=
    @gBitri (.classMem A (synCncs)) (.classMem A (synCqs (synCvv) (synCen)))
      (synWex x (.classEq A (synCnc (.cv x)))) p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_ncelncs`. -/
@[expose]
noncomputable def gNcelncs (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCnc A) (synCncs))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCnc A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_A,
          not_false_eq_true])
  have p0000 := @gElisset x A V dv_cache_0001
  have p0001 := @gNceq A (.cv x)
  have p0002 := @gEqcoms (.classEq (synCnc A) (synCnc (.cv x))) A (.cv x) p0001
  have p0003 :=
    @gEximi (.classEq (.cv x) A) (.classEq (synCnc A) (synCnc (.cv x))) x p0002
  have p0004 :=
    @gSyl (.classMem A V) (synWex x (.classEq (.cv x) A))
      (synWex x (.classEq (synCnc A) (synCnc (.cv x)))) p0000 p0003
  have p0005 := @gElncs x (synCnc A) dv_cache_0002
  have p0006 :=
    @gSylibr (.classMem A V) (synWex x (.classEq (synCnc A) (synCnc (.cv x))))
      (.classMem (synCnc A) (synCncs)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ncelncsi`. -/
@[expose]
noncomputable def gNcelncsi (A : Class)
    (hyp_ncelncsi_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCnc A) (synCncs)) :=
  by
  have p0000 := @gNcelncs A (synCvv)
  have p0001 := Nominal.mp hyp_ncelncsi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ncidg`. -/
@[expose]
noncomputable def gNcidg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (synCnc A))) :=
  by
  have p0000 := @gEnrflxg A V
  have p0001 := @gElec A A (synCen)
  have p0002 :=
    @gSylibr (.classMem A V) (synWbr A (synCen) A) (.classMem A (synCec A (synCen)))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCnc A))
  have p0004 :=
    @gSyl6eleqr (.classMem A V) A (synCec A (synCen)) (synCnc A) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ncid`. -/
@[expose]
noncomputable def gNcid (A : Class) (hyp_ncid_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem A (synCnc A)) :=
  by
  have p0000 := @gNcidg A (synCvv)
  have p0001 := Nominal.mp hyp_ncid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elnc`. -/
@[expose]
noncomputable def gElnc (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classMem A (synCnc B)) (synWbr A (synCen) B)) :=
  by
  have p0000 := @gElex A (synCnc B)
  have p0001 := @gEcexr A B (synCen)
  have p0002 := (Nominal.classEqRefl (synCnc B))
  have p0003 :=
    @gEleq2s (.classMem B (synCvv)) A (synCec B (synCen)) (synCnc B) p0001 p0002
  have p0004 :=
    @gJca (.classMem A (synCnc B)) (.classMem A (synCvv)) (.classMem B (synCvv)) p0000
      p0003
  have p0005 := @gBrex A B (synCen)
  have p0006 := @gEleq2i (synCnc B) (synCec B (synCen)) A p0002
  have p0007 := @gElec A B (synCen)
  have p0008 :=
    @gBitri (.classMem A (synCnc B)) (.classMem A (synCec B (synCen)))
      (synWbr B (synCen) A) p0006 p0007
  have p0009 := @gEner
  have p0010 :=
    @gA1i (synWbr (synCen) (synCer) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0009
  have p0011 := @gSimpr (.classMem A (synCvv)) (.classMem B (synCvv))
  have p0012 := @gSimpl (.classMem A (synCvv)) (.classMem B (synCvv))
  have p0013 :=
    @gErsymb (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (synCvv) (synCen)
      B A p0010 p0011 p0012
  have p0014 :=
    @gSyl5bb (.classMem A (synCnc B)) (synWbr B (synCen) A)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (synWbr A (synCen) B)
      p0008 p0013
  have p0015 :=
    @gPm521nii (.classMem A (synCnc B))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (synWbr A (synCen) B)
      p0004 p0005 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_eqncg`. -/
@[expose]
noncomputable def gEqncg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (synWb (.classEq (synCnc A) (synCnc B)) (synWbr A (synCen) B))) :=
  by
  have p0000 := @gNcidg A V
  have p0001 :=
    @gAdantr (.classMem A V) (.classMem A (synCnc A)) (.classEq (synCnc A) (synCnc B))
      p0000
  have p0002 := @gEleq2 (synCnc A) (synCnc B) A
  have p0003 :=
    @gAdantl (.classEq (synCnc A) (synCnc B))
      (synWb (.classMem A (synCnc A)) (.classMem A (synCnc B))) (.classMem A V) p0002
  have p0004 :=
    @gMpbid (synWa (.classMem A V) (.classEq (synCnc A) (synCnc B)))
      (.classMem A (synCnc A)) (.classMem A (synCnc B)) p0001 p0003
  have p0005 := (Nominal.classEqRefl (synCnc B))
  have p0006 :=
    @gSyl6eleq (synWa (.classMem A V) (.classEq (synCnc A) (synCnc B))) A (synCnc B)
      (synCec B (synCen)) p0004 p0005
  have p0007 := @gEcexr A B (synCen)
  have p0008 :=
    @gSyl (synWa (.classMem A V) (.classEq (synCnc A) (synCnc B)))
      (.classMem A (synCec B (synCen))) (.classMem B (synCvv)) p0006 p0007
  have p0009 :=
    @gEx (.classMem A V) (.classEq (synCnc A) (synCnc B)) (.classMem B (synCvv)) p0008
  have p0010 := @gBrex A B (synCen)
  have p0011 :=
    @gSimprd (synWbr A (synCen) B) (.classMem A (synCvv)) (.classMem B (synCvv))
      p0010
  have p0012 :=
    @gA1i (.imp (synWbr A (synCen) B) (.classMem B (synCvv))) (.classMem A V) p0011
  have p0013 := @gEner
  have p0014 :=
    @gA1i (synWbr (synCen) (synCer) (synCvv))
      (synWa (.classMem A V) (.classMem B (synCvv))) p0013
  have p0015 := @gDmen
  have p0016 :=
    @gA1i (.classEq (synCdm (synCen)) (synCvv))
      (synWa (.classMem A V) (.classMem B (synCvv))) p0015
  have p0017 := @gElex A V
  have p0018 :=
    @gAdantr (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv)) p0017
  have p0019 := @gSimpr (.classMem A V) (.classMem B (synCvv))
  have p0020 :=
    @gErth (synWa (.classMem A V) (.classMem B (synCvv))) A B (synCen) (synCvv)
      (synCvv) p0014 p0016 p0018 p0019
  have p0021 := (Nominal.classEqRefl (synCnc A))
  have p0022 :=
    @gEqeq12i (synCnc A) (synCec A (synCen)) (synCnc B) (synCec B (synCen)) p0021
      p0005
  have p0023 :=
    @gSyl6rbbr (synWa (.classMem A V) (.classMem B (synCvv))) (synWbr A (synCen) B)
      (.classEq (synCec A (synCen)) (synCec B (synCen)))
      (.classEq (synCnc A) (synCnc B)) p0020 p0022
  have p0024 :=
    @gEx (.classMem A V) (.classMem B (synCvv))
      (synWb (.classEq (synCnc A) (synCnc B)) (synWbr A (synCen) B)) p0023
  have p0025 :=
    @gPm521ndd (.classMem A V) (.classMem B (synCvv))
      (.classEq (synCnc A) (synCnc B)) (synWbr A (synCen) B) p0009 p0012 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_eqnc`. -/
@[expose]
noncomputable def gEqnc (A : Class) (B : Class)
    (hyp_eqnc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classEq (synCnc A) (synCnc B)) (synWbr A (synCen) B)) :=
  by
  have p0000 := @gEqncg A B (synCvv)
  have p0001 := Nominal.mp hyp_eqnc_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ncseqnc`. -/
@[expose]
noncomputable def gNcseqnc (A : Class) (X : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCncs)) (synWb (.classEq A (synCnc X)) (.classMem X A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWb (.classEq A (synCnc X)) (.classMem X A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_A,
          fresh_y_not_X, or_false, not_false_eq_true])
  have p0000 := @gElncs y A dv_cache_0001
  have p0001 := @gVex y
  have p0002 := @gNcid (.cv y) p0001
  have p0003 := @gEleq2 (synCnc X) (synCnc (.cv y)) (.cv y)
  have p0004 :=
    @gMpbiri (.classEq (synCnc X) (synCnc (.cv y))) (.classMem (.cv y) (synCnc X))
      (.classMem (.cv y) (synCnc (.cv y))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCnc X))
  have p0006 :=
    @gSyl6eleq (.classEq (synCnc X) (synCnc (.cv y))) (.cv y) (synCnc X)
      (synCec X (synCen)) p0004 p0005
  have p0007 := @gEcexr (.cv y) X (synCen)
  have p0008 :=
    @gSyl (.classEq (synCnc X) (synCnc (.cv y)))
      (.classMem (.cv y) (synCec X (synCen))) (.classMem X (synCvv)) p0006 p0007
  have p0009 := @gBrex X (.cv y) (synCen)
  have p0010 :=
    @gSimpld (synWbr X (synCen) (.cv y)) (.classMem X (synCvv))
      (.classMem (.cv y) (synCvv)) p0009
  have p0011 := @gEner
  have p0012 :=
    @gA1i (synWbr (synCen) (synCer) (synCvv)) (.classMem X (synCvv)) p0011
  have p0013 := @gDmen
  have p0014 :=
    @gA1i (.classEq (synCdm (synCen)) (synCvv)) (.classMem X (synCvv)) p0013
  have p0015 := @gId (.classMem X (synCvv))
  have p0016 := @gA1i (.classMem (.cv y) (synCvv)) (.classMem X (synCvv)) p0001
  have p0017 :=
    @gErth (.classMem X (synCvv)) X (.cv y) (synCen) (synCvv) (synCvv) p0012 p0014
      p0015 p0016
  have p0018 := (Nominal.classEqRefl (synCnc (.cv y)))
  have p0019 :=
    @gEqeq12i (synCnc X) (synCec X (synCen)) (synCnc (.cv y))
      (synCec (.cv y) (synCen)) p0005 p0018
  have p0020 :=
    @gSyl6rbbr (.classMem X (synCvv)) (synWbr X (synCen) (.cv y))
      (.classEq (synCec X (synCen)) (synCec (.cv y) (synCen)))
      (.classEq (synCnc X) (synCnc (.cv y))) p0017 p0019
  have p0021 :=
    @gPm521nii (.classEq (synCnc X) (synCnc (.cv y))) (.classMem X (synCvv))
      (synWbr X (synCen) (.cv y)) p0008 p0010 p0020
  have p0022 := @gEqcom (synCnc (.cv y)) (synCnc X)
  have p0023 := @gElnc X (.cv y)
  have p0024 :=
    @gN3bitr4i (.classEq (synCnc X) (synCnc (.cv y))) (synWbr X (synCen) (.cv y))
      (.classEq (synCnc (.cv y)) (synCnc X)) (.classMem X (synCnc (.cv y))) p0021 p0022
      p0023
  have p0025 :=
    @gA1i
      (synWb (.classEq (synCnc (.cv y)) (synCnc X)) (.classMem X (synCnc (.cv y))))
      (.classEq A (synCnc (.cv y))) p0024
  have p0026 := @gEqeq1 A (synCnc (.cv y)) (synCnc X)
  have p0027 := @gEleq2 A (synCnc (.cv y)) X
  have p0028 :=
    @gN3bitr4d (.classEq A (synCnc (.cv y))) (.classEq (synCnc (.cv y)) (synCnc X))
      (.classMem X (synCnc (.cv y))) (.classEq A (synCnc X)) (.classMem X A) p0025 p0026
      p0027
  have p0029 :=
    @gExlimiv (.classEq A (synCnc (.cv y)))
      (synWb (.classEq A (synCnc X)) (.classMem X A)) y dv_cache_0002 p0028
  have p0030 :=
    @gSylbi (.classMem A (synCncs)) (synWex y (.classEq A (synCnc (.cv y))))
      (synWb (.classEq A (synCnc X)) (.classMem X A)) p0000 p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end
