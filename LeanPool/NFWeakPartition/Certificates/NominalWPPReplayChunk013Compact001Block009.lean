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

@[expose]
noncomputable def g_enprmaplem3 (x : Var) (y : Var) (A : Class) (B : Class) (W : Class)
    (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x)
    (hyp_enprmaplem3_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wfun (syn_ccnv W))) :=
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
  have dv_cache_0004 : r ∉ ((syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))).fv :=
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
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv :=
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
  have dv_cache_0007 : r ∉ ((syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))).fv :=
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
      ((syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y)))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
            (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
              (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
                (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
          (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))).fv :=
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
      ((syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))).fv :=
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
    q ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
    z ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
    p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
  have dv_cache_0019 : z ∉ ((syn_ccnv W)).fv :=
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
  have dv_cache_0020 : p ∉ ((syn_ccnv W)).fv :=
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
  have dv_cache_0021 : q ∉ ((syn_ccnv W)).fv :=
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
  have p0000 := @g_brcnv (.cv z) (.cv p) W
  have p0001 := @g_brcnv (.cv z) (.cv q) W
  have p0002 := @g_breldm (.cv p) (.cv z) W
  have p0003 := @g_enprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem3_1
  have p0004 := @g_fndm (syn_co A (syn_cmap) B) W
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_syl6eleq (syn_wbr (.cv p) W (.cv z)) (.cv p) (syn_cdm W) (syn_co A (syn_cmap) B)
      p0002 p0005
  have p0007 := @g_fnfun (syn_co A (syn_cmap) B) W
  have p0008 := Nominal.mp p0003 p0007
  have p0009 := @g_funbrfv (.cv p) (.cv z) W
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_cnveq (.cv r) (.cv p)
  have p0012_e00_recanon :
    Nominal.NPrf (.imp (.objEq r p) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_imaeq1d (.objEq r p) (syn_ccnv (.cv r)) (syn_ccnv (.cv p)) (syn_csn (.cv x))
      p0012_e00_recanon
  have p0013 := @g_vex p
  have p0014 := @g_cnvex (.cv p) p0013
  have p0015 := @g_snex (.cv x)
  have p0016 := @g_imaex (syn_ccnv (.cv p)) (syn_csn (.cv x)) p0014 p0015
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv p)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_ccnv syn_copab syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0017 :=
    @g_fvmpt r (.cv p) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0017_e00_recanon hyp_enprmaplem3_1 p0016
  have p0018 :=
    @g_syl (syn_wbr (.cv p) W (.cv z)) (.classMem (.cv p) (syn_co A (syn_cmap) B))
      (.classEq (syn_cfv W (.cv p)) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) p0006
      p0017
  have p0019 :=
    @g_eqtr3d (syn_wbr (.cv p) W (.cv z)) (syn_cfv W (.cv p)) (.cv z)
      (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) p0010 p0018
  have p0020 :=
    @g_jca (syn_wbr (.cv p) W (.cv z)) (.classMem (.cv p) (syn_co A (syn_cmap) B))
      (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) p0006 p0019
  have p0021 := @g_breldm (.cv q) (.cv z) W
  have p0022 :=
    @g_syl6eleq (syn_wbr (.cv q) W (.cv z)) (.cv q) (syn_cdm W) (syn_co A (syn_cmap) B)
      p0021 p0005
  have p0023 := @g_funbrfv (.cv q) (.cv z) W
  have p0024 := Nominal.mp p0008 p0023
  have p0025 := @g_cnveq (.cv r) (.cv q)
  have p0026_e00_recanon :
    Nominal.NPrf (.imp (.objEq r q) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @g_imaeq1d (.objEq r q) (syn_ccnv (.cv r)) (syn_ccnv (.cv q)) (syn_csn (.cv x))
      p0026_e00_recanon
  have p0027 := @g_vex q
  have p0028 := @g_cnvex (.cv q) p0027
  have p0029 := @g_imaex (syn_ccnv (.cv q)) (syn_csn (.cv x)) p0028 p0015
  have p0030_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv q)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_ccnv syn_copab syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0030 :=
    @g_fvmpt r (.cv q) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W
      dv_cache_0006 dv_cache_0007 dv_cache_0005 p0030_e00_recanon hyp_enprmaplem3_1 p0029
  have p0031 :=
    @g_syl (syn_wbr (.cv q) W (.cv z)) (.classMem (.cv q) (syn_co A (syn_cmap) B))
      (.classEq (syn_cfv W (.cv q)) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) p0022
      p0030
  have p0032 :=
    @g_eqtr3d (syn_wbr (.cv q) W (.cv z)) (syn_cfv W (.cv q)) (.cv z)
      (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) p0024 p0031
  have p0033 :=
    @g_jca (syn_wbr (.cv q) W (.cv z)) (.classMem (.cv q) (syn_co A (syn_cmap) B))
      (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) p0022 p0032
  have p0034 :=
    @g_anim12i (syn_wbr (.cv p) W (.cv z))
      (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B))
        (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))))
      (syn_wbr (.cv q) W (.cv z))
      (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B))
        (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      p0020 p0033
  have p0035 :=
    @g_syl2anb (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv p) W (.cv z))
      (syn_wbr (.cv q) W (.cv z))
      (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))))
        (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) (syn_ccnv W) (.cv q)) p0000 p0001 p0034
  have p0036 := @g_elmapi (.cv p) A B
  have p0037 := @g_elmapi (.cv q) A B
  have p0038 :=
    @g_anim12i (.classMem (.cv p) (syn_co A (syn_cmap) B)) (syn_wf (.cv p) B A)
      (.classMem (.cv q) (syn_co A (syn_cmap) B)) (syn_wf (.cv q) B A) p0036 p0037
  have p0039 :=
    @g_eqtr2 (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))
  have p0040 :=
    @g_simprll (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)
      (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
  have p0041 := @g_ffn B A (.cv p)
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wf (.cv p) B A) (syn_wfn (.cv p) B) p0040 p0041
  have p0043 :=
    @g_simprlr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)
      (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
  have p0044 := @g_ffn B A (.cv q)
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wf (.cv q) B A) (syn_wfn (.cv q) B) p0043 p0044
  have p0046 := @g_ffvelrn B A (.cv z) (.cv p)
  have p0047 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wf (.cv p) B A) (.classMem (.cv z) B) (.classMem (syn_cfv (.cv p) (.cv z)) A)
      p0040 p0046
  have p0048 :=
    @g_simpllr (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
        (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      (.classMem (.cv z) B)
  have p0049 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      A (syn_cpr (.cv x) (.cv y)) (syn_cfv (.cv p) (.cv z)) p0048
  have p0050 := @g_fvex (.cv z) (.cv p)
  have p0051 := @g_elpr (syn_cfv (.cv p) (.cv z)) (.cv x) (.cv y) p0050
  have p0052 :=
    @g_syl6bb
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (syn_cfv (.cv p) (.cv z)) A)
      (.classMem (syn_cfv (.cv p) (.cv z)) (syn_cpr (.cv x) (.cv y)))
      (syn_wo (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
        (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)))
      p0049 p0051
  have p0053 :=
    @g_simprr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
  have p0054 :=
    @g_simplrr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
      (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
      (.classMem (.cv z) B)
  have p0055 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) (.cv z) p0054
  have p0056 := @g_eliniseg (.cv p) (.cv x) (.cv z)
  have p0057 := @g_eliniseg (.cv q) (.cv x) (.cv z)
  have p0058 :=
    @g_n_3bitr3g
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))
      (.classMem (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
      (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0055 p0056
      p0057
  have p0059 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0058
  have p0060 := @g_fnbrfvb B (.cv z) (.cv x) (.cv p)
  have p0061 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wfn (.cv p) B) (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (syn_wbr (.cv z) (.cv p) (.cv x)))
      p0042 p0060
  have p0062 := @g_fnbrfvb B (.cv z) (.cv x) (.cv q)
  have p0063 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wfn (.cv q) B) (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)))
      p0045 p0062
  have p0064 :=
    @g_n_3imtr4d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x))
      (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
      (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) p0059 p0061 p0063
  have p0065 :=
    @g_impr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
      (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) p0064
  have p0066 :=
    @g_eqtr4d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))))
      (syn_cfv (.cv p) (.cv z)) (.cv x) (syn_cfv (.cv q) (.cv z)) p0053 p0065
  have p0067 :=
    @g_expr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
      (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0066
  have p0068 :=
    @g_simprr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))
  have p0069 :=
    @g_simplll (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
        (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))
  have p0070 :=
    @g_neneqd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.cv x) (.cv y) p0069
  have p0071 :=
    @g_adantr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wf (.cv p) B A) (.classMem (.cv z) B) p0040
  have p0072 := @g_ffun B A (.cv p)
  have p0073 := @g_fununiq (.cv z) (.cv x) (.cv y) (.cv p)
  have p0074_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x))
          (syn_wbr (.cv z) (.cv p) (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0073
  have p0074 :=
    @g_n_3expib (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x))
      (syn_wbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074_e00_recanon
  have p0075 :=
    @g_ancomsd (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x))
      (syn_wbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074
  have p0076 :=
    @g_n_3syl
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wf (.cv p) B A) (syn_wfun (.cv p))
      (.imp (syn_wa (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x)))
        (.objEq x y))
      p0071 p0072 p0075
  have p0077 :=
    @g_exp3a
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y)
      p0076
  have p0078 :=
    @g_impr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
      (.imp (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y)) p0077
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa
            (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
            (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
              (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
                (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
          (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
        (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0070
  have p0079 :=
    @g_mtod
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y) p0079_e00_recanon p0078
  have p0080 :=
    @g_expr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
      (.neg (syn_wbr (.cv z) (.cv p) (.cv x))) p0079
  have p0081 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0058
  have p0082 :=
    @g_nsyld
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x))
      (syn_wbr (.cv z) (.cv q) (.cv x)) p0080 p0081
  have p0083 :=
    @g_impr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
      (.neg (syn_wbr (.cv z) (.cv q) (.cv x))) p0082
  have p0084 :=
    @g_simprl
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
  have p0085 :=
    @g_adantr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wf (.cv q) B A)
      (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))) p0043
  have p0086 := @g_fdm B A (.cv q)
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wf (.cv q) B A) (.classEq (syn_cdm (.cv q)) B) p0085 p0086
  have p0088 :=
    @g_eleqtrrd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.cv z) B (syn_cdm (.cv q)) p0084 p0087
  have p0089 := @g_eldm w (.cv z) (.cv q) dv_cache_0008 dv_cache_0009
  have p0090 := @g_brelrn (.cv z) (.cv w) (.cv q)
  have p0091 := @g_frn B A (.cv q)
  have p0092 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wf (.cv q) B A) (syn_wss (syn_crn (.cv q)) A) p0085 p0091
  have p0093 :=
    @g_sseld
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_crn (.cv q)) A (.cv w) p0092
  have p0094 :=
    @g_syl5 (syn_wbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) (syn_crn (.cv q)))
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) p0090 p0093
  have p0095 :=
    @g_simpllr (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
        (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))
  have p0096 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      A (syn_cpr (.cv x) (.cv y)) (.cv w) p0095
  have p0097 := @g_vex w
  have p0098 := @g_elpr (.cv w) (.cv x) (.cv y) p0097
  have p0099 := @g_breq2 (.cv w) (.cv x) (.cv z) (.cv q)
  have p0100_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x)
        (syn_wb (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @g_biimpcd (.objEq w x) (syn_wbr (.cv z) (.cv q) (.cv w))
      (syn_wbr (.cv z) (.cv q) (.cv x)) p0100_e00_recanon
  have p0101 := @g_breq2 (.cv w) (.cv y) (.cv z) (.cv q)
  have p0102_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y)
        (syn_wb (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0101
  have p0102 :=
    @g_biimpcd (.objEq w y) (syn_wbr (.cv z) (.cv q) (.cv w))
      (syn_wbr (.cv z) (.cv q) (.cv y)) p0102_e00_recanon
  have p0103 :=
    @g_orim12d (syn_wbr (.cv z) (.cv q) (.cv w)) (.objEq w x)
      (syn_wbr (.cv z) (.cv q) (.cv x)) (.objEq w y) (syn_wbr (.cv z) (.cv q) (.cv y))
      p0100 p0102
  have p0104 :=
    @g_com12 (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (.objEq w x) (.objEq w y))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0103
  have p0105_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w) (syn_cpr (.cv x) (.cv y)))
        (syn_wo (.objEq w x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_wo
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
    @g_sylbi (.classMem (.cv w) (syn_cpr (.cv x) (.cv y)))
      (syn_wo (.objEq w x) (.objEq w y))
      (.imp (syn_wbr (.cv z) (.cv q) (.cv w))
        (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))))
      p0105_e00_recanon p0104
  have p0106 :=
    @g_syl6bi
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) (.classMem (.cv w) (syn_cpr (.cv x) (.cv y)))
      (.imp (syn_wbr (.cv z) (.cv q) (.cv w))
        (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))))
      p0096 p0105
  have p0107 :=
    @g_com23
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv w) A) (syn_wbr (.cv z) (.cv q) (.cv w))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0106
  have p0108 :=
    @g_mpdd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) A)
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0094
      p0107
  have p0109 :=
    @g_exlimdv
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wbr (.cv z) (.cv q) (.cv w))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) w
      dv_cache_0010 dv_cache_0011 p0108
  have p0110 :=
    @g_syl5bi (.classMem (.cv z) (syn_cdm (.cv q)))
      (syn_wex w (syn_wbr (.cv z) (.cv q) (.cv w)))
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0089
      p0109
  have p0111 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.classMem (.cv z) (syn_cdm (.cv q)))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0088
      p0110
  have p0112 :=
    @g_orel1 (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))
  have p0113 :=
    @g_sylc
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))
      (.neg (syn_wbr (.cv z) (.cv q) (.cv x)))
      (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y)))
      (syn_wbr (.cv z) (.cv q) (.cv y)) p0083 p0111 p0112
  have p0114 :=
    @g_expr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
      (syn_wbr (.cv z) (.cv q) (.cv y)) p0113
  have p0115 := @g_fnbrfvb B (.cv z) (.cv y) (.cv p)
  have p0116 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wfn (.cv p) B) (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv y)))
      p0042 p0115
  have p0117 := @g_fnbrfvb B (.cv z) (.cv y) (.cv q)
  have p0118 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wfn (.cv q) B) (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) (syn_wbr (.cv z) (.cv q) (.cv y)))
      p0045 p0117
  have p0119 :=
    @g_n_3imtr4d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv q) (.cv y))
      (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))
      (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) p0114 p0116 p0118
  have p0120 :=
    @g_impr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))
      (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) p0119
  have p0121 :=
    @g_eqtr4d
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
        (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))))
      (syn_cfv (.cv p) (.cv z)) (.cv y) (syn_cfv (.cv q) (.cv z)) p0068 p0120
  have p0122 :=
    @g_expr
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))
      (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0121
  have p0123 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
      (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z)))
      (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) p0067 p0122
  have p0124 :=
    @g_sylbid
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (syn_cfv (.cv p) (.cv z)) A)
      (syn_wo (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
        (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)))
      (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0052 p0123
  have p0125 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B))
      (.classMem (syn_cfv (.cv p) (.cv z)) A)
      (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0047 p0124
  have p0126 :=
    @g_eqfnfvd
      (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
          (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
            (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      z B (.cv p) (.cv q) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0042
      p0045 p0125
  have p0127_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
          (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
            (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
              (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.objEq p q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0126
  have p0127 :=
    @g_expcom (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
        (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      (.objEq p q) p0127_e00_recanon
  have p0128 :=
    @g_syl2an
      (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B))
        (.classMem (.cv q) (syn_co A (syn_cmap) B)))
      (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A))
      (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (.objEq p q))
      (syn_wa (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))
        (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))
      p0038 p0039 p0127
  have p0129 :=
    @g_an4s (.classMem (.cv p) (syn_co A (syn_cmap) B))
      (.classMem (.cv q) (syn_co A (syn_cmap) B))
      (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))
      (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (.objEq p q))
      p0128
  have p0130 :=
    @g_com12
      (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))))
        (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.objEq p q) p0129
  have p0131 :=
    @g_syl5
      (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv z) (syn_ccnv W) (.cv q)))
      (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))))
        (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B))
          (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.objEq p q) p0035 p0130
  have p0132 :=
    @g_alrimiv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p))
          (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q))
      q dv_cache_0016 p0131
  have p0133 :=
    @g_alrimivv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.all q (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p))
            (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q)))
      z p dv_cache_0017 dv_cache_0018 p0132
  have p0134 :=
    @g_dffun2 z p q (syn_ccnv W) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0135 :=
    @g_sylibr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.all z (.all p (.all q (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p))
                (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q)))))
      (syn_wfun (syn_ccnv W)) p0133 p0134
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

@[expose]
noncomputable def g_enprmaplem4 (x : Var) (y : Var) (u : Var) (B : Class) (R : Class)
    (p : Var) (dv_B_u : u ∉ B.fv) (dv_p_u : p ≠ u) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (hyp_enprmaplem4_1 :
      Nominal.NPrf (.classEq R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))))
    (hyp_enprmaplem4_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem R (syn_cvv)) :=
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
      ((syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
            (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))).fv :=
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
      ((syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
            (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))).fv :=
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
  have dv_cache_0004 : z ∉ ((syn_cif (.objMem u p) (.cv x) (.cv y))).fv :=
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
    @g_elun (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
      (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))
  have p0001 := @g_opelxp (.cv u) (syn_csn (.cv z)) (.cv p) (syn_cpw1 (.cv x))
  have p0002 := @g_snelpw1 (.cv z) (.cv x)
  have p0003_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_anbi2i (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) (.objMem z x) (.objMem u p)
      p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
          (syn_cxp (.cv p) (syn_cpw1 (.cv x))))
        (syn_wa (.objMem u p) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_cxp syn_copab syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c
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
    @g_bitri
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x))))
      (syn_wa (.objMem u p) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))))
      (syn_wa (.objMem u p) (.objMem z x)) p0004_e00_recanon p0003
  have p0005 :=
    @g_opelxp (.cv u) (syn_csn (.cv z)) (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))
  have p0006 := @g_vex u
  have p0007 := @g_elcompl (.cv u) (.cv p) p0006
  have p0008 := @g_snelpw1 (.cv z) (.cv y)
  have p0009_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv u) (syn_ccompl (.cv p))) (.neg (.objMem u p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
      (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_anbi12i (.classMem (.cv u) (syn_ccompl (.cv p))) (.neg (.objMem u p))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y) p0009_e00_recanon
      p0009_e01_recanon
  have p0010 :=
    @g_bitri
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
        (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))
      (syn_wa (.classMem (.cv u) (syn_ccompl (.cv p)))
        (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))))
      (syn_wa (.neg (.objMem u p)) (.objMem z y)) p0005 p0009
  have p0011 :=
    @g_orbi12i
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x))))
      (syn_wa (.objMem u p) (.objMem z x))
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
        (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))
      (syn_wa (.neg (.objMem u p)) (.objMem z y)) p0004 p0010
  have p0012 :=
    @g_bitri
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
        (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
          (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))
      (syn_wo (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
          (syn_cxp (.cv p) (syn_cpw1 (.cv x)))) (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
          (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))
      (syn_wo (syn_wa (.objMem u p) (.objMem z x)) (syn_wa (.neg (.objMem u p)) (.objMem z y)))
      p0000 p0011
  have p0013 :=
    @g_opelcnv (syn_csn (.cv z)) (.cv u)
      (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
        (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))
  have p0014 := @g_elif (.objMem u p) (.cv z) (.cv x) (.cv y)
  have p0015_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y)))
        (syn_wo (syn_wa (.objMem u p) (.objMem z x))
          (syn_wa (.neg (.objMem u p)) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa
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
    @g_n_3bitr4i
      (.classMem (syn_cop (.cv u) (syn_csn (.cv z)))
        (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
          (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))
      (syn_wo (syn_wa (.objMem u p) (.objMem z x)) (syn_wa (.neg (.objMem u p)) (.objMem z y)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv u)) (syn_ccnv
          (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
            (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))))
      (.classMem (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y))) p0012 p0013
      p0015_e02_recanon
  have p0016 :=
    @g_releqmpt u z B
      (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
          (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))
      (syn_cif (.objMem u p) (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0015
  have p0017 :=
    @g_eqtr4i R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))
      (syn_cin (syn_cxp B (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_ccnv
                    (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
                      (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))))) (syn_c1c)))))
      hyp_enprmaplem4_1 p0016
  have p0018 := @g_vex p
  have p0019 := @g_vex x
  have p0020 := @g_pw1ex (.cv x) p0019
  have p0021 := @g_xpex (.cv p) (syn_cpw1 (.cv x)) p0018 p0020
  have p0022 := @g_complex (.cv p) p0018
  have p0023 := @g_vex y
  have p0024 := @g_pw1ex (.cv y) p0023
  have p0025 := @g_xpex (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)) p0022 p0024
  have p0026 :=
    @g_unex (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
      (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))) p0021 p0025
  have p0027 :=
    @g_cnvex
      (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
        (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))
      p0026
  have p0028 :=
    @g_mptexlem B
      (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
          (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))
      hyp_enprmaplem4_2 p0027
  have p0029 :=
    @g_eqeltri R
      (syn_cin (syn_cxp B (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_ccnv
                    (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x)))
                      (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))))) (syn_c1c)))))
      (syn_cvv) p0017 p0028
  exact p0029

@[expose]
noncomputable def g_enprmaplem5 (x : Var) (y : Var) (u : Var) (A : Class) (B : Class)
    (R : Class) (W : Class) (r : Var) (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_r : r ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_B_r : r ∉ B.fv) (dv_B_u : u ∉ B.fv)
    (dv_R_r : r ∉ R.fv) (dv_W_p : p ∉ W.fv) (dv_p_u : p ≠ u) (dv_p_x : p ≠ x)
    (dv_p_y : p ≠ y) (dv_r_x : r ≠ x) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (hyp_enprmaplem5_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))))
    (hyp_enprmaplem5_2 :
      Nominal.NPrf (.classEq R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))))
    (hyp_enprmaplem5_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wss (syn_cpw B) (syn_crn W))) :=
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
  have dv_cache_0001 : u ∉ ((Wff.classEq A (syn_cpr (.cv x) (.cv y)))).fv := by
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
  have dv_cache_0008 : r ∉ ((syn_cima (syn_ccnv R) (syn_csn (.cv x)))).fv :=
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
  have dv_cache_0009 : r ∉ ((syn_co A (syn_cmap) B)).fv :=
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
  have dv_cache_0011 : u ∉ ((syn_cif (.objMem z p) (.cv x) (.cv y))).fv :=
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
  have dv_cache_0012 : z ∉ ((syn_cima (syn_ccnv R) (syn_csn (.cv x)))).fv :=
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
      ((syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B))).fv :=
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
  have dv_cache_0017 : p ∉ ((syn_cpw B)).fv :=
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
  have dv_cache_0018 : p ∉ ((syn_crn W)).fv :=
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
    p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
  have p0000 := @g_vex p
  have p0001 := @g_elpw (.cv p) B p0000
  have p0002 := @g_ifeqor (.objMem u p) (.cv x) (.cv y)
  have p0003 := @g_vex x
  have p0004 := @g_vex y
  have p0005 := @g_ifex (.objMem u p) (.cv x) (.cv y) p0003 p0004
  have p0006 := @g_elpr (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv x) (.cv y) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cpr (.cv x) (.cv y)))
      (syn_wo (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv x))
        (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv y)))
      p0002 p0006
  have p0008 := @g_id (.classEq A (syn_cpr (.cv x) (.cv y)))
  have p0009 :=
    @g_syl5eleqr (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cpr (.cv x) (.cv y)) A p0007 p0008
  have p0010 :=
    @g_ralrimivw (.classEq A (syn_cpr (.cv x) (.cv y)))
      (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) A) u B dv_cache_0001 p0009
  have p0011 :=
    @g_fmpt u B A (syn_cif (.objMem u p) (.cv x) (.cv y)) R dv_cache_0002 dv_cache_0003
      hyp_enprmaplem5_2
  have p0012 :=
    @g_sylib (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wral u B (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) A)) (syn_wf R B A)
      p0010 p0011
  have p0013 := @g_prex (.cv x) (.cv y)
  have p0014 := @g_eleq1 A (syn_cpr (.cv x) (.cv y)) (syn_cvv)
  have p0015 :=
    @g_mpbiri (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (.classMem (syn_cpr (.cv x) (.cv y)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_enprmaplem4 x y u B R p dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_enprmaplem5_2 hyp_enprmaplem5_3
  have p0017 := @g_elmapg A B R (syn_cvv) (syn_cvv) (syn_cvv)
  have p0018 :=
    @g_mp3an23 (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem R (syn_cvv))
      (syn_wb (.classMem R (syn_co A (syn_cmap) B)) (syn_wf R B A)) hyp_enprmaplem5_3
      p0016 p0017
  have p0019 :=
    @g_syl (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (syn_wb (.classMem R (syn_co A (syn_cmap) B)) (syn_wf R B A)) p0015 p0018
  have p0020 :=
    @g_mpbird (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem R (syn_co A (syn_cmap) B))
      (syn_wf R B A) p0012 p0019
  have p0021 :=
    @g_n_3ad2ant2 (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wne (.cv x) (.cv y))
      (.classMem R (syn_co A (syn_cmap) B)) (syn_wss (.cv p) B) p0020
  have p0022 := @g_cnveq (.cv r) R
  have p0023 :=
    @g_imaeq1d (.classEq (.cv r) R) (syn_ccnv (.cv r)) (syn_ccnv R) (syn_csn (.cv x))
      p0022
  have p0024 := @g_cnvex R p0016
  have p0025 := @g_snex (.cv x)
  have p0026 := @g_imaex (syn_ccnv R) (syn_csn (.cv x)) p0024 p0025
  have p0027 :=
    @g_fvmpt r R (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W dv_cache_0007
      dv_cache_0008 dv_cache_0009 p0023 hyp_enprmaplem5_1 p0026
  have p0028 :=
    @g_syl
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.classMem R (syn_co A (syn_cmap) B))
      (.classEq (syn_cfv W R) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0021 p0027
  have p0029 := @g_eliniseg R (.cv x) (.cv z)
  have p0030 := @g_breldm (.cv z) (.cv x) R
  have p0031 :=
    @g_fnmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)) R (syn_cvv) dv_cache_0002
      hyp_enprmaplem5_2
  have p0032 :=
    @g_a1i (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cvv))
      (.classMem (.cv u) B) p0005
  have p0033 :=
    @g_mprg (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cvv)) (syn_wfn R B) u
      B p0031 p0032
  have p0034 := @g_fndm B R
  have p0035 := Nominal.mp p0033 p0034
  have p0036 := @g_syl6eleq (syn_wbr (.cv z) R (.cv x)) (.cv z) (syn_cdm R) B p0030 p0035
  have p0037 := @g_fnbrfvb B (.cv z) (.cv x) R
  have p0038 :=
    @g_mpan (syn_wfn R B) (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x))) p0033
      p0037
  have p0039 :=
    @g_biimprd (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x))
      (syn_wbr (.cv z) R (.cv x)) p0038
  have p0040 :=
    @g_com12 (.classMem (.cv z) B) (syn_wbr (.cv z) R (.cv x))
      (.classEq (syn_cfv R (.cv z)) (.cv x)) p0039
  have p0041 :=
    @g_jcai (syn_wbr (.cv z) R (.cv x)) (.classMem (.cv z) B)
      (.classEq (syn_cfv R (.cv z)) (.cv x)) p0036 p0040
  have p0042 := @g_eleq1 (.cv u) (.cv z) (.cv p)
  have p0043_e00_recanon :
    Nominal.NPrf (.imp (.objEq u z) (syn_wb (.objMem u p) (.objMem z p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_ifbid (.objEq u z) (.objMem u p) (.objMem z p) (.cv x) (.cv y) p0043_e00_recanon
  have p0044 := @g_ifex (.objMem z p) (.cv x) (.cv y) p0003 p0004
  have p0045_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv u) (.cv z)) (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y))
          (syn_cif (.objMem z p) (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cif syn_wo syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0045 :=
    @g_fvmpt u (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y))
      (syn_cif (.objMem z p) (.cv x) (.cv y)) B R dv_cache_0010 dv_cache_0011
      dv_cache_0002 p0045_e00_recanon hyp_enprmaplem5_2 p0044
  have p0046 :=
    @g_eqeq1d (.classMem (.cv z) B) (syn_cfv R (.cv z))
      (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0045
  have p0047 :=
    @g_biimpd (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x))
      (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0046
  have p0048 :=
    @g_imp (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x))
      (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0047
  have p0049 :=
    @g_simpl1 (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wss (.cv p) B) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))
  have p0050 := (Nominal.biimpRefl (syn_wne (.cv x) (.cv y)))
  have p0051_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wne (.cv x) (.cv y)) (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne
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
    @g_sylib
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)))
      (syn_wne (.cv x) (.cv y)) (.neg (.objEq x y)) p0049 p0051_e01_recanon
  have p0052 := @g_iffalse (.objMem z p) (.cv x) (.cv y)
  have p0053 :=
    @g_eqeq2d (.neg (.objMem z p)) (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv y) (.cv x)
      p0052
  have p0054_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem z p))
        (syn_wb (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa
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
    @g_biimpd (.neg (.objMem z p))
      (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y)
      p0054_e00_recanon
  have p0055 :=
    @g_com12 (.neg (.objMem z p))
      (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y) p0054
  have p0056 :=
    @g_eqcoms (.imp (.neg (.objMem z p)) (.objEq x y)) (.cv x)
      (syn_cif (.objMem z p) (.cv x) (.cv y)) p0055
  have p0057 :=
    @g_adantl (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (.imp (.neg (.objMem z p)) (.objEq x y))
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      p0056
  have p0058 :=
    @g_mt3d
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)))
      (.objMem z p) (.objEq x y) p0051 p0057
  have p0059 :=
    @g_ex
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (.objMem z p) p0058
  have p0060 :=
    @g_syl5 (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)))
      (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.objMem z p) p0048 p0059
  have p0061 :=
    @g_syl5 (syn_wbr (.cv z) R (.cv x))
      (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)))
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.objMem z p) p0041 p0060
  have p0062 := @g_ssel2 (.cv p) B (.cv z)
  have p0063_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss (.cv p) B) (.objMem z p)) (.classMem (.cv z) B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
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
    @g_n_3ad2antl3 (syn_wss (.cv p) B) (syn_wne (.cv x) (.cv y)) (.objMem z p)
      (.classMem (.cv z) B) (.classEq A (syn_cpr (.cv x) (.cv y))) p0063_e00_recanon
  have p0064 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.objMem z p))
      (.classMem (.cv z) B)
      (.classEq (syn_cfv R (.cv z)) (syn_cif (.objMem z p) (.cv x) (.cv y))) p0063 p0045
  have p0065 := @g_iftrue (.objMem z p) (.cv x) (.cv y)
  have p0066 :=
    @g_adantl (.objMem z p) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      p0065
  have p0067 :=
    @g_eqtrd
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.objMem z p))
      (syn_cfv R (.cv z)) (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0064 p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.objMem z p))
      (.classMem (.cv z) B)
      (syn_wb (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x))) p0063
      p0038
  have p0069 :=
    @g_mpbid
      (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B)) (.objMem z p))
      (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x)) p0067 p0068
  have p0070 :=
    @g_ex
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.objMem z p) (syn_wbr (.cv z) R (.cv x)) p0069
  have p0071 :=
    @g_impbid
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (syn_wbr (.cv z) R (.cv x)) (.objMem z p) p0061 p0070
  have p0072 :=
    @g_syl5bb (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
      (syn_wbr (.cv z) R (.cv x))
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.objMem z p) p0029 p0071
  have p0073_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
          (syn_wss (.cv p) B))
        (syn_wb (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
          (.classMem (.cv z) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wne syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
          syn_wss syn_cin syn_wb syn_cima syn_wrex syn_wex syn_wbr syn_cop syn_ccnv
          syn_copab
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
    @g_eqrdv
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      z (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (.cv p) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0073_e00_recanon
  have p0074 :=
    @g_eqtrd
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (syn_cfv W R) (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (.cv p) p0028 p0073
  have p0075 := @g_enprmaplem2 x A B W r dv_cache_0015 dv_cache_0016 hyp_enprmaplem5_1
  have p0076 := @g_fnbrfvb (syn_co A (syn_cmap) B) R (.cv p) W
  have p0077 :=
    @g_mpan (syn_wfn W (syn_co A (syn_cmap) B)) (.classMem R (syn_co A (syn_cmap) B))
      (syn_wb (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p))) p0075 p0076
  have p0078 :=
    @g_syl
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.classMem R (syn_co A (syn_cmap) B))
      (syn_wb (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p))) p0021 p0077
  have p0079 :=
    @g_mpbid
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (syn_wss (.cv p) B))
      (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p)) p0074 p0078
  have p0080 :=
    @g_n_3expia (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (syn_wss (.cv p) B) (syn_wbr R W (.cv p)) p0079
  have p0081 := @g_brelrn R (.cv p) W
  have p0082 :=
    @g_syl6 (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wss (.cv p) B) (syn_wbr R W (.cv p)) (.classMem (.cv p) (syn_crn W)) p0080
      p0081
  have p0083 :=
    @g_syl5bi (.classMem (.cv p) (syn_cpw B)) (syn_wss (.cv p) B)
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.classMem (.cv p) (syn_crn W)) p0001 p0082
  have p0084 :=
    @g_ssrdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p
      (syn_cpw B) (syn_crn W) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0083
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

@[expose]
noncomputable def g_enprmaplem6 (x : Var) (y : Var) (A : Class) (B : Class) (W : Class)
    (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y)
    (hyp_enprmaplem6_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))))
    (hyp_enprmaplem6_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (.classEq (syn_crn W) (syn_cpw B))) :=
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
  have dv_cache_0004 : r ∉ ((syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x)))).fv :=
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
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv :=
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
  have dv_cache_0006 : s ∉ ((syn_wss (.cv p) B)).fv :=
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
    s ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
  have dv_cache_0010 : p ∉ ((syn_crn W)).fv :=
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
  have dv_cache_0011 : p ∉ ((syn_cpw B)).fv :=
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
    p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv :=
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
  have dv_cache_0017 : r ∉ ((syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))).fv :=
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
  have p0000 := @g_breldm (.cv s) (.cv p) W
  have p0001 := @g_enprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem6_1
  have p0002 := @g_fndm (syn_co A (syn_cmap) B) W
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6eleq (syn_wbr (.cv s) W (.cv p)) (.cv s) (syn_cdm W) (syn_co A (syn_cmap) B)
      p0000 p0003
  have p0005 := @g_fnbrfvb (syn_co A (syn_cmap) B) (.cv s) (.cv p) W
  have p0006 :=
    @g_sylancr (syn_wbr (.cv s) W (.cv p)) (syn_wfn W (syn_co A (syn_cmap) B))
      (.classMem (.cv s) (syn_co A (syn_cmap) B))
      (syn_wb (.classEq (syn_cfv W (.cv s)) (.cv p)) (syn_wbr (.cv s) W (.cv p))) p0001
      p0004 p0005
  have p0007 :=
    @g_ibir (syn_wbr (.cv s) W (.cv p)) (.classEq (syn_cfv W (.cv s)) (.cv p)) p0006
  have p0008 :=
    @g_jca (syn_wbr (.cv s) W (.cv p)) (.classMem (.cv s) (syn_co A (syn_cmap) B))
      (.classEq (syn_cfv W (.cv s)) (.cv p)) p0004 p0007
  have p0009 := @g_cnveq (.cv r) (.cv s)
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.objEq r s) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_imaeq1d (.objEq r s) (syn_ccnv (.cv r)) (syn_ccnv (.cv s)) (syn_csn (.cv x))
      p0010_e00_recanon
  have p0011 := @g_vex s
  have p0012 := @g_cnvex (.cv s) p0011
  have p0013 := @g_snex (.cv x)
  have p0014 := @g_imaex (syn_ccnv (.cv s)) (syn_csn (.cv x)) p0012 p0013
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (.cv s)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
          (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_ccnv syn_copab syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0015 :=
    @g_fvmpt r (.cv s) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0015_e00_recanon hyp_enprmaplem6_1 p0014
  have p0016 :=
    @g_eqeq1d (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_cfv W (.cv s))
      (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p) p0015
  have p0017 :=
    @g_n_3ad2ant3 (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wne (.cv x) (.cv y))
      (syn_wb (.classEq (syn_cfv W (.cv s)) (.cv p))
        (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p)))
      (.classEq A (syn_cpr (.cv x) (.cv y))) p0016
  have p0018 := @g_imassrn (syn_ccnv (.cv s)) (syn_csn (.cv x))
  have p0019 := (Nominal.classEqRefl (syn_cdm (.cv s)))
  have p0020 := @g_elmapi (.cv s) A B
  have p0021 := @g_fdm B A (.cv s)
  have p0022 := @g_eqimss (syn_cdm (.cv s)) B
  have p0023 :=
    @g_n_3syl (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wf (.cv s) B A)
      (.classEq (syn_cdm (.cv s)) B) (syn_wss (syn_cdm (.cv s)) B) p0020 p0021 p0022
  have p0024 :=
    @g_syl5eqssr (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_crn (syn_ccnv (.cv s)))
      (syn_cdm (.cv s)) B p0019 p0023
  have p0025 :=
    @g_syl5ss (.classMem (.cv s) (syn_co A (syn_cmap) B))
      (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (syn_crn (syn_ccnv (.cv s))) B p0018
      p0024
  have p0026 :=
    @g_n_3ad2ant3 (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wne (.cv x) (.cv y))
      (syn_wss (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) B)
      (.classEq A (syn_cpr (.cv x) (.cv y))) p0025
  have p0027 := @g_sseq1 (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p) B
  have p0028 :=
    @g_syl5ibcom
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (.classMem (.cv s) (syn_co A (syn_cmap) B)))
      (syn_wss (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) B)
      (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p))
      (syn_wss (.cv p) B) p0026 p0027
  have p0029 :=
    @g_sylbid
      (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
        (.classMem (.cv s) (syn_co A (syn_cmap) B)))
      (.classEq (syn_cfv W (.cv s)) (.cv p))
      (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p))
      (syn_wss (.cv p) B) p0017 p0028
  have p0030 :=
    @g_n_3expia (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))
      (.classMem (.cv s) (syn_co A (syn_cmap) B))
      (.imp (.classEq (syn_cfv W (.cv s)) (.cv p)) (syn_wss (.cv p) B)) p0029
  have p0031 :=
    @g_imp3a (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (.classMem (.cv s) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv s)) (.cv p))
      (syn_wss (.cv p) B) p0030
  have p0032 :=
    @g_syl5 (syn_wbr (.cv s) W (.cv p))
      (syn_wa (.classMem (.cv s) (syn_co A (syn_cmap) B))
        (.classEq (syn_cfv W (.cv s)) (.cv p)))
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wss (.cv p) B) p0008 p0031
  have p0033 :=
    @g_exlimdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wbr (.cv s) W (.cv p)) (syn_wss (.cv p) B) s dv_cache_0006 dv_cache_0007 p0032
  have p0034 := @g_elrn s (.cv p) W dv_cache_0008 dv_cache_0009
  have p0035 := @g_vex p
  have p0036 := @g_elpw (.cv p) B p0035
  have p0037 :=
    @g_n_3imtr4g (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wex s (syn_wbr (.cv s) W (.cv p))) (syn_wss (.cv p) B)
      (.classMem (.cv p) (syn_crn W)) (.classMem (.cv p) (syn_cpw B)) p0033 p0034 p0036
  have p0038 :=
    @g_ssrdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p
      (syn_crn W) (syn_cpw B) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0037
  have p0039 := @g_eqid (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))
  have p0040 :=
    @g_enprmaplem5 x y u A B (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y))) W r p
      dv_cache_0013 dv_cache_0001 dv_cache_0014 dv_cache_0015 dv_cache_0002 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 hyp_enprmaplem6_1 p0039 hyp_enprmaplem6_2
  have p0041 :=
    @g_eqssd (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_crn W) (syn_cpw B) p0038 p0040
  exact p0041

@[expose]
noncomputable def g_enprmap (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_enprmap_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
        (syn_wbr (syn_co A (syn_cmap) B) (syn_cen) (syn_cpw B))) :=
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
    @g_eqid
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
  have p0001 :=
    @g_enprmaplem2 x A B
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      r dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_a1i
      (syn_wfn (syn_cmpt r (syn_co A (syn_cmap) B)
          (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B))
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p0001
  have p0003 :=
    @g_enprmaplem3 x y A B
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0004 :=
    @g_enprmaplem6 x y A B
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 hyp_enprmap_1
  have p0005 :=
    @g_dff1o2 (syn_co A (syn_cmap) B) (syn_cpw B)
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
  have p0006 :=
    @g_syl3anbrc (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wfn (syn_cmpt r (syn_co A (syn_cmap) B)
          (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B))
      (syn_wfun (syn_ccnv (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))))
      (.classEq (syn_crn (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))) (syn_cpw B))
      (syn_wf1o (syn_cmpt r (syn_co A (syn_cmap) B)
          (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B) (syn_cpw B))
      p0002 p0003 p0004 p0005
  have p0007 :=
    @g_enprmaplem1 x A B
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0008 :=
    @g_f1oen (syn_co A (syn_cmap) B) (syn_cpw B)
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))
      (syn_wf1o (syn_cmpt r (syn_co A (syn_cmap) B)
          (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B) (syn_cpw B))
      (syn_wbr (syn_co A (syn_cmap) B) (syn_cen) (syn_cpw B)) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_enprmapc (A : Class) (B : Class) (C : Class) (P : Class)
    (hyp_enprmapc_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_enprmapc_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_enprmapc_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B)))
        (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) :=
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
      ((Wff.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B)))
          (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))).fv :=
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
      ((Wff.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B)))
          (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))).fv :=
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
  have p0000 := @g_neeq1 (.cv x) A B
  have p0001 := @g_preq1 (.cv x) A B
  have p0002 := @g_eqeq2d (.classEq (.cv x) A) (syn_cpr (.cv x) B) (syn_cpr A B) P p0001
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wne (.cv x) B) (syn_wne A B)
      (.classEq P (syn_cpr (.cv x) B)) (.classEq P (syn_cpr A B)) p0000 p0002
  have p0004 :=
    @g_imbi1d (.classEq (.cv x) A)
      (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B)))
      (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B)))
      (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)) p0003
  have p0005 := @g_neeq2 (.cv y) B (.cv x)
  have p0006 := @g_preq2 (.cv y) B (.cv x)
  have p0007 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cpr (.cv x) (.cv y)) (syn_cpr (.cv x) B) P p0006
  have p0008 :=
    @g_anbi12d (.classEq (.cv y) B) (syn_wne (.cv x) (.cv y)) (syn_wne (.cv x) B)
      (.classEq P (syn_cpr (.cv x) (.cv y))) (.classEq P (syn_cpr (.cv x) B)) p0005 p0007
  have p0009 :=
    @g_imbi1d (.classEq (.cv y) B)
      (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq P (syn_cpr (.cv x) (.cv y))))
      (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B)))
      (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)) p0008
  have p0010 := @g_enprmap x y P C hyp_enprmapc_3
  have p0011 :=
    @g_vtocl
      (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq P (syn_cpr (.cv x) (.cv y))))
        (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))
      (.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B)))
        (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))
      y B dv_cache_0001 dv_cache_0002 hyp_enprmapc_2 p0009 p0010
  have p0012 :=
    @g_vtocl
      (.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B)))
        (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))
      (.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B)))
        (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))
      x A dv_cache_0003 dv_cache_0004 hyp_enprmapc_1 p0004 p0011
  exact p0012

@[expose]
noncomputable def g_enpw (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B))) :=
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
      ((Wff.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)))).fv :=
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
      ((Wff.imp (syn_wbr A (syn_cen) (.cv b))
          (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))))).fv :=
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
  have p0000 := @g_brex A B (syn_cen)
  have p0001 := @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0002 := @g_pweq (.cv a) A
  have p0003 :=
    @g_breq1d (.classEq (.cv a) A) (syn_cpw (.cv a)) (syn_cpw A) (syn_cpw (.cv b))
      (syn_cen) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr A (syn_cen) (.cv b))
      (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b)))
      (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))) p0001 p0003
  have p0005 := @g_breq2 (.cv b) B A (syn_cen)
  have p0006 := @g_pweq (.cv b) B
  have p0007 :=
    @g_breq2d (.classEq (.cv b) B) (syn_cpw (.cv b)) (syn_cpw B) (syn_cpw A) (syn_cen)
      p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B)
      (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b)))
      (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)) p0005 p0007
  have p0009 := @g_enmap2 (.cv a) (.cv b) (syn_cpr (syn_cvv) (syn_c0))
  have p0010 := @g_vn0
  have p0011 := @g_eqid (syn_cpr (syn_cvv) (syn_c0))
  have p0012 := @g_vvex
  have p0013 := @g_n_0ex
  have p0014 := @g_vex a
  have p0015 :=
    @g_enprmapc (syn_cvv) (syn_c0) (.cv a) (syn_cpr (syn_cvv) (syn_c0)) p0012 p0013 p0014
  have p0016 :=
    @g_mp2an (syn_wne (syn_cvv) (syn_c0))
      (.classEq (syn_cpr (syn_cvv) (syn_c0)) (syn_cpr (syn_cvv) (syn_c0)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_cpw (.cv a)))
      p0010 p0011 p0015
  have p0017 :=
    @g_ensym (syn_cpw (.cv a)) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))
  have p0018 :=
    @g_mpbir
      (syn_wbr (syn_cpw (.cv a)) (syn_cen)
        (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_cpw (.cv a)))
      p0016 p0017
  have p0022 := @g_vex b
  have p0023 :=
    @g_enprmapc (syn_cvv) (syn_c0) (.cv b) (syn_cpr (syn_cvv) (syn_c0)) p0012 p0013 p0022
  have p0024 :=
    @g_mp2an (syn_wne (syn_cvv) (syn_c0))
      (.classEq (syn_cpr (syn_cvv) (syn_c0)) (syn_cpr (syn_cvv) (syn_c0)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cen)
        (syn_cpw (.cv b)))
      p0010 p0011 p0023
  have p0025 :=
    @g_entr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))
      (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cpw (.cv b))
  have p0026 :=
    @g_mpan2
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cen)
        (syn_cpw (.cv b)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_cpw (.cv b)))
      p0024 p0025
  have p0027 :=
    @g_entr (syn_cpw (.cv a)) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))
      (syn_cpw (.cv b))
  have p0028 :=
    @g_sylancr
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)))
      (syn_wbr (syn_cpw (.cv a)) (syn_cen)
        (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_cpw (.cv b)))
      (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))) p0018 p0026 p0027
  have p0029 :=
    @g_syl (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen)
        (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)))
      (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))) p0009 p0028
  have p0030 :=
    @g_vtocl2g
      (.imp (syn_wbr (.cv a) (syn_cen) (.cv b))
        (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))))
      (.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))))
      (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B))) a b A B
      (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0004 p0008 p0029
  have p0031 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)) p0000 p0030
  exact p0031

@[expose]
noncomputable def g_nceq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cnc A) (syn_cnc B))) :=
  by
  have p0000 := @g_eceq1 A B (syn_cen)
  have p0001 := (Nominal.classEqRefl (syn_cnc A))
  have p0002 := (Nominal.classEqRefl (syn_cnc B))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cec A (syn_cen)) (syn_cec B (syn_cen)) (syn_cnc A)
      (syn_cnc B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_nceqi (A : Class) (B : Class)
    (hyp_nceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cnc A) (syn_cnc B)) :=
  by
  have p0000 := @g_nceq A B
  have p0001 := Nominal.mp hyp_nceqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_nceqd (ph : Wff) (A : Class) (B : Class)
    (hyp_nceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cnc A) (syn_cnc B))) :=
  by
  have p0000 := @g_nceq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cnc A) (syn_cnc B)) hyp_nceqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_ncsex : Nominal.NPrf (.classMem (syn_cncs) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cncs))
  have p0001 := @g_enex
  have p0002 := @g_vvex
  have p0003 := @g_qsex (syn_cvv) (syn_cen) p0001 p0002
  have p0004 := @g_eqeltri (syn_cncs) (syn_cqs (syn_cvv) (syn_cen)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_brlecg (x : Var) (y : Var) (A : Class) (B : Class) (V : Class)
    (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wbr A (syn_clec) B)
          (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y)))))) :=
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
  have dv_cache_0016 : a ∉ ((syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))).fv :=
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
  have dv_cache_0017 : b ∉ ((syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))).fv :=
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
    @g_rexeq (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))) x (.cv a) A dv_cache_0001
      dv_cache_0002
  have p0001 := @g_rexeq (syn_wss (.cv x) (.cv y)) y (.cv b) B dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_rexbidv (.classEq (.cv b) B) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))
      (syn_wrex y B (syn_wss (.cv x) (.cv y))) x A dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lec x y a b
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    @g_brabg (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))))
      (syn_wrex x A (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))))
      (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y)))) a b A B V W (syn_clec)
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

@[expose]
noncomputable def g_brlec (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_brlec_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brlec_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_clec) B)
        (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))) :=
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
    @g_brlecg x y A B (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y)))))
      hyp_brlec_1 hyp_brlec_2 p0000
  exact p0001

@[expose]
noncomputable def g_brltc (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cltc) B) (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B))) :=
  by
  have p0000 := @g_brex A B (syn_cltc)
  have p0001 :=
    @g_simprd (syn_wbr A (syn_cltc) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      p0000
  have p0002 := @g_brex A B (syn_clec)
  have p0003 :=
    @g_simprd (syn_wbr A (syn_clec) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      p0002
  have p0004 :=
    @g_adantr (syn_wbr A (syn_clec) B) (.classMem B (syn_cvv)) (syn_wne A B) p0003
  have p0005 := (Nominal.classEqRefl (syn_cltc))
  have p0006 := @g_breqi A B (syn_cltc) (syn_cdif (syn_clec) (syn_cid)) p0005
  have p0007 := @g_brdif A B (syn_clec) (syn_cid)
  have p0008 :=
    @g_bitri (syn_wbr A (syn_cltc) B) (syn_wbr A (syn_cdif (syn_clec) (syn_cid)) B)
      (syn_wa (syn_wbr A (syn_clec) B) (.neg (syn_wbr A (syn_cid) B))) p0006 p0007
  have p0009 := @g_ideqg A B (syn_cvv)
  have p0010 := @g_necon3bbid (.classMem B (syn_cvv)) (syn_wbr A (syn_cid) B) A B p0009
  have p0011 :=
    @g_anbi2d (.classMem B (syn_cvv)) (.neg (syn_wbr A (syn_cid) B)) (syn_wne A B)
      (syn_wbr A (syn_clec) B) p0010
  have p0012 :=
    @g_syl5bb (syn_wbr A (syn_cltc) B)
      (syn_wa (syn_wbr A (syn_clec) B) (.neg (syn_wbr A (syn_cid) B)))
      (.classMem B (syn_cvv)) (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B)) p0008 p0011
  have p0013 :=
    @g_pm5_21nii (syn_wbr A (syn_cltc) B) (.classMem B (syn_cvv))
      (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B)) p0001 p0004 p0012
  exact p0013

@[expose]
noncomputable def g_lecex : Nominal.NPrf (.classMem (syn_clec) (syn_cvv)) :=
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
  have dv_cache_0003 : t ∉ ((syn_wss (.cv x) (.cv y))).fv :=
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
  have dv_cache_0004 : u ∉ ((syn_wss (.cv x) (.cv y))).fv :=
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
  have dv_cache_0005 : t ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0006 : u ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_csn (.cv y))).fv :=
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
  have dv_cache_0008 : u ∉ ((syn_csn (.cv y))).fv :=
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
      ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
          (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))).fv :=
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
      ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
  have dv_cache_0017 : t ∉ ((syn_ccom (syn_csset) (syn_csi (syn_csset)))).fv :=
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
  have dv_cache_0018 : t ∉ ((syn_ccnv (syn_csset))).fv :=
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
  have dv_cache_0021 : u ∉ ((syn_csset)).fv :=
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
  have dv_cache_0022 : u ∉ ((syn_csi (syn_csset))).fv :=
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
  have dv_cache_0027 : x ∉ ((syn_csset)).fv :=
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
  have dv_cache_0028 : y ∉ ((syn_csset)).fv :=
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
  have dv_cache_0029 : u ∉ ((syn_wbr (.cv t) (syn_csset) (.cv a))).fv :=
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
      ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
      ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
  have dv_cache_0032 : a ∉ ((syn_clec)).fv :=
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
  have dv_cache_0033 : b ∉ ((syn_clec)).fv :=
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
      ((syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))).fv :=
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
      ((syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))).fv :=
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
    @g_r2ex (syn_wss (.cv x) (.cv y)) x y (.cv a) (.cv b) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_19_41vv
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_wss (.cv x) (.cv y)) t u dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anass
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
      (syn_wss (.cv x) (.cv y))
  have p0003 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
            (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wss (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
          (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
          (syn_wss (.cv x) (.cv y))))
      t u p0002
  have p0004 :=
    @g_ancom
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
  have p0005 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))))
  have p0006 :=
    @g_bitr4i
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      p0004 p0005
  have p0007 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      t u p0006
  have p0008 := @g_snex (.cv x)
  have p0009 := @g_snex (.cv y)
  have p0010 := @g_breq1 (.cv t) (syn_csn (.cv x)) (.cv a) (syn_csset)
  have p0011 :=
    @g_anbi1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
      (syn_wbr (.cv u) (syn_csset) (.cv b)) p0010
  have p0012 := @g_breq1 (.cv u) (syn_csn (.cv y)) (.cv b) (syn_csset)
  have p0013 :=
    @g_anbi2d (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv u) (syn_csset) (.cv b))
      (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b))
      (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) p0012
  have p0014 :=
    @g_ceqsex2v
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))
      t u (syn_csn (.cv x)) (syn_csn (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008 p0009 p0011 p0013
  have p0015 := @g_vex x
  have p0016 := @g_vex a
  have p0017 := @g_brssetsn (.cv x) (.cv a) p0015 p0016
  have p0018 := @g_vex y
  have p0019 := @g_vex b
  have p0020 := @g_brssetsn (.cv y) (.cv b) p0018 p0019
  have p0021_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (.objMem x a)
      (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (.objMem y b) p0021_e00_recanon
      p0021_e01_recanon
  have p0022 :=
    @g_n_3bitri
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b)))
            (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))))))
      (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))))))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))
      (syn_wa (.objMem x a) (.objMem y b)) p0007 p0014 p0021
  have p0023 :=
    @g_anbi1i
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b)))
            (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))))))
      (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y)) p0022
  have p0024 :=
    @g_n_3bitr3i
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b)))
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wss (.cv x) (.cv y)))))
      (syn_wa (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b)))
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                (.classEq (.cv u) (syn_csn (.cv y))))))) (syn_wss (.cv x) (.cv y)))
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y))) p0001 p0003
      p0023
  have p0025 :=
    @g_n_2exbii
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y))) x y p0024
  have p0026_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wex x
          (syn_wex y
            (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))))
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y)))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      p0026_e00_recanon p0025
  have p0027 :=
    @g_brlec x y (.cv a) (.cv b) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0002
      p0016 p0019
  have p0028 :=
    @g_brco t (.cv a) (.cv b) (syn_ccom (syn_csset) (syn_csi (syn_csset)))
      (syn_ccnv (syn_csset)) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0029 := @g_brcnv (.cv a) (.cv t) (syn_csset)
  have p0030 :=
    @g_brco u (.cv t) (.cv b) (syn_csset) (syn_csi (syn_csset)) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0031 :=
    @g_brsi x y (.cv t) (.cv u) (syn_csset) dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0002
  have p0032 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wbr (.cv x) (syn_csset) (.cv y))))
  have p0033 := @g_brsset (.cv x) (.cv y) p0015 p0018
  have p0034 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_csset) (.cv y)) (syn_wss (.cv x) (.cv y))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
      p0033
  have p0035 :=
    @g_bitri
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wbr (.cv x) (syn_csset) (.cv y)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wbr (.cv x) (syn_csset) (.cv y)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wss (.cv x) (.cv y)))
      p0032 p0034
  have p0036 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wbr (.cv x) (syn_csset) (.cv y)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wss (.cv x) (.cv y)))
      x y p0035
  have p0037 :=
    @g_bitri (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) (syn_csset) (.cv y)))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))
      p0031 p0036
  have p0038 :=
    @g_anbi2ci (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))
      (syn_wbr (.cv u) (syn_csset) (.cv b)) p0037
  have p0039 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u))
        (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      u p0038
  have p0040 :=
    @g_bitri (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b))
      (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u))
          (syn_wbr (.cv u) (syn_csset) (.cv b))))
      (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      p0030 p0039
  have p0041 :=
    @g_anbi12i (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
      (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b))
      (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      p0029 p0040
  have p0042 :=
    @g_n_19_42v (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      u dv_cache_0029
  have p0043 :=
    @g_n_19_42vv
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wss (.cv x) (.cv y)))
      x y dv_cache_0030 dv_cache_0031
  have p0044 :=
    @g_anass (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))
  have p0045 :=
    @g_bitr2i
      (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
        (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      p0043 p0044
  have p0046 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
        (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wss (.cv x) (.cv y))))))
      u p0045
  have p0047 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
        (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b)))
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wex u
          (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      p0041 p0042 p0046
  have p0048 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
        (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b)))
      (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))
      t p0047
  have p0049 :=
    @g_exrot4
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
          (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
          (syn_wss (.cv x) (.cv y))))
      t u x y
  have p0050 :=
    @g_n_3bitri
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) (.cv b))
      (syn_wex t (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
          (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b))))
      (syn_wex t (syn_wex u (syn_wex x (syn_wex y (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      p0028 p0048 p0049
  have p0051 :=
    @g_n_3bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))))
      (syn_wbr (.cv a) (syn_clec) (.cv b))
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) (.cv b))
      p0026 p0027 p0050
  have p0052 :=
    @g_eqbrriv a b (syn_clec)
      (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0051
  have p0053 := @g_ssetex
  have p0055 := @g_siex (syn_csset) p0053
  have p0056 := @g_coex (syn_csset) (syn_csi (syn_csset)) p0053 p0055
  have p0058 := @g_cnvex (syn_csset) p0053
  have p0059 :=
    @g_coex (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)) p0056
      p0058
  have p0060 :=
    @g_eqeltri (syn_clec)
      (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))
      (syn_cvv) p0052 p0059
  exact p0060

@[expose]
noncomputable def g_ltcex : Nominal.NPrf (.classMem (syn_cltc) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cltc))
  have p0001 := @g_lecex
  have p0002 := @g_idex
  have p0003 := @g_difex (syn_clec) (syn_cid) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cltc) (syn_cdif (syn_clec) (syn_cid)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_ncex (A : Class) : Nominal.NPrf (.classMem (syn_cnc A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cnc A))
  have p0001 := @g_enex
  have p0002 := @g_ecexg A (syn_cvv) (syn_cen)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_eqeltri (syn_cnc A) (syn_cec A (syn_cen)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nulnnc : Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cncs))) :=
  by
  have p0000 := @g_eqid (syn_c0)
  have p0001 := @g_dmen
  have p0002 := @g_elqsn0 (syn_cvv) (syn_c0) (syn_cen)
  have p0003 :=
    @g_mpan (.classEq (syn_cdm (syn_cen)) (syn_cvv))
      (.classMem (syn_c0) (syn_cqs (syn_cvv) (syn_cen))) (syn_wne (syn_c0) (syn_c0)) p0001
      p0002
  have p0004 := (Nominal.classEqRefl (syn_cncs))
  have p0005 :=
    @g_eleq2s (syn_wne (syn_c0) (syn_c0)) (syn_c0) (syn_cqs (syn_cvv) (syn_cen))
      (syn_cncs) p0003 p0004
  have p0006 := @g_necon2bi (.classMem (syn_c0) (syn_cncs)) (syn_c0) (syn_c0) p0005
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

@[expose]
noncomputable def g_elncs (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))) :=
  by
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cen)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cncs))
  have p0001 := @g_eleq2i (syn_cncs) (syn_cqs (syn_cvv) (syn_cen)) A p0000
  have p0002 := @g_elex A (syn_cqs (syn_cvv) (syn_cen))
  have p0003 := @g_ncex (.cv x)
  have p0004 := @g_eleq1 A (syn_cnc (.cv x)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cnc (.cv x))) (.classMem A (syn_cvv))
      (.classMem (syn_cnc (.cv x)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv x))) (.classMem A (syn_cvv)) x dv_cache_0001
      p0005
  have p0007 :=
    @g_elqsg x (syn_cvv) A (syn_cen) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 := (Nominal.classEqRefl (syn_cnc (.cv x)))
  have p0009 := @g_eqeq2i (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen)) A p0008
  have p0010 :=
    @g_exbii (.classEq A (syn_cnc (.cv x))) (.classEq A (syn_cec (.cv x) (syn_cen))) x
      p0009
  have p0011 := @g_rexv (.classEq A (syn_cec (.cv x) (syn_cen))) x
  have p0012 :=
    @g_bitr4i (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (syn_wex x (.classEq A (syn_cec (.cv x) (syn_cen))))
      (syn_wrex x (syn_cvv) (.classEq A (syn_cec (.cv x) (syn_cen)))) p0010 p0011
  have p0013 :=
    @g_syl6bbr (.classMem A (syn_cvv)) (.classMem A (syn_cqs (syn_cvv) (syn_cen)))
      (syn_wrex x (syn_cvv) (.classEq A (syn_cec (.cv x) (syn_cen))))
      (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0007 p0012
  have p0014 :=
    @g_pm5_21nii (.classMem A (syn_cqs (syn_cvv) (syn_cen))) (.classMem A (syn_cvv))
      (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0002 p0006 p0013
  have p0015 :=
    @g_bitri (.classMem A (syn_cncs)) (.classMem A (syn_cqs (syn_cvv) (syn_cen)))
      (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0001 p0014
  exact p0015

@[expose]
noncomputable def g_ncelncs (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cnc A) (syn_cncs))) :=
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
  have dv_cache_0002 : x ∉ ((syn_cnc A)).fv :=
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
  have p0000 := @g_elisset x A V dv_cache_0001
  have p0001 := @g_nceq A (.cv x)
  have p0002 := @g_eqcoms (.classEq (syn_cnc A) (syn_cnc (.cv x))) A (.cv x) p0001
  have p0003 :=
    @g_eximi (.classEq (.cv x) A) (.classEq (syn_cnc A) (syn_cnc (.cv x))) x p0002
  have p0004 :=
    @g_syl (.classMem A V) (syn_wex x (.classEq (.cv x) A))
      (syn_wex x (.classEq (syn_cnc A) (syn_cnc (.cv x)))) p0000 p0003
  have p0005 := @g_elncs x (syn_cnc A) dv_cache_0002
  have p0006 :=
    @g_sylibr (.classMem A V) (syn_wex x (.classEq (syn_cnc A) (syn_cnc (.cv x))))
      (.classMem (syn_cnc A) (syn_cncs)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_ncelncsi (A : Class)
    (hyp_ncelncsi_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cnc A) (syn_cncs)) :=
  by
  have p0000 := @g_ncelncs A (syn_cvv)
  have p0001 := Nominal.mp hyp_ncelncsi_1 p0000
  exact p0001

@[expose]
noncomputable def g_ncidg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_cnc A))) :=
  by
  have p0000 := @g_enrflxg A V
  have p0001 := @g_elec A A (syn_cen)
  have p0002 :=
    @g_sylibr (.classMem A V) (syn_wbr A (syn_cen) A) (.classMem A (syn_cec A (syn_cen)))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cnc A))
  have p0004 :=
    @g_syl6eleqr (.classMem A V) A (syn_cec A (syn_cen)) (syn_cnc A) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_ncid (A : Class) (hyp_ncid_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_cnc A)) :=
  by
  have p0000 := @g_ncidg A (syn_cvv)
  have p0001 := Nominal.mp hyp_ncid_1 p0000
  exact p0001

@[expose]
noncomputable def g_elnc (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cnc B)) (syn_wbr A (syn_cen) B)) :=
  by
  have p0000 := @g_elex A (syn_cnc B)
  have p0001 := @g_ecexr A B (syn_cen)
  have p0002 := (Nominal.classEqRefl (syn_cnc B))
  have p0003 :=
    @g_eleq2s (.classMem B (syn_cvv)) A (syn_cec B (syn_cen)) (syn_cnc B) p0001 p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cnc B)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
      p0003
  have p0005 := @g_brex A B (syn_cen)
  have p0006 := @g_eleq2i (syn_cnc B) (syn_cec B (syn_cen)) A p0002
  have p0007 := @g_elec A B (syn_cen)
  have p0008 :=
    @g_bitri (.classMem A (syn_cnc B)) (.classMem A (syn_cec B (syn_cen)))
      (syn_wbr B (syn_cen) A) p0006 p0007
  have p0009 := @g_ener
  have p0010 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0009
  have p0011 := @g_simpr (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
  have p0012 := @g_simpl (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
  have p0013 :=
    @g_ersymb (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_cvv) (syn_cen)
      B A p0010 p0011 p0012
  have p0014 :=
    @g_syl5bb (.classMem A (syn_cnc B)) (syn_wbr B (syn_cen) A)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B)
      p0008 p0013
  have p0015 :=
    @g_pm5_21nii (.classMem A (syn_cnc B))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B)
      p0004 p0005 p0014
  exact p0015

@[expose]
noncomputable def g_eqncg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B))) :=
  by
  have p0000 := @g_ncidg A V
  have p0001 :=
    @g_adantr (.classMem A V) (.classMem A (syn_cnc A)) (.classEq (syn_cnc A) (syn_cnc B))
      p0000
  have p0002 := @g_eleq2 (syn_cnc A) (syn_cnc B) A
  have p0003 :=
    @g_adantl (.classEq (syn_cnc A) (syn_cnc B))
      (syn_wb (.classMem A (syn_cnc A)) (.classMem A (syn_cnc B))) (.classMem A V) p0002
  have p0004 :=
    @g_mpbid (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B)))
      (.classMem A (syn_cnc A)) (.classMem A (syn_cnc B)) p0001 p0003
  have p0005 := (Nominal.classEqRefl (syn_cnc B))
  have p0006 :=
    @g_syl6eleq (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B))) A (syn_cnc B)
      (syn_cec B (syn_cen)) p0004 p0005
  have p0007 := @g_ecexr A B (syn_cen)
  have p0008 :=
    @g_syl (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B)))
      (.classMem A (syn_cec B (syn_cen))) (.classMem B (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_ex (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B)) (.classMem B (syn_cvv)) p0008
  have p0010 := @g_brex A B (syn_cen)
  have p0011 :=
    @g_simprd (syn_wbr A (syn_cen) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      p0010
  have p0012 :=
    @g_a1i (.imp (syn_wbr A (syn_cen) B) (.classMem B (syn_cvv))) (.classMem A V) p0011
  have p0013 := @g_ener
  have p0014 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv))
      (syn_wa (.classMem A V) (.classMem B (syn_cvv))) p0013
  have p0015 := @g_dmen
  have p0016 :=
    @g_a1i (.classEq (syn_cdm (syn_cen)) (syn_cvv))
      (syn_wa (.classMem A V) (.classMem B (syn_cvv))) p0015
  have p0017 := @g_elex A V
  have p0018 :=
    @g_adantr (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0017
  have p0019 := @g_simpr (.classMem A V) (.classMem B (syn_cvv))
  have p0020 :=
    @g_erth (syn_wa (.classMem A V) (.classMem B (syn_cvv))) A B (syn_cen) (syn_cvv)
      (syn_cvv) p0014 p0016 p0018 p0019
  have p0021 := (Nominal.classEqRefl (syn_cnc A))
  have p0022 :=
    @g_eqeq12i (syn_cnc A) (syn_cec A (syn_cen)) (syn_cnc B) (syn_cec B (syn_cen)) p0021
      p0005
  have p0023 :=
    @g_syl6rbbr (syn_wa (.classMem A V) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B)
      (.classEq (syn_cec A (syn_cen)) (syn_cec B (syn_cen)))
      (.classEq (syn_cnc A) (syn_cnc B)) p0020 p0022
  have p0024 :=
    @g_ex (.classMem A V) (.classMem B (syn_cvv))
      (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) p0023
  have p0025 :=
    @g_pm5_21ndd (.classMem A V) (.classMem B (syn_cvv))
      (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B) p0009 p0012 p0024
  exact p0025

@[expose]
noncomputable def g_eqnc (A : Class) (B : Class)
    (hyp_eqnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) :=
  by
  have p0000 := @g_eqncg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_eqnc_1 p0000
  exact p0001

@[expose]
noncomputable def g_ncseqnc (A : Class) (X : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cncs)) (syn_wb (.classEq A (syn_cnc X)) (.classMem X A))) :=
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
  have dv_cache_0002 : y ∉ ((syn_wb (.classEq A (syn_cnc X)) (.classMem X A))).fv :=
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
  have p0000 := @g_elncs y A dv_cache_0001
  have p0001 := @g_vex y
  have p0002 := @g_ncid (.cv y) p0001
  have p0003 := @g_eleq2 (syn_cnc X) (syn_cnc (.cv y)) (.cv y)
  have p0004 :=
    @g_mpbiri (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.classMem (.cv y) (syn_cnc X))
      (.classMem (.cv y) (syn_cnc (.cv y))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cnc X))
  have p0006 :=
    @g_syl6eleq (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.cv y) (syn_cnc X)
      (syn_cec X (syn_cen)) p0004 p0005
  have p0007 := @g_ecexr (.cv y) X (syn_cen)
  have p0008 :=
    @g_syl (.classEq (syn_cnc X) (syn_cnc (.cv y)))
      (.classMem (.cv y) (syn_cec X (syn_cen))) (.classMem X (syn_cvv)) p0006 p0007
  have p0009 := @g_brex X (.cv y) (syn_cen)
  have p0010 :=
    @g_simpld (syn_wbr X (syn_cen) (.cv y)) (.classMem X (syn_cvv))
      (.classMem (.cv y) (syn_cvv)) p0009
  have p0011 := @g_ener
  have p0012 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) (.classMem X (syn_cvv)) p0011
  have p0013 := @g_dmen
  have p0014 :=
    @g_a1i (.classEq (syn_cdm (syn_cen)) (syn_cvv)) (.classMem X (syn_cvv)) p0013
  have p0015 := @g_id (.classMem X (syn_cvv))
  have p0016 := @g_a1i (.classMem (.cv y) (syn_cvv)) (.classMem X (syn_cvv)) p0001
  have p0017 :=
    @g_erth (.classMem X (syn_cvv)) X (.cv y) (syn_cen) (syn_cvv) (syn_cvv) p0012 p0014
      p0015 p0016
  have p0018 := (Nominal.classEqRefl (syn_cnc (.cv y)))
  have p0019 :=
    @g_eqeq12i (syn_cnc X) (syn_cec X (syn_cen)) (syn_cnc (.cv y))
      (syn_cec (.cv y) (syn_cen)) p0005 p0018
  have p0020 :=
    @g_syl6rbbr (.classMem X (syn_cvv)) (syn_wbr X (syn_cen) (.cv y))
      (.classEq (syn_cec X (syn_cen)) (syn_cec (.cv y) (syn_cen)))
      (.classEq (syn_cnc X) (syn_cnc (.cv y))) p0017 p0019
  have p0021 :=
    @g_pm5_21nii (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.classMem X (syn_cvv))
      (syn_wbr X (syn_cen) (.cv y)) p0008 p0010 p0020
  have p0022 := @g_eqcom (syn_cnc (.cv y)) (syn_cnc X)
  have p0023 := @g_elnc X (.cv y)
  have p0024 :=
    @g_n_3bitr4i (.classEq (syn_cnc X) (syn_cnc (.cv y))) (syn_wbr X (syn_cen) (.cv y))
      (.classEq (syn_cnc (.cv y)) (syn_cnc X)) (.classMem X (syn_cnc (.cv y))) p0021 p0022
      p0023
  have p0025 :=
    @g_a1i
      (syn_wb (.classEq (syn_cnc (.cv y)) (syn_cnc X)) (.classMem X (syn_cnc (.cv y))))
      (.classEq A (syn_cnc (.cv y))) p0024
  have p0026 := @g_eqeq1 A (syn_cnc (.cv y)) (syn_cnc X)
  have p0027 := @g_eleq2 A (syn_cnc (.cv y)) X
  have p0028 :=
    @g_n_3bitr4d (.classEq A (syn_cnc (.cv y))) (.classEq (syn_cnc (.cv y)) (syn_cnc X))
      (.classMem X (syn_cnc (.cv y))) (.classEq A (syn_cnc X)) (.classMem X A) p0025 p0026
      p0027
  have p0029 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv y)))
      (syn_wb (.classEq A (syn_cnc X)) (.classMem X A)) y dv_cache_0002 p0028
  have p0030 :=
    @g_sylbi (.classMem A (syn_cncs)) (syn_wex y (.classEq A (syn_cnc (.cv y))))
      (syn_wb (.classEq A (syn_cnc X)) (.classMem X A)) p0000 p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end
