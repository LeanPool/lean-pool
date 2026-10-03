/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block015

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_sifrreflectndv (D : Class) (R : Class)
    (hyp_sifrreflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_sifrreflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cfound) D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let r : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_r : z ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_r_ne_z : r ≠ z := Ne.symm fresh_z_ne_r
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_r_ne_q : r ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_r : q ≠ r := Ne.symm fresh_r_ne_q
  have dv_cache_0001 : q ∉ ((syn_csi R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_q_not_R,
          not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_r_not_R,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_x,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_r_ne_x,
          not_false_eq_true])
  have dv_cache_0005 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0006 : r ∉ ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_r_ne_z,
          not_false_eq_true])
  have dv_cache_0007 :
    r ∉
      ((Wff.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q))
          (.classEq (syn_csn (.cv z)) (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_z, fresh_r_ne_q, fresh_r_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x, fresh_z_ne_q,
          fresh_z_ne_r, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_q, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cuni (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_q,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q)))
            (.classEq (.cv z) (syn_cuni (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_q, fresh_y_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    q ∉
      ((syn_wrex y (.cv x) (syn_wral z (.cv x)
            (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_z, fresh_q_ne_y, fresh_q_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    q ∉
      ((syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_R, fresh_q_not_D, fresh_q_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (D).fv :=
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
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0016 : z ∉ (D).fv :=
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
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0017 : y ∉ (D).fv :=
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
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0018 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0019 : z ∉ (R).fv :=
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
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0020 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0023 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0024 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have p0000 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      hyp_sifrreflectndv_1
  have p0001 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      hyp_sifrreflectndv_2
  have p0002 :=
    @g_simpl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0003 := (Nominal.classEqRefl (syn_cwe))
  have p0004 :=
    @g_breqi (syn_csi R) (syn_cpw1 D) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 := @g_brin (syn_csi R) (syn_cpw1 D) (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cpw1 D))
      (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
        (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)))
      p0004 p0005
  have p0007 :=
    @g_simprbi (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0006
  have p0008 :=
    @g_syl
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0002 p0007
  have p0009 := @g_vex x
  have p0010 := @g_pw1ex (.cv x) p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cpw1 (.cv x)) (syn_cvv))
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      p0010
  have p0012 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0013 := @g_simpl (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) D) p0012
      p0013
  have p0015 := @g_pw1ss (.cv x) D
  have p0016 :=
    @g_syl
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) D) (syn_wss (syn_cpw1 (.cv x)) (syn_cpw1 D)) p0014 p0015
  have p0017 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0018 := @g_simpr (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))) (syn_wne (.cv x) (syn_c0))
      p0017 p0018
  have p0020 := @g_pw10b (.cv x)
  have p0021 := @g_necon3bii (syn_cpw1 (.cv x)) (syn_c0) (.cv x) (syn_c0) p0020
  have p0022 :=
    @g_biimpri (syn_wne (syn_cpw1 (.cv x)) (syn_c0)) (syn_wne (.cv x) (syn_c0)) p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cpw1 (.cv x)) (syn_c0)) p0019 p0022
  have p0024 :=
    @g_frd
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      q r (syn_cpw1 D) (syn_csi R) (syn_cvv) (syn_cpw1 (.cv x)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0011 p0016 p0023
  have p0025 :=
    @g_simpr
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0026 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (.cv x))) p0025 p0026
  have p0028 := @g_hnwpw1argcl (.cv x) q
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0027 p0028
  have p0030 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (.cv x))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (.cv x)) p0029 p0030
  have p0032 := @g_vex z
  have p0033 := @g_vex q
  have p0034 := @g_uniex (.cv q) p0033
  have p0035 := @g_brsnsi (.cv z) (syn_cuni (.cv q)) R p0032 p0034
  have p0036 :=
    @g_biimpri (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q))))
      (syn_wbr (.cv z) R (syn_cuni (.cv q))) p0035
  have p0037 :=
    @g_a1i
      (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q)))
        (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      p0036
  have p0038 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0039 :=
    @g_simpr
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0040 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (.cv x))) p0039 p0040
  have p0042 := @g_hnwpw1argcl (.cv x) q
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0041 p0042
  have p0044 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (.cv x))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0043 p0044
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0038 p0045
  have p0047 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.cv q) (syn_csn (syn_cuni (.cv q))) p0046
  have p0048 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_csn (syn_cuni (.cv q))) (.cv q) (syn_csn (.cv z)) (syn_csi R) p0047
  have p0049 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q))))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) p0048
  have p0050 :=
    @g_syld
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) R (syn_cuni (.cv q)))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q))))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) p0037 p0049
  have p0051 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0052 :=
    @g_simpr
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0053 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      p0052 p0053
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      p0051 p0054
  have p0056 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0057 := @g_snelpw1 (.cv z) (.cv x)
  have p0058 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x)))
      (.classMem (.cv z) (.cv x)) p0057
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (.cv x)) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) p0056
      p0058
  have p0060 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) p0055 p0059
  have p0061 := @g_id (.classEq (.cv r) (syn_csn (.cv z)))
  have p0062 :=
    @g_breq1d (.classEq (.cv r) (syn_csn (.cv z))) (.cv r) (syn_csn (.cv z)) (.cv q)
      (syn_csi R) p0061
  have p0063 := @g_id (.classEq (.cv r) (syn_csn (.cv z)))
  have p0064 :=
    @g_eqeq1d (.classEq (.cv r) (syn_csn (.cv z))) (.cv r) (syn_csn (.cv z)) (.cv q) p0063
  have p0065 :=
    @g_imbi12d (.classEq (.cv r) (syn_csn (.cv z))) (syn_wbr (.cv r) (syn_csi R) (.cv q))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))
      (.classEq (syn_csn (.cv z)) (.cv q)) p0062 p0064
  have p0066 :=
    @g_rspccva (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))
      (.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q))
        (.classEq (syn_csn (.cv z)) (.cv q)))
      r (syn_csn (.cv z)) (syn_cpw1 (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007
      p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
        (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))))
      (.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q))
        (.classEq (syn_csn (.cv z)) (.cv q)))
      p0060 p0066
  have p0068 :=
    @g_syld
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) R (syn_cuni (.cv q)))
      (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q))
      p0050 p0067
  have p0069 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (syn_csn (.cv z)) (.cv q))
  have p0070 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (syn_csn (.cv z)) (.cv q))
  have p0071 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0072 :=
    @g_simpr
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0073 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
          (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (.cv x))) p0072 p0073
  have p0075 := @g_hnwpw1argcl (.cv x) q
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (syn_cpw1 (.cv x)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0074 p0075
  have p0077 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (.cv x))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0076 p0077
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0071 p0078
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
              (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
                (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q)))
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0070 p0079
  have p0081 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
              (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
                (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q)))
      (syn_csn (.cv z)) (.cv q) (syn_csn (syn_cuni (.cv q))) p0069 p0080
  have p0082 := @g_vex z
  have p0083 := @g_sneqr (.cv z) (syn_cuni (.cv q)) p0082
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
              (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
                (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q)))
      (.classEq (syn_csn (.cv z)) (syn_csn (syn_cuni (.cv q))))
      (.classEq (.cv z) (syn_cuni (.cv q))) p0081 p0083
  have p0085 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (syn_csn (.cv z)) (.cv q)) (.classEq (.cv z) (syn_cuni (.cv q))) p0084
  have p0086 :=
    @g_syld
      (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
            (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
              (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (syn_csn (.cv z)) (.cv q))
      (.classEq (.cv z) (syn_cuni (.cv q))) p0068 p0085
  have p0087 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q))))
      z (.cv x) dv_cache_0008 p0086
  have p0088 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (syn_cuni (.cv q)) (.cv x))
      (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q)))
          (.classEq (.cv z) (syn_cuni (.cv q)))))
      p0031 p0087
  have p0089 := @g_id (.classEq (.cv y) (syn_cuni (.cv q)))
  have p0090 :=
    @g_breq2d (.classEq (.cv y) (syn_cuni (.cv q))) (.cv y) (syn_cuni (.cv q)) (.cv z) R
      p0089
  have p0091 := @g_id (.classEq (.cv y) (syn_cuni (.cv q)))
  have p0092 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni (.cv q))) (.cv y) (syn_cuni (.cv q)) (.cv z)
      p0091
  have p0093 :=
    @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q))) (syn_wbr (.cv z) R (.cv y))
      (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (.cv y))
      (.classEq (.cv z) (syn_cuni (.cv q))) p0090 p0092
  have p0094 :=
    @g_ralbidv (.classEq (.cv y) (syn_cuni (.cv q)))
      (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q))))
      z (.cv x) dv_cache_0009 p0093
  have p0095 :=
    @g_rspcev
      (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
      (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q)))
          (.classEq (.cv z) (syn_cuni (.cv q)))))
      y (syn_cuni (.cv q)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0094
  have p0096 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q))))))
      (syn_wrex y (.cv x) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))
      p0088 p0095
  have p0097_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex q (syn_cpw1 (.cv x)) (syn_wral r (syn_cpw1 (.cv x))
            (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict syn_cfound
          syn_cpw1
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0024
  have p0097 :=
    @g_rexlimddv
      (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))
      (syn_wral r (syn_cpw1 (.cv x))
        (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      (syn_wrex y (.cv x) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))
      q (syn_cpw1 (.cv x)) dv_cache_0013 dv_cache_0014 p0097_e00_recanon p0096
  have p0098_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict syn_cfound
          syn_cpw1
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0097
  have p0098 :=
    @g_frrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x z y D R dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0000 p0001 p0098_e02_recanon
  exact p0098

@[expose]
noncomputable def g_siwereflectndv (D : Class) (R : Class)
    (hyp_siwereflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_siwereflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cwe) D)) :=
  by
  have p0000 := @g_siorreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0001 := @g_sifrreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0002 :=
    @g_jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cstrict) D)
      (syn_wbr R (syn_cfound) D) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cwe))
  have p0004 := @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 := @g_brin R D (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0004 p0005
  have p0007 :=
    @g_biimpri (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0006
  have p0008 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D))
      (syn_wbr R (syn_cwe) D) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_hndownbrclndv (x : Var) (y : Var) (S : Class) (a : Var) (b : Var)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y)
    (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))) :=
  by
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_x), not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_y), not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_b_x), not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_b_y), not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), (Ne.symm dv_b_x), dv_S_x, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_y), (Ne.symm dv_b_y), dv_S_y, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_vex a
  have p0001 := @g_vex b
  have p0002 := @g_id (.classEq (.cv x) (.cv a))
  have p0003 := @g_sneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @g_breq1d (.classEq (.cv x) (.cv a)) (syn_csn (.cv x)) (syn_csn (.cv a))
      (syn_csn (.cv y)) S p0003
  have p0005 := @g_id (.classEq (.cv y) (.cv b))
  have p0006 := @g_sneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @g_breq2d (.classEq (.cv y) (.cv b)) (syn_csn (.cv y)) (syn_csn (.cv b))
      (syn_csn (.cv a)) S p0006
  have p0008 := @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
  have p0009 :=
    @g_brab (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) x y (.cv a) (.cv b)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0000 p0001 p0004 p0007 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hndownexclndv (x : Var) (y : Var) (S : Class) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_hndownexclndv_1 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ S.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_g : x ≠ g := Ne.symm fresh_g_ne_x
  have fresh_g_ne_y : g ≠ y := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_g : y ≠ g := Ne.symm fresh_g_ne_y
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv g) S)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_g, dv_S_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv g) S)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_g, dv_S_y, or_false, not_false_eq_true])
  have dv_cache_0003 : g ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0004 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : g ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_S, not_false_eq_true])
  have dv_cache_0007 :
    g ∉
      ((Wff.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_y,
          fresh_g_not_S, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv g) S)
  have p0001 :=
    @g_breqd (.classEq (.cv g) S) (.cv g) S (syn_csn (.cv x)) (syn_csn (.cv y)) p0000
  have p0002 :=
    @g_opabbidv (.classEq (.cv g) S) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv g) S)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv) p0002
  have p0004 := @g_hndownexndv x y g dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0005 :=
    @g_vtoclg
      (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (syn_cvv))
      (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv))
      g S (syn_cvv) dv_cache_0006 dv_cache_0007 p0003 p0004
  have p0006 := Nominal.mp hyp_hndownexclndv_1 p0005
  exact p0006

@[expose]
noncomputable def g_sidownrecoverclndv (x : Var) (y : Var) (D : Class) (S : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classEq
          (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) S)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let r : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_q_not_S : q ∉ S.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
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
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_a : q ≠ a := Ne.symm fresh_a_ne_q
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_b_ne_q : b ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_b : q ≠ b := Ne.symm fresh_b_ne_q
  have fresh_b_ne_r : b ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_r_ne_b : r ≠ b := Ne.symm fresh_b_ne_r
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : q ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_a, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_a, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_b, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_b, not_false_eq_true])
  have dv_cache_0005 :
    q ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0006 :
    r ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0007 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show q ≠ r from (by exact fresh_q_ne_r))
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
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0010 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0011 : q ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ y from (by exact fresh_q_ne_y))
  have dv_cache_0012 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0013 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0014 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0015 : q ∉ ((syn_wbr (.cv a) S (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_a, fresh_q_ne_b, fresh_q_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0016 : r ∉ ((syn_wbr (.cv a) S (.cv b))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_a, fresh_r_ne_b, fresh_r_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0017 : a ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0018 : b ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_D, not_false_eq_true])
  have dv_cache_0019 :
    a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0020 :
    b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0021 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0022 : x ∉ ((syn_cuni (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
          not_false_eq_true])
  have dv_cache_0023 : y ∉ ((syn_cuni (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_a,
          not_false_eq_true])
  have dv_cache_0024 : x ∉ ((syn_cuni (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_b,
          not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cuni (.cv b))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_b,
          not_false_eq_true])
  have dv_cache_0026 :
    x ∉ ((syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, dv_S_x, or_false,
          not_false_eq_true])
  have dv_cache_0027 :
    y ∉ ((syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, dv_S_y, or_false,
          not_false_eq_true])
  have dv_cache_0028 :
    a ∉ ((syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0029 :
    b ∉ ((syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0031 : b ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_S, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_a_not_S, fresh_a_not_D, or_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_b_not_S, fresh_b_not_D, or_false, not_false_eq_true])
  have p0000 :=
    @g_brsi q r (.cv a) (.cv b)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_biimpi
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wex q (syn_wex r (syn_w3a (.classEq (.cv a) (syn_csn (.cv q)))
            (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q)
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r)))))
      p0000
  have p0002 :=
    @g_simp3 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
      (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0003 :=
    @g_hndownbrclndv x y S q r dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0004 :=
    @g_biimpi
      (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
      (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0003
  have p0005 :=
    @g_syl
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
        (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv r)))
      (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
      (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0002 p0004
  have p0006 :=
    @g_simp1 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
      (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0007 :=
    @g_simp2 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
      (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0008 :=
    @g_breq12d
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
        (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv r)))
      (.cv a) (syn_csn (.cv q)) (.cv b) (syn_csn (.cv r)) S p0006 p0007
  have p0009 :=
    @g_biimprd
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
        (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv r)))
      (syn_wbr (.cv a) S (.cv b)) (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0008
  have p0010 :=
    @g_mpd
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
        (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv r)))
      (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) (syn_wbr (.cv a) S (.cv b)) p0005
      p0009
  have p0011 :=
    @g_exlimivv
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r)))
        (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (.cv r)))
      (syn_wbr (.cv a) S (.cv b)) q r dv_cache_0015 dv_cache_0016 p0010
  have p0012 :=
    @g_syl
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wex q (syn_wex r (syn_w3a (.classEq (.cv a) (syn_csn (.cv q)))
            (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q)
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r)))))
      (syn_wbr (.cv a) S (.cv b)) p0001 p0011
  have p0013 :=
    @g_a1i
      (.imp (syn_wbr (.cv a)
          (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
        (syn_wbr (.cv a) S (.cv b)))
      (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0012
  have p0014 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
  have p0015 :=
    @g_simpl (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
  have p0017 := (Nominal.biimpRefl (syn_wbr (.cv a) S (.cv b)))
  have p0018 :=
    @g_biimpi (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0017
  have p0019 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0014 p0018
  have p0020 :=
    @g_sseldd
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) (syn_cop (.cv a) (.cv b)) p0015 p0019
  have p0021 := @g_opelxp (.cv a) (.cv b) (syn_cpw1 D) (syn_cpw1 D)
  have p0022 :=
    @g_biimpi (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) p0020
      p0022
  have p0024 :=
    @g_pw1typedbrndv D (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) b a
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0025 := @g_simpl (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0026 := @g_pw1argclcl D (.cv a)
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.classMem (.cv a) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a)))))
      p0025 p0026
  have p0028 :=
    @g_simpl (.classMem (syn_cuni (.cv a)) D)
      (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a)))))
      (.classMem (syn_cuni (.cv a)) D) p0027 p0028
  have p0030 := @g_elex (syn_cuni (.cv a)) D
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv a)) D) (.classMem (syn_cuni (.cv a)) (syn_cvv)) p0029
      p0030
  have p0032 := @g_simpr (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0033 := @g_pw1argclcl D (.cv b)
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.classMem (.cv b) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b)))))
      p0032 p0033
  have p0035 :=
    @g_simpl (.classMem (syn_cuni (.cv b)) D)
      (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b)))))
      (.classMem (syn_cuni (.cv b)) D) p0034 p0035
  have p0037 := @g_elex (syn_cuni (.cv b)) D
  have p0038 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv b)) D) (.classMem (syn_cuni (.cv b)) (syn_cvv)) p0036
      p0037
  have p0039 :=
    @g_jca (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.classMem (syn_cuni (.cv a)) (syn_cvv)) (.classMem (syn_cuni (.cv b)) (syn_cvv))
      p0031 p0038
  have p0040 :=
    @g_simpl (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))
  have p0041 :=
    @g_sneqd
      (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b))))
      (.cv x) (syn_cuni (.cv a)) p0040
  have p0042 :=
    @g_simpr (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))
  have p0043 :=
    @g_sneqd
      (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b))))
      (.cv y) (syn_cuni (.cv b)) p0042
  have p0044 :=
    @g_breq12d
      (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b))))
      (syn_csn (.cv x)) (syn_csn (syn_cuni (.cv a))) (syn_csn (.cv y))
      (syn_csn (syn_cuni (.cv b))) S p0041 p0043
  have p0045 := @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
  have p0046 :=
    @g_brabga (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))
      (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) x y
      (syn_cuni (.cv a)) (syn_cuni (.cv b))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv) (syn_cvv)
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0014 p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv a)) (syn_cvv)) (.classMem (syn_cuni (.cv b)) (syn_cvv)))
      (syn_wb (syn_wbr (syn_cuni (.cv a))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cuni (.cv b)))
        (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))))
      p0039 p0046
  have p0048 :=
    @g_bitrd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wbr (syn_cuni (.cv a))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cuni (.cv b)))
      (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) p0024 p0047
  have p0052 :=
    @g_simpr (.classMem (syn_cuni (.cv a)) D)
      (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))
  have p0053 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a)))))
      (.classEq (.cv a) (syn_csn (syn_cuni (.cv a)))) p0027 p0052
  have p0057 :=
    @g_simpr (.classMem (syn_cuni (.cv b)) D)
      (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))
  have p0058 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b)))))
      (.classEq (.cv b) (syn_csn (syn_cuni (.cv b)))) p0034 p0057
  have p0059 :=
    @g_breq12d (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (.cv a) (syn_csn (syn_cuni (.cv a))) (.cv b) (syn_csn (syn_cuni (.cv b))) S p0053
      p0058
  have p0060 :=
    @g_bicomd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wbr (.cv a) S (.cv b))
      (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) p0059
  have p0061 :=
    @g_bitrd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))
      (syn_wbr (.cv a) S (.cv b)) p0048 p0060
  have p0062 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D)))
      (syn_wb (syn_wbr (.cv a)
          (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
        (syn_wbr (.cv a) S (.cv b)))
      p0023 p0061
  have p0063 :=
    @g_biimprd
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wbr (.cv a) S (.cv b)) p0062
  have p0064 :=
    @g_mpd
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)))
      (syn_wbr (.cv a) S (.cv b))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      p0014 p0063
  have p0065 :=
    @g_ex (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      p0064
  have p0066 :=
    @g_impbid (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wbr (.cv a) S (.cv b)) p0013 p0065
  have p0067 :=
    (Nominal.biimpRefl (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)))
  have p0068 :=
    @g_bicomi
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      p0067
  have p0069 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv a) (.cv b))
          (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
        (syn_wbr (.cv a)
          (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)))
      (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0068
  have p0071 :=
    @g_bicomi (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0017
  have p0072 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv a) (.cv b)) S) (syn_wbr (.cv a) S (.cv b)))
      (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0071
  have p0073 :=
    @g_n_3bitr4d (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wbr (.cv a)
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))
      (syn_wbr (.cv a) S (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (syn_cop (.cv a) (.cv b)) S) p0066 p0069 p0072
  have p0074 :=
    @g_eqrelrdv (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) a b
      (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) S
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0021 p0073
  exact p0074


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit

@[expose]
noncomputable def g_sidownsuppclndv (x : Var) (y : Var) (D : Class) (S : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (syn_cxp D D))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (S).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0003 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0004 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0005 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0006 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : a ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_wss, fv_syn_cxp, fv_syn_cpw1, Finset.mem_union, fresh_a_not_S,
          fresh_a_not_D, or_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_wss, fv_syn_cxp, fv_syn_cpw1, Finset.mem_union, fresh_b_not_S,
          fresh_b_not_D, or_false, not_false_eq_true])
  have dv_cache_0010 :
    a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_copab, fv_syn_wbr, fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0011 :
    b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_copab, fv_syn_wbr, fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_cxp D D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cxp, Finset.mem_union, fresh_a_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0013 : b ∉ ((syn_cxp D D)).fv :=
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
        simp only [fv_syn_cxp, Finset.mem_union, fresh_b_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0014 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_simpl (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0001 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0002 :=
    (Nominal.biimpRefl
      (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)))
  have p0003 :=
    @g_biimpri
      (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
      p0002
  have p0004 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
      (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))
      p0001 p0003
  have p0005 :=
    @g_hndownbrclndv x y S a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0006 :=
    @g_biimpi
      (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))
      (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))
      (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0004 p0006
  have p0008 := (Nominal.biimpRefl (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))))
  have p0009 :=
    @g_biimpi (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0007 p0009
  have p0011 :=
    @g_sseldd
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b)))
      p0000 p0010
  have p0012 := @g_opelxp (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cpw1 D) (syn_cpw1 D)
  have p0013 :=
    @g_biimpi
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b)))
        (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b)))
        (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      p0011 p0013
  have p0015 :=
    @g_simpl (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0014 p0015
  have p0017 := @g_snelpw1 (.cv a) D
  have p0018 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D))
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      p0017
  have p0019 :=
    @g_mpbid
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0016 p0018
  have p0035 :=
    @g_simpr (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0014 p0035
  have p0037 := @g_snelpw1 (.cv b) D
  have p0038 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) (.classMem (.cv b) D))
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      p0037
  have p0039 :=
    @g_mpbid
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) (.classMem (.cv b) D) p0036 p0038
  have p0040 :=
    @g_jca
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (.classMem (.cv a) D) (.classMem (.cv b) D) p0019 p0039
  have p0041 := @g_opelxp (.cv a) (.cv b) D D
  have p0042 :=
    @g_biimpri (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)) p0040 p0042
  have p0044 :=
    @g_ex (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)) p0043
  have p0045 :=
    @g_alrimivv (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (.imp (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
        (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)))
      a b dv_cache_0008 dv_cache_0009 p0044
  have p0046 :=
    @g_ssrel a b (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
      (syn_cxp D D) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0047 :=
    @g_a1i
      (syn_wb (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
          (syn_cxp D D)) (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b))
                (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
              (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D))))))
      (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0046
  have p0048 :=
    @g_mpbird (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cxp D D))
      (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b))
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
            (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)))))
      p0045 p0047
  exact p0048

@[expose]
noncomputable def g_pw1subunissclndv (A : Class) (S : Class)
    (hyp_pw1subunissclndv_1 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ S.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (h))
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_S, not_false_eq_true])
  have dv_cache_0002 :
    g ∉ ((Wff.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, fv_syn_wss, fv_syn_cpw1,
          fv_syn_cuni, Finset.mem_union, fresh_g_not_S, fresh_g_not_A, or_false,
          not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv g) S)
  have p0001 := @g_sseq1d (.classEq (.cv g) S) (.cv g) S (syn_cpw1 A) p0000
  have p0003 := @g_unieqd (.classEq (.cv g) S) (.cv g) S p0000
  have p0004 := @g_sseq1d (.classEq (.cv g) S) (syn_cuni (.cv g)) (syn_cuni S) A p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv g) S) (syn_wss (.cv g) (syn_cpw1 A))
      (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni (.cv g)) A) (syn_wss (syn_cuni S) A)
      p0001 p0004
  have p0006 := @g_pw1subuniss g A
  have p0007 :=
    @g_vtoclg (.imp (syn_wss (.cv g) (syn_cpw1 A)) (syn_wss (syn_cuni (.cv g)) A))
      (.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A)) g S (syn_cvv) dv_cache_0001
      dv_cache_0002 p0005 p0006
  have p0008 := Nominal.mp hyp_pw1subunissclndv_1 p0007
  exact p0008

@[expose]
noncomputable def g_hnsireversecodememndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))) :=
  by
  have dv_cache_0001 : u ∉ ((syn_cpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cpw1, dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cuni, fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cuni, fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_u_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_u_y),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0007 :
    Disjoint (A).fv
      ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
            (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (A).fv ((syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))).fv
        from (by
          rw [fv_syn_copab];
          exact
            (show
              Disjoint ((A).fv)
                ((((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                              (syn_csn (.cv y)))).fv).erase
                        y).erase
                    x) ∪
                  (((({ x } : Finset Var)).erase y).erase x))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint ((A).fv)
                      (((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                                  (syn_csn (.cv y)))).fv).erase
                            y).erase
                        x)
                    from
                    (Disjoint.mono_right (Finset.erase_subset x _)
                      (show
                        Disjoint ((A).fv)
                          ((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                                  (syn_csn (.cv y)))).fv).erase
                            y)
                        from
                        (Disjoint.mono_right (Finset.erase_subset y _)
                          (show
                            Disjoint ((A).fv)
                              (((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                                  (syn_csn (.cv y)))).fv)
                            from
                            (by
                              rw [fv_syn_wbr];
                              exact
                                (show
                                  Disjoint ((A).fv)
                                    ((((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) ∪
                                      (((syn_cfv (syn_c1st) (.cv u))).fv))
                                  from
                                  (Finset.disjoint_union_right.mpr
                                    ⟨(Finset.disjoint_union_right.mpr
                                        ⟨(show Disjoint ((A).fv) (((syn_csn (.cv x))).fv)
                                            from
                                            (by
                                              rw [fv_syn_csn];
                                              exact
                                                (show
                                                  Disjoint ((A).fv) (((Class.cv x)).fv)
                                                  from
                                                  (by
                                                    rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                                    exact
                                                      (show
                                                        Disjoint ((A).fv)
                                                          (({ x } : Finset Var))
                                                        from
                                                        (Finset.disjoint_singleton_right.mpr
                                                          (show x ∉ (A).fv from
                                                            (by exact dv_A_x)))))))),
                                          (show Disjoint ((A).fv) (((syn_csn (.cv y))).fv)
                                            from
                                            (by
                                              rw [fv_syn_csn];
                                              exact
                                                (show
                                                  Disjoint ((A).fv) (((Class.cv y)).fv)
                                                  from
                                                  (by
                                                    rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                                    exact
                                                      (show
                                                        Disjoint ((A).fv)
                                                          (({ y } : Finset Var))
                                                        from
                                                        (Finset.disjoint_singleton_right.mpr
                                                          (show y ∉ (A).fv from
                                                            (by exact dv_A_y))))))))⟩),
                                      (show
                                        Disjoint ((A).fv)
                                          (((syn_cfv (syn_c1st) (.cv u))).fv)
                                        from
                                        (by
                                          rw [fv_syn_cfv];
                                          exact
                                            (show
                                              Disjoint ((A).fv)
                                                ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
                                              from
                                              (Finset.disjoint_union_right.mpr
                                                ⟨(show
                                                    Disjoint ((A).fv) (((Class.cv u)).fv)
                                                    from
                                                    (by
                                                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                                      exact
                                                        (show
                                                          Disjoint ((A).fv)
                                                            (({ u } : Finset Var))
                                                          from
                                                          (Finset.disjoint_singleton_right.mpr
                                                            (show u ∉ (A).fv from
                                                              (by exact dv_A_u)))))),
                                                  (show
                                                    Disjoint ((A).fv) (((syn_c1st)).fv)
                                                    from
                                                    (by
                                                      rw [fv_syn_c1st];
                                                      exact
                                                        (show
                                                          Disjoint ((A).fv)
                                                            ((∅ : Finset Var))
                                                          from (by simp))))⟩))))⟩)))))))),
                  (show Disjoint ((A).fv) (((({ x } : Finset Var)).erase y).erase x) from
                    (Disjoint.mono_right (Finset.erase_subset x _)
                      (show Disjoint ((A).fv) ((({ x } : Finset Var)).erase y) from
                        (Disjoint.mono_right (Finset.erase_subset y _)
                          (show Disjoint ((A).fv) (({ x } : Finset Var)) from
                            (Finset.disjoint_singleton_right.mpr
                              (show x ∉ (A).fv from (by exact dv_A_x))))))))⟩))))
  have p0000 := @g_hwcnwendv u (syn_cpw1 A) dv_cache_0001
  have p0001 := @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0002 := @g_pw1ss1c A
  have p0003 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      p0002
  have p0004 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 A) (syn_c1c) p0001 p0003
  have p0005 := @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c))
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0004 p0005
  have p0007 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))
      (syn_cwe) p0006
  have p0008 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0000 p0007
  have p0009 := @g_hwcnsupp u (syn_cpw1 A)
  have p0022 :=
    @g_xpeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0006 p0006
  have p0023 :=
    @g_sseq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c1st) (.cv u)) p0022
  have p0024 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      p0009 p0023
  have p0025 :=
    @g_sidownrecoverclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0026 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cfv (syn_c1st) (.cv u)))
      p0024 p0025
  have p0027 :=
    @g_breq1d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_csi (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cwe) p0026
  have p0028 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wbr (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0008 p0027
  have p0029 := @g_fvex (.cv u) (syn_c1st)
  have p0030 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0029
  have p0031 := @g_fvex (.cv u) (syn_c2nd)
  have p0032 := @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0031
  have p0033 :=
    @g_siwereflectndv (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      p0030 p0032
  have p0034 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wbr (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      p0028 p0033
  have p0037 := @g_pw1subunissclndv A (syn_cfv (syn_c2nd) (.cv u)) p0031
  have p0038 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A))
      (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A) p0001 p0037
  have p0039 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wbr (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A) p0034 p0038
  have p0044 :=
    @g_elhwcodes A (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      dv_cache_0007 p0030 p0032
  have p0045 :=
    @g_biimpri
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A))
      p0044
  have p0046 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wbr (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A))
      p0039 p0045
  have p0063 :=
    @g_sidownsuppclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0064 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0024 p0063
  have p0069 :=
    @g_opfv1st
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0030 p0032
  have p0074 :=
    @g_opfv2nd
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0030 p0032
  have p0080 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0074 p0074
  have p0081 :=
    @g_sseq12i
      (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop
            (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      p0069 p0080
  have p0082 :=
    @g_a1i
      (syn_wb (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop
                (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                    (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wss (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0081
  have p0083 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                  (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wss (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0064 p0082
  have p0084 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                  (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      p0046 p0083
  have p0089 :=
    @g_opex
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0030 p0032
  have p0090 :=
    @g_elhwcncl A
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
  have p0091 := Nominal.mp p0089 p0090
  have p0092 :=
    @g_biimpri
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))
      (syn_wa (.classMem (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop
                (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                    (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
      p0091
  have p0093 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (.classMem (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop
                (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                    (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))
      p0084 p0092
  exact p0093

@[expose]
noncomputable def g_hnsireversecodeidndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (_dv_A_x : x ∉ A.fv) (_dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv u) (syn_cop (syn_csi
              (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                  (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) :=
  by
  have dv_cache_0001 : u ∉ ((syn_cpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cpw1, dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cuni, fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cuni, fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_u_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_u_y),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_hwcnpair u (syn_cpw1 A)
  have p0001 := @g_hwcnsupp u (syn_cpw1 A)
  have p0002 := @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0003 := @g_pw1ss1c A
  have p0004 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      p0003
  have p0005 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 A) (syn_c1c) p0002 p0004
  have p0006 := @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c))
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0005 p0006
  have p0014 :=
    @g_xpeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0007 p0007
  have p0015 :=
    @g_sseq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c1st) (.cv u)) p0014
  have p0016 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      p0001 p0015
  have p0017 :=
    @g_sidownrecoverclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0018 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cfv (syn_c1st) (.cv u)))
      p0016 p0017
  have p0019 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_csi (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
      (syn_cfv (syn_c1st) (.cv u)) p0018
  have p0026 :=
    @g_opeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c1st) (.cv u))
      (syn_csi (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      p0019 p0007
  have p0027 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cop (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0000 p0026
  exact p0027


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_sieqdndv (ph : Wff) (A : Class) (B : Class)
    (hyp_sieqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csi A) (syn_csi B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : w ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0005 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0006 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0007 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0012 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0013 : x ∉ (ph).fv :=
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
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0014 : y ∉ (ph).fv :=
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
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0015 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0016 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0017 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0018 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si x y z w A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_a1i
      (.classEq (syn_csi A) (syn_copab x y (syn_wex z (syn_wex w
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
                (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w)))))))
      ph p0000
  have p0002 := @g_breqd ph A B (.cv z) (.cv w) hyp_sieqdndv_1
  have p0003 :=
    @g_n_3anbi3d ph (syn_wbr (.cv z) A (.cv w)) (syn_wbr (.cv z) B (.cv w))
      (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) p0002
  have p0004 :=
    @g_n_2exbidv ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) A (.cv w)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) B (.cv w)))
      z w dv_cache_0011 dv_cache_0012 p0003
  have p0005 :=
    @g_opabbidv ph
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w)))))
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w)))))
      x y dv_cache_0013 dv_cache_0014 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si x y z w B
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @g_eqcomi (syn_csi B)
      (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
              (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w))))))
      p0006
  have p0008 :=
    @g_a1i
      (.classEq (syn_copab x y (syn_wex z (syn_wex w
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
                (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w))))))
        (syn_csi B))
      ph p0007
  have p0009 :=
    @g_n_3eqtrd ph (syn_csi A)
      (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
              (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w))))))
      (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
              (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w))))))
      (syn_csi B) p0001 p0005 p0008
  exact p0009

@[expose]
noncomputable def g_hnsicodemapvalclndv (A : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q)
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_Q, not_false_eq_true])
  have dv_cache_0003 :
    q ∉
      ((Wff.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
          (.classEq (syn_cfv (syn_chnsicodemap A) Q)
            (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_q_not_Q, fresh_q_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elex Q (syn_cpw1 (syn_chwcn A))
  have p0001 := @g_id (.classEq (.cv q) Q)
  have p0002 := @g_eleq1d (.classEq (.cv q) Q) (.cv q) Q (syn_cpw1 (syn_chwcn A)) p0001
  have p0004 := @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0001
  have p0006 := @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0001
  have p0007 :=
    @g_fveq2d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q) (syn_c1st) p0006
  have p0008 :=
    @g_sieqdndv (.classEq (.cv q) Q) (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
      (syn_cfv (syn_c1st) (syn_cuni Q)) p0007
  have p0011 :=
    @g_fveq2d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q) (syn_c2nd) p0006
  have p0012 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni Q))
  have p0013 :=
    @g_syl (.classEq (.cv q) Q)
      (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni Q)))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))
      p0011 p0012
  have p0014 :=
    @g_opeq12d (.classEq (.cv q) Q) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))) p0008 p0013
  have p0015 :=
    @g_eqeq12d (.classEq (.cv q) Q) (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_chnsicodemap A) Q)
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))
      p0004 p0014
  have p0016 :=
    @g_imbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      (.classEq (syn_cfv (syn_chnsicodemap A) Q)
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))))
      p0002 p0015
  have p0017 := @g_hnsicodemapvalndv A q dv_cache_0001
  have p0018 :=
    @g_vtoclg
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))))
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q)
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))))
      q Q (syn_cvv) dv_cache_0002 dv_cache_0003 p0016 p0017
  have p0019 :=
    @g_mpcom (.classMem Q (syn_cvv)) (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) Q)
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))))
      p0000 p0018
  exact p0019

@[expose]
noncomputable def g_hnsicodemapfondv (A : Class) :
    Nominal.NPrf
      (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u_ne_q : u ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_u : q ≠ u := Ne.symm fresh_u_ne_q
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    q ∉
      ((syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y,
          fresh_q_ne_u, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0011 :
    q ∉
      ((Wff.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_u, fresh_q_ne_x,
          fresh_q_ne_y, fresh_q_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_chwcn (syn_cpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_chwcn (syn_cpw1 A))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0015 : q ∉ ((syn_chnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((syn_chnsicodemap A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0017 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have p0000 := @g_hnsicodemapfndv A
  have p0001 :=
    @g_hnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_snelpw1
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chwcn A)
  have p0003 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classMem
          (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0002
  have p0004 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))
      p0001 p0003
  have p0005 :=
    @g_hnsireversecodeidndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0010 :=
    @g_hnsicodemapvalclndv A
      (syn_csn (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
  have p0011 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st)
              (syn_cuni (syn_csn (syn_cop (syn_copab x y
                      (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                        (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                      (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u))
                        (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))))
      p0004 p0010
  have p0013 :=
    @g_elex
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chwcn A)
  have p0014 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
      p0001 p0013
  have p0015 :=
    @g_unisng
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cvv)
  have p0016 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
      (.classEq (syn_cuni (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0014 p0015
  have p0017 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cuni (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_c1st) p0016
  have p0018 := @g_fvex (.cv u) (syn_c1st)
  have p0019 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0007 dv_cache_0008
      dv_cache_0006 p0018
  have p0020 := @g_fvex (.cv u) (syn_c2nd)
  have p0021 := @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0020
  have p0022 :=
    @g_opfv1st
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0019 p0021
  have p0023 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0022
  have p0024 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cfv (syn_c1st) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      p0017 p0023
  have p0025 :=
    @g_sieqdndv (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      p0024
  have p0031 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cuni (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (syn_c2nd) p0016
  have p0036 :=
    @g_opfv2nd
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0019 p0021
  have p0037 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0036
  have p0038 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0031 p0037
  have p0039 :=
    @g_pw1eq
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
  have p0040 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classEq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
        (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                    (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0038 p0039
  have p0041 :=
    @g_opeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
      (syn_csi (syn_copab x y
          (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
      (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0025 p0040
  have p0042 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y
                    (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cop (syn_copab x y
                    (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                  (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))))
      (syn_cop (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0011 p0041
  have p0043 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      p0042
  have p0044 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.cv u)
      (syn_cop (syn_csi (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))))
        (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      p0005 p0043
  have p0045 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A)))
      (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      p0004 p0044
  have p0046 :=
    @g_id
      (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
  have p0047 :=
    @g_fveq2d
      (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (.cv q)
      (syn_csn (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_chnsicodemap A) p0046
  have p0048 :=
    @g_eqeq2d
      (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
              (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
            (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
      (.cv u) p0047
  have p0049 :=
    @g_rspcev (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))
      q
      (syn_csn (syn_cop (syn_copab x y
            (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
          (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpw1 (syn_chwcn A)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0048
  have p0050 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (.classMem (syn_csn (syn_cop (syn_copab x y
                (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
              (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y
                  (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))
                (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q))))
      p0045 p0049
  have p0051 :=
    @g_rgen
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q))))
      u (syn_chwcn (syn_cpw1 A)) p0050
  have p0052 :=
    @g_pm3_2i
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wral u (syn_chwcn (syn_cpw1 A)) (syn_wrex q (syn_cpw1 (syn_chwcn A))
          (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q)))))
      p0000 p0051
  have p0053 :=
    @g_dffo3 q u (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A)
      dv_cache_0010 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017
  have p0054 :=
    @g_biimpri
      (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (syn_wral u (syn_chwcn (syn_cpw1 A)) (syn_wrex q (syn_cpw1 (syn_chwcn A))
            (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q))))))
      p0053
  have p0055 := Nominal.mp p0052 p0054
  exact p0055

@[expose]
noncomputable def g_siinjndv (ph : Wff) (R : Class) (S : Class)
    (hyp_siinjndv_1 : Nominal.NPrf (.imp ph (.classEq (syn_csi R) (syn_csi S)))) :
    Nominal.NPrf (.imp ph (.classEq R S)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0003 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0004 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_breqd ph (syn_csi R) (syn_csi S) (syn_csn (.cv x)) (syn_csn (.cv y)) hyp_siinjndv_1
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_brsnsi (.cv x) (.cv y) R p0001 p0002
  have p0004 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      ph p0003
  have p0005 :=
    @g_bicomd ph (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0004
  have p0008 := @g_brsnsi (.cv x) (.cv y) S p0001 p0002
  have p0009 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y)))
        (syn_wbr (.cv x) S (.cv y)))
      ph p0008
  have p0010 :=
    @g_bicomd ph (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y)))
      (syn_wbr (.cv x) S (.cv y)) p0009
  have p0011 :=
    @g_n_3bitr4d ph (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv y)) p0000 p0005 p0010
  have p0012 := (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y)))
  have p0013 :=
    @g_bicomi (syn_wbr (.cv x) R (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) R) p0012
  have p0014 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) R) (syn_wbr (.cv x) R (.cv y))) ph
      p0013
  have p0015 := (Nominal.biimpRefl (syn_wbr (.cv x) S (.cv y)))
  have p0016 :=
    @g_bicomi (syn_wbr (.cv x) S (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) S) p0015
  have p0017 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) S) (syn_wbr (.cv x) S (.cv y))) ph
      p0016
  have p0018 :=
    @g_n_3bitr4d ph (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) R) (.classMem (syn_cop (.cv x) (.cv y)) S)
      p0011 p0014 p0017
  have p0019 :=
    @g_eqrelrdv ph x y R S dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0018
  exact p0019

@[expose]
noncomputable def g_hwcnpairclndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A))
        (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((Wff.imp (.classMem B (syn_chwcn A))
          (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elex B (syn_chwcn A)
  have p0001 := @g_id (.classEq (.cv u) B)
  have p0002 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0001
  have p0005 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0001
  have p0007 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0001
  have p0008 :=
    @g_opeq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) p0005 p0007
  have p0009 :=
    @g_eqeq12d (.classEq (.cv u) B) (.cv u) B
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)) p0001 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) p0002 p0009
  have p0011 := @g_hwcnpair u A
  have p0012 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem B (syn_chwcn A))
        (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
      u B (syn_cvv) dv_cache_0001 dv_cache_0002 p0010 p0011
  have p0013 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_chwcn A))
      (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnsicodemapf1ndv (A : Class) :
    Nominal.NPrf
      (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (h)
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q := Ne.symm fresh_q_ne_r
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_q, fresh_r_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_chnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_chnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0008 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have p0000 := @g_hnsicodemapfndv A
  have p0001 :=
    @g_simpl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0002 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0001 p0002
  have p0004 := @g_hnwpw1argcl (syn_chwcn A) q
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0003 p0004
  have p0006 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005 p0006
  have p0013 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0005 p0013
  have p0015 := @g_hwcnpairclndv A (syn_cuni (.cv q))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0014 p0015
  have p0020 := @g_hnsicodemapvalndv A q dv_cache_0001
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      p0003 p0020
  have p0022 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0021
  have p0023 :=
    @g_simpr
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0025 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0001 p0025
  have p0027 := @g_hnsicodemapvalndv A r dv_cache_0002
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0026 p0027
  have p0029 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      p0022 p0023 p0028
  have p0030 :=
    @g_opth (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
  have p0031 :=
    @g_biimpi
      (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
        (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
        (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0029 p0031
  have p0033 :=
    @g_simpl
      (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
        (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
      p0032 p0033
  have p0035 :=
    @g_siinjndv
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r)))
      p0034
  have p0052 :=
    @g_simpr
      (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
        (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      p0032 p0052
  have p0054 :=
    @g_pw111 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))
  have p0055 :=
    @g_biimpi
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
      p0054
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
      p0053 p0055
  have p0057 :=
    @g_opeq12d
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r)))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))
      p0035 p0056
  have p0061 := @g_hnwpw1argcl (syn_chwcn A) r
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      p0026 p0061
  have p0063 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0062 p0063
  have p0065 := @g_hwcnpairclndv A (syn_cuni (.cv r))
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (syn_cuni (.cv r)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      p0064 p0065
  have p0067 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cuni (.cv r))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
      p0066
  have p0068 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cuni (.cv q))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
      (syn_cuni (.cv r)) p0016 p0057 p0067
  have p0069 :=
    @g_sneqd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_cuni (.cv q)) (syn_cuni (.cv r)) p0068
  have p0075 :=
    @g_simpr (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))) p0062 p0075
  have p0077 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.cv r) (syn_csn (syn_cuni (.cv r))) p0076
  have p0078 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cuni (.cv r))) (.cv r) p0007
      p0069 p0077
  have p0079 :=
    @g_ex
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0078
  have p0080 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))
      p0079
  have p0081 :=
    @g_ralrimiv (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))
      r (syn_cpw1 (syn_chwcn A)) dv_cache_0003 p0080
  have p0082 :=
    @g_rgen
      (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp
          (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
            (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))
      q (syn_cpw1 (syn_chwcn A)) p0081
  have p0083 :=
    @g_pm3_2i
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp
            (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
              (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0000 p0082
  have p0084 :=
    @g_dff13 q r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0085_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
          (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp
                (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
                  (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnsicodemap syn_cres
          syn_chnsicodeliftfn syn_ctxp syn_clnpwsirelfn syn_clnpwpw1secondfn syn_cpw1
          syn_chwcn
        simp (config := { failIfUnchanged := false }) only []
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
      p0084
  have p0085 :=
    @g_biimpri
      (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp
              (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
                (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0085_e00_recanon
  have p0086 := Nominal.mp p0083 p0085
  exact p0086

@[expose]
noncomputable def g_hnsicodemapf1ondv (A : Class) :
    Nominal.NPrf
      (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) :=
  by
  have p0000 := @g_hnsicodemapf1ndv A
  have p0001 := @g_hnsicodemapfondv A
  have p0002 :=
    @g_pm3_2i
      (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))))
  have p0004 :=
    @g_biimpri
      (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))))
      p0003
  have p0005 := Nominal.mp p0002 p0004
  exact p0005

@[expose]
noncomputable def g_hnsiquomapexgndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnsiquomap A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnsiquomap A))
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnsiquomap A)
        (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
          (syn_cpw1 (syn_chnord A))))
      (.classMem A (syn_cvv)) p0000
  have p0002 := @g_hnsicodemapexgndv A
  have p0003 := @g_imageexg (syn_chnsicodemap A) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnsicodemap A) (syn_cvv))
      (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv)) p0002 p0003
  have p0005 := @g_pw1fnex
  have p0006 := @g_a1i (.classMem (syn_cpw1fn) (syn_cvv)) (.classMem A (syn_cvv)) p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv))
      (.classMem (syn_cpw1fn) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_coexg (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv))
        (.classMem (syn_cpw1fn) (syn_cvv)))
      (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv))
      p0007 p0008
  have p0010 := @g_hnordexg A
  have p0011 := @g_pw1exg (syn_chnord A) (syn_cvv)
  have p0012 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv)) p0009 p0012
  have p0014 :=
    @g_resexg (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
      (syn_cpw1 (syn_chnord A)) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv))
        (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv)))
      (.classMem (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
          (syn_cpw1 (syn_chnord A))) (syn_cvv))
      p0013 p0014
  have p0016 :=
    @g_eqeltrd (.classMem A (syn_cvv)) (syn_chnsiquomap A)
      (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
        (syn_cpw1 (syn_chnord A)))
      (syn_cvv) p0001 p0015
  exact p0016

@[expose]
noncomputable def g_hnsiquomapfnndv (A : Class)
    (hyp_hnsiquomapfnndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A))) :=
  by
  have p0000 := @g_hnsicodemapexgndv A
  have p0001 := Nominal.mp hyp_hnsiquomapfnndv_1 p0000
  have p0002 := @g_wppimagefn (syn_chnsicodemap A) p0001
  have p0003 := @g_fnpw1fn
  have p0004 := @g_ssv (syn_crn (syn_cpw1fn))
  have p0005 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_chnsicodemap A)) (syn_cvv))
      (syn_wfn (syn_cpw1fn) (syn_c1c)) (syn_wss (syn_crn (syn_cpw1fn)) (syn_cvv)) p0002
      p0003 p0004
  have p0006 := @g_fnco (syn_cvv) (syn_c1c) (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_pw1ss1c (syn_chnord A)
  have p0009 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_c1c))
      (syn_wss (syn_cpw1 (syn_chnord A)) (syn_c1c)) p0007 p0008
  have p0010 :=
    @g_fnssres (syn_c1c) (syn_cpw1 (syn_chnord A))
      (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := (Nominal.classEqRefl (syn_chnsiquomap A))
  have p0013 :=
    @g_fneq1i (syn_cpw1 (syn_chnord A)) (syn_chnsiquomap A)
      (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
        (syn_cpw1 (syn_chnord A)))
      p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)))
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
          (syn_cpw1 (syn_chnord A))) (syn_cpw1 (syn_chnord A)))
      p0011 p0013
  exact p0014

@[expose]
noncomputable def g_hnsiquomapvalndv (A : Class) (q : Var) (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomapvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_cpw1 (syn_cuni (.cv q)))).fv ((syn_chnsicodemap A)).fv := by
    exact
      (show Disjoint ((syn_cpw1 (syn_cuni (.cv q)))).fv ((syn_chnsicodemap A)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap];
          exact
            (show Disjoint (((syn_cuni (.cv q))).fv) ((A).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv q)).fv) ((A).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ q } : Finset Var)) ((A).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show q ∉ (A).fv from (by exact dv_A_q))))))))))
  have p0000 := (Nominal.classEqRefl (syn_chnsiquomap A))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnsiquomap A)
      (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
        (syn_cpw1 (syn_chnord A)))
      p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv
          (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
            (syn_cpw1 (syn_chnord A))) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0001
  have p0003 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_chnord A))
      (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
          (syn_cpw1 (syn_chnord A))) (.cv q))
      (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q)) p0002
      p0003
  have p0005 := @g_fnpw1fn
  have p0006 :=
    @g_a1i (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      p0005
  have p0007 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
  have p0008 := @g_pw1ss1c (syn_chnord A)
  have p0009 := @g_sseli (syn_cpw1 (syn_chnord A)) (syn_c1c) (.cv q) p0008
  have p0010 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv q) (syn_c1c)) p0007
      p0009
  have p0011 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wfn (syn_cpw1fn) (syn_c1c))
      (.classMem (.cv q) (syn_c1c)) p0006 p0010
  have p0012 := @g_fvco2 (syn_c1c) (.cv q) (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)
  have p0013 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (.cv q) (syn_c1c)))
      (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q))
        (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q))))
      p0011 p0012
  have p0014 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q))
      (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q))) p0004
      p0013
  have p0015 := @g_hnwpw1argcl (syn_chnord A) q
  have p0016 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.cv q)
      (syn_csn (syn_cuni (.cv q))) (syn_cpw1fn) p0016
  have p0018 := @g_vex q
  have p0019 := @g_uniex (.cv q) p0018
  have p0020 := @g_pw1fnval (syn_cuni (.cv q)) p0019
  have p0021 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cpw1fn) (syn_csn (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cuni (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0020
  have p0022 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_cpw1fn) (.cv q))
      (syn_cfv (syn_cpw1fn) (syn_csn (syn_cuni (.cv q)))) (syn_cpw1 (syn_cuni (.cv q)))
      p0017 p0021
  have p0023 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_cpw1fn) (.cv q))
      (syn_cpw1 (syn_cuni (.cv q))) (syn_cimage (syn_chnsicodemap A)) p0022
  have p0024 := @g_hnsicodemapexgndv A
  have p0025 := Nominal.mp hyp_hnsiquomapvalndv_1 p0024
  have p0028 := @g_pw1ex (syn_cuni (.cv q)) p0019
  have p0029 :=
    @g_wppfvimage (syn_cpw1 (syn_cuni (.cv q))) (syn_chnsicodemap A) dv_cache_0001 p0025
      p0028
  have p0030 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cpw1 (syn_cuni (.cv q))))
        (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0029
  have p0031 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q)))
      (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cpw1 (syn_cuni (.cv q))))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) p0023 p0030
  have p0032 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q)))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) p0014 p0031
  exact p0032


end NFChoice.DirectNominalPrf.WPPReplay

end
