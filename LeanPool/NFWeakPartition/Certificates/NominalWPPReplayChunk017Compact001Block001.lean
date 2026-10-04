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

/-- Checked nominal proof certificate identified upstream as `g_sifrreflectndv`. -/
@[expose]
noncomputable def gSifrreflectndv (D : Class) (R : Class)
    (hyp_sifrreflectndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_sifrreflectndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCfound) D)) :=
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
  have dv_cache_0001 : q ∉ ((synCsi R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_q_not_R,
          not_false_eq_true])
  have dv_cache_0002 : r ∉ ((synCsi R)).fv :=
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
  have dv_cache_0003 : q ∉ ((synCpw1 (.cv x))).fv :=
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
  have dv_cache_0004 : r ∉ ((synCpw1 (.cv x))).fv :=
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
  have dv_cache_0006 : r ∉ ((synCsn (.cv z))).fv :=
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
      ((Wff.imp (synWbr (synCsn (.cv z)) (synCsi R) (.cv q))
          (.classEq (synCsn (.cv z)) (.cv q)))).fv :=
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
      ((synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))).fv :=
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
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (synCuni (.cv q)))).fv :=
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
  have dv_cache_0010 : y ∉ ((synCuni (.cv q))).fv :=
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
      ((synWral z (.cv x) (.imp (synWbr (.cv z) R (synCuni (.cv q)))
            (.classEq (.cv z) (synCuni (.cv q)))))).fv :=
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
      ((synWrex y (.cv x) (synWral z (.cv x)
            (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))).fv :=
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
      ((synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))).fv :=
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
  have dv_cache_0021 : x ∉ ((synWbr (synCsi R) (synCwe) (synCpw1 D))).fv :=
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
    @gA1i (.classMem R (synCvv)) (synWbr (synCsi R) (synCwe) (synCpw1 D))
      hyp_sifrreflectndv_1
  have p0001 :=
    @gA1i (.classMem D (synCvv)) (synWbr (synCsi R) (synCwe) (synCpw1 D))
      hyp_sifrreflectndv_2
  have p0002 :=
    @gSimpl (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0)))
  have p0003 := (Nominal.classEqRefl (synCwe))
  have p0004 :=
    @gBreqi (synCsi R) (synCpw1 D) (synCwe) (synCin (synCstrict) (synCfound)) p0003
  have p0005 := @gBrin (synCsi R) (synCpw1 D) (synCstrict) (synCfound)
  have p0006 :=
    @gBitri (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCin (synCstrict) (synCfound)) (synCpw1 D))
      (synWa (synWbr (synCsi R) (synCstrict) (synCpw1 D))
        (synWbr (synCsi R) (synCfound) (synCpw1 D)))
      p0004 p0005
  have p0007 :=
    @gSimprbi (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCstrict) (synCpw1 D))
      (synWbr (synCsi R) (synCfound) (synCpw1 D)) p0006
  have p0008 :=
    @gSyl
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCfound) (synCpw1 D)) p0002 p0007
  have p0009 := @gVex x
  have p0010 := @gPw1ex (.cv x) p0009
  have p0011 :=
    @gA1i (.classMem (synCpw1 (.cv x)) (synCvv))
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      p0010
  have p0012 :=
    @gSimpr (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0)))
  have p0013 := @gSimpl (synWss (.cv x) D) (synWne (.cv x) (synC0))
  have p0014 :=
    @gSyl
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))) (synWss (.cv x) D) p0012
      p0013
  have p0015 := @gPw1ss (.cv x) D
  have p0016 :=
    @gSyl
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWss (.cv x) D) (synWss (synCpw1 (.cv x)) (synCpw1 D)) p0014 p0015
  have p0017 :=
    @gSimpr (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0)))
  have p0018 := @gSimpr (synWss (.cv x) D) (synWne (.cv x) (synC0))
  have p0019 :=
    @gSyl
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))) (synWne (.cv x) (synC0))
      p0017 p0018
  have p0020 := @gPw10b (.cv x)
  have p0021 := @gNecon3bii (synCpw1 (.cv x)) (synC0) (.cv x) (synC0) p0020
  have p0022 :=
    @gBiimpri (synWne (synCpw1 (.cv x)) (synC0)) (synWne (.cv x) (synC0)) p0021
  have p0023 :=
    @gSyl
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWne (.cv x) (synC0)) (synWne (synCpw1 (.cv x)) (synC0)) p0019 p0022
  have p0024 :=
    @gFrd
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      q r (synCpw1 D) (synCsi R) (synCvv) (synCpw1 (.cv x)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0011 p0016 p0023
  have p0025 :=
    @gSimpr
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0026 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0027 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (synCpw1 (.cv x))) p0025 p0026
  have p0028 := @gHnwpw1argcl (.cv x) q
  have p0029 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0027 p0028
  have p0030 :=
    @gSimpl (.classMem (synCuni (.cv q)) (.cv x))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (.cv x)) p0029 p0030
  have p0032 := @gVex z
  have p0033 := @gVex q
  have p0034 := @gUniex (.cv q) p0033
  have p0035 := @gBrsnsi (.cv z) (synCuni (.cv q)) R p0032 p0034
  have p0036 :=
    @gBiimpri (synWbr (synCsn (.cv z)) (synCsi R) (synCsn (synCuni (.cv q))))
      (synWbr (.cv z) R (synCuni (.cv q))) p0035
  have p0037 :=
    @gA1i
      (.imp (synWbr (.cv z) R (synCuni (.cv q)))
        (synWbr (synCsn (.cv z)) (synCsi R) (synCsn (synCuni (.cv q)))))
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      p0036
  have p0038 :=
    @gSimpl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0039 :=
    @gSimpr
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0040 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0041 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (synCpw1 (.cv x))) p0039 p0040
  have p0042 := @gHnwpw1argcl (.cv x) q
  have p0043 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0041 p0042
  have p0044 :=
    @gSimpr (.classMem (synCuni (.cv q)) (.cv x))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0045 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0043 p0044
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0038 p0045
  have p0047 :=
    @gEqcomd
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.cv q) (synCsn (synCuni (.cv q))) p0046
  have p0048 :=
    @gBreq2d
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synCsn (synCuni (.cv q))) (.cv q) (synCsn (.cv z)) (synCsi R) p0047
  have p0049 :=
    @gBiimpd
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (synCsn (.cv z)) (synCsi R) (synCsn (synCuni (.cv q))))
      (synWbr (synCsn (.cv z)) (synCsi R) (.cv q)) p0048
  have p0050 :=
    @gSyld
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) R (synCuni (.cv q)))
      (synWbr (synCsn (.cv z)) (synCsi R) (synCsn (synCuni (.cv q))))
      (synWbr (synCsn (.cv z)) (synCsi R) (.cv q)) p0037 p0049
  have p0051 :=
    @gSimpl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0052 :=
    @gSimpr
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0053 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0054 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      p0052 p0053
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      p0051 p0054
  have p0056 :=
    @gSimpr
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0057 := @gSnelpw1 (.cv z) (.cv x)
  have p0058 :=
    @gBiimpri (.classMem (synCsn (.cv z)) (synCpw1 (.cv x)))
      (.classMem (.cv z) (.cv x)) p0057
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (.cv x)) (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))) p0056
      p0058
  have p0060 :=
    @gJca
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))) p0055 p0059
  have p0061 := @gId (.classEq (.cv r) (synCsn (.cv z)))
  have p0062 :=
    @gBreq1d (.classEq (.cv r) (synCsn (.cv z))) (.cv r) (synCsn (.cv z)) (.cv q)
      (synCsi R) p0061
  have p0063 := @gId (.classEq (.cv r) (synCsn (.cv z)))
  have p0064 :=
    @gEqeq1d (.classEq (.cv r) (synCsn (.cv z))) (.cv r) (synCsn (.cv z)) (.cv q) p0063
  have p0065 :=
    @gImbi12d (.classEq (.cv r) (synCsn (.cv z))) (synWbr (.cv r) (synCsi R) (.cv q))
      (synWbr (synCsn (.cv z)) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))
      (.classEq (synCsn (.cv z)) (.cv q)) p0062 p0064
  have p0066 :=
    @gRspccva (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))
      (.imp (synWbr (synCsn (.cv z)) (synCsi R) (.cv q))
        (.classEq (synCsn (.cv z)) (.cv q)))
      r (synCsn (.cv z)) (synCpw1 (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007
      p0065
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
        (.classMem (synCsn (.cv z)) (synCpw1 (.cv x))))
      (.imp (synWbr (synCsn (.cv z)) (synCsi R) (.cv q))
        (.classEq (synCsn (.cv z)) (.cv q)))
      p0060 p0066
  have p0068 :=
    @gSyld
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) R (synCuni (.cv q)))
      (synWbr (synCsn (.cv z)) (synCsi R) (.cv q)) (.classEq (synCsn (.cv z)) (.cv q))
      p0050 p0067
  have p0069 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (synCsn (.cv z)) (.cv q))
  have p0070 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (synCsn (.cv z)) (.cv q))
  have p0071 :=
    @gSimpl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv z) (.cv x))
  have p0072 :=
    @gSimpr
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0073 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0074 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
          (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
      (.classMem (.cv q) (synCpw1 (.cv x))) p0072 p0073
  have p0075 := @gHnwpw1argcl (.cv x) q
  have p0076 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (.cv q) (synCpw1 (.cv x)))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0074 p0075
  have p0077 :=
    @gSimpr (.classMem (synCuni (.cv q)) (.cv x))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0078 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (synCuni (.cv q)) (.cv x))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0076 p0077
  have p0079 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0071 p0078
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
              (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
                (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (synCsn (.cv z)) (.cv q)))
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0070 p0079
  have p0081 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
              (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
                (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (synCsn (.cv z)) (.cv q)))
      (synCsn (.cv z)) (.cv q) (synCsn (synCuni (.cv q))) p0069 p0080
  have p0082 := @gVex z
  have p0083 := @gSneqr (.cv z) (synCuni (.cv q)) p0082
  have p0084 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
              (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
                (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
          (.classMem (.cv z) (.cv x))) (.classEq (synCsn (.cv z)) (.cv q)))
      (.classEq (synCsn (.cv z)) (synCsn (synCuni (.cv q))))
      (.classEq (.cv z) (synCuni (.cv q))) p0081 p0083
  have p0085 :=
    @gEx
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (synCsn (.cv z)) (.cv q)) (.classEq (.cv z) (synCuni (.cv q))) p0084
  have p0086 :=
    @gSyld
      (synWa (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
            (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
              (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) R (synCuni (.cv q))) (.classEq (synCsn (.cv z)) (.cv q))
      (.classEq (.cv z) (synCuni (.cv q))) p0068 p0085
  have p0087 :=
    @gRalrimiva
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.imp (synWbr (.cv z) R (synCuni (.cv q))) (.classEq (.cv z) (synCuni (.cv q))))
      z (.cv x) dv_cache_0008 p0086
  have p0088 :=
    @gJca
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (.classMem (synCuni (.cv q)) (.cv x))
      (synWral z (.cv x) (.imp (synWbr (.cv z) R (synCuni (.cv q)))
          (.classEq (.cv z) (synCuni (.cv q)))))
      p0031 p0087
  have p0089 := @gId (.classEq (.cv y) (synCuni (.cv q)))
  have p0090 :=
    @gBreq2d (.classEq (.cv y) (synCuni (.cv q))) (.cv y) (synCuni (.cv q)) (.cv z) R
      p0089
  have p0091 := @gId (.classEq (.cv y) (synCuni (.cv q)))
  have p0092 :=
    @gEqeq2d (.classEq (.cv y) (synCuni (.cv q))) (.cv y) (synCuni (.cv q)) (.cv z)
      p0091
  have p0093 :=
    @gImbi12d (.classEq (.cv y) (synCuni (.cv q))) (synWbr (.cv z) R (.cv y))
      (synWbr (.cv z) R (synCuni (.cv q))) (.classEq (.cv z) (.cv y))
      (.classEq (.cv z) (synCuni (.cv q))) p0090 p0092
  have p0094 :=
    @gRalbidv (.classEq (.cv y) (synCuni (.cv q)))
      (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (synWbr (.cv z) R (synCuni (.cv q))) (.classEq (.cv z) (synCuni (.cv q))))
      z (.cv x) dv_cache_0009 p0093
  have p0095 :=
    @gRspcev
      (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
      (synWral z (.cv x) (.imp (synWbr (.cv z) R (synCuni (.cv q)))
          (.classEq (.cv z) (synCuni (.cv q)))))
      y (synCuni (.cv q)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0094
  have p0096 :=
    @gSyl
      (synWa (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv q) (synCpw1 (.cv x))) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))))
      (synWa (.classMem (synCuni (.cv q)) (.cv x)) (synWral z (.cv x)
          (.imp (synWbr (.cv z) R (synCuni (.cv q))) (.classEq (.cv z) (synCuni (.cv q))))))
      (synWrex y (.cv x) (synWral z (.cv x)
          (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))
      p0088 p0095
  have p0097_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
        (synWrex q (synCpw1 (.cv x)) (synWral r (synCpw1 (.cv x))
            (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi synCsi synCopab synCwe synCin synCstrict synCfound
          synCpw1
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
    @gRexlimddv
      (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0))))
      (synWral r (synCpw1 (.cv x))
        (.imp (synWbr (.cv r) (synCsi R) (.cv q)) (.classEq (.cv r) (.cv q))))
      (synWrex y (.cv x) (synWral z (.cv x)
          (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))
      q (synCpw1 (.cv x)) dv_cache_0013 dv_cache_0014 p0097_e00_recanon p0096
  have p0098_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (synWss (.cv x) D) (synWne (.cv x) (synC0)))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi synCsi synCopab synCwe synCin synCstrict synCfound
          synCpw1
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
    @gFrrd (synWbr (synCsi R) (synCwe) (synCpw1 D)) x z y D R dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0000 p0001 p0098_e02_recanon
  exact p0098

/-- Checked nominal proof certificate identified upstream as `g_siwereflectndv`. -/
@[expose]
noncomputable def gSiwereflectndv (D : Class) (R : Class)
    (hyp_siwereflectndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_siwereflectndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCwe) D)) :=
  by
  have p0000 := @gSiorreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0001 := @gSifrreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0002 :=
    @gJca (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCstrict) D)
      (synWbr R (synCfound) D) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCwe))
  have p0004 := @gBreqi R D (synCwe) (synCin (synCstrict) (synCfound)) p0003
  have p0005 := @gBrin R D (synCstrict) (synCfound)
  have p0006 :=
    @gBitri (synWbr R (synCwe) D) (synWbr R (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0004 p0005
  have p0007 :=
    @gBiimpri (synWbr R (synCwe) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0006
  have p0008 :=
    @gSyl (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D))
      (synWbr R (synCwe) D) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hndownbrclndv`. -/
@[expose]
noncomputable def gHndownbrclndv (x : Var) (y : Var) (S : Class) (a : Var) (b : Var)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y)
    (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv b)) (synWbr (synCsn (.cv a)) S (synCsn (.cv b)))) :=
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
  have dv_cache_0005 : x ∉ ((synWbr (synCsn (.cv a)) S (synCsn (.cv b)))).fv :=
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
  have dv_cache_0006 : y ∉ ((synWbr (synCsn (.cv a)) S (synCsn (.cv b)))).fv :=
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
  have p0000 := @gVex a
  have p0001 := @gVex b
  have p0002 := @gId (.classEq (.cv x) (.cv a))
  have p0003 := @gSneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @gBreq1d (.classEq (.cv x) (.cv a)) (synCsn (.cv x)) (synCsn (.cv a))
      (synCsn (.cv y)) S p0003
  have p0005 := @gId (.classEq (.cv y) (.cv b))
  have p0006 := @gSneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @gBreq2d (.classEq (.cv y) (.cv b)) (synCsn (.cv y)) (synCsn (.cv b))
      (synCsn (.cv a)) S p0006
  have p0008 := @gEqid (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
  have p0009 :=
    @gBrab (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))
      (synWbr (synCsn (.cv a)) S (synCsn (.cv y)))
      (synWbr (synCsn (.cv a)) S (synCsn (.cv b))) x y (.cv a) (.cv b)
      (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) dv_cache_0001
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

/-- Checked nominal proof certificate identified upstream as `g_hndownexclndv`. -/
@[expose]
noncomputable def gHndownexclndv (x : Var) (y : Var) (S : Class) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_hndownexclndv_1 : Nominal.NPrf (.classMem S (synCvv))) :
    Nominal.NPrf
      (.classMem (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCvv)) :=
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
      ((Wff.classMem (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (synCvv))).fv :=
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
  have p0000 := @gId (.classEq (.cv g) S)
  have p0001 :=
    @gBreqd (.classEq (.cv g) S) (.cv g) S (synCsn (.cv x)) (synCsn (.cv y)) p0000
  have p0002 :=
    @gOpabbidv (.classEq (.cv g) S) (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv x)) S (synCsn (.cv y))) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    @gEleq1d (.classEq (.cv g) S)
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCvv) p0002
  have p0004 := @gHndownexndv x y g dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0005 :=
    @gVtoclg
      (.classMem (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (synCvv))
      (.classMem (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCvv))
      g S (synCvv) dv_cache_0006 dv_cache_0007 p0003 p0004
  have p0006 := Nominal.mp hyp_hndownexclndv_1 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sidownrecoverclndv`. -/
@[expose]
noncomputable def gSidownrecoverclndv (x : Var) (y : Var) (D : Class) (S : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (.classEq
          (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) S)) :=
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
    q ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
    r ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
  have dv_cache_0015 : q ∉ ((synWbr (.cv a) S (.cv b))).fv :=
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
  have dv_cache_0016 : r ∉ ((synWbr (.cv a) S (.cv b))).fv :=
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
    a ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
    b ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
  have dv_cache_0022 : x ∉ ((synCuni (.cv a))).fv :=
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
  have dv_cache_0023 : y ∉ ((synCuni (.cv a))).fv :=
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
  have dv_cache_0024 : x ∉ ((synCuni (.cv b))).fv :=
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
  have dv_cache_0025 : y ∉ ((synCuni (.cv b))).fv :=
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
    x ∉ ((synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b))))).fv :=
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
    y ∉ ((synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b))))).fv :=
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
    a ∉ ((synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))).fv :=
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
    b ∉ ((synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))).fv :=
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
  have dv_cache_0032 : a ∉ ((synWss S (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
  have dv_cache_0033 : b ∉ ((synWss S (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
    @gBrsi q r (.cv a) (.cv b)
      (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gBiimpi
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWex q (synWex r (synW3a (.classEq (.cv a) (synCsn (.cv q)))
            (.classEq (.cv b) (synCsn (.cv r))) (synWbr (.cv q)
              (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r)))))
      p0000
  have p0002 :=
    @gSimp3 (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
      (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r))
  have p0003 :=
    @gHndownbrclndv x y S q r dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0004 :=
    @gBiimpi
      (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r))
      (synWbr (synCsn (.cv q)) S (synCsn (.cv r))) p0003
  have p0005 :=
    @gSyl
      (synW3a (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
        (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv r)))
      (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r))
      (synWbr (synCsn (.cv q)) S (synCsn (.cv r))) p0002 p0004
  have p0006 :=
    @gSimp1 (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
      (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r))
  have p0007 :=
    @gSimp2 (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
      (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r))
  have p0008 :=
    @gBreq12d
      (synW3a (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
        (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv r)))
      (.cv a) (synCsn (.cv q)) (.cv b) (synCsn (.cv r)) S p0006 p0007
  have p0009 :=
    @gBiimprd
      (synW3a (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
        (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv r)))
      (synWbr (.cv a) S (.cv b)) (synWbr (synCsn (.cv q)) S (synCsn (.cv r))) p0008
  have p0010 :=
    @gMpd
      (synW3a (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
        (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv r)))
      (synWbr (synCsn (.cv q)) S (synCsn (.cv r))) (synWbr (.cv a) S (.cv b)) p0005
      p0009
  have p0011 :=
    @gExlimivv
      (synW3a (.classEq (.cv a) (synCsn (.cv q))) (.classEq (.cv b) (synCsn (.cv r)))
        (synWbr (.cv q) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (.cv r)))
      (synWbr (.cv a) S (.cv b)) q r dv_cache_0015 dv_cache_0016 p0010
  have p0012 :=
    @gSyl
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWex q (synWex r (synW3a (.classEq (.cv a) (synCsn (.cv q)))
            (.classEq (.cv b) (synCsn (.cv r))) (synWbr (.cv q)
              (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv r)))))
      (synWbr (.cv a) S (.cv b)) p0001 p0011
  have p0013 :=
    @gA1i
      (.imp (synWbr (.cv a)
          (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
        (synWbr (.cv a) S (.cv b)))
      (synWss S (synCxp (synCpw1 D) (synCpw1 D))) p0012
  have p0014 :=
    @gSimpr (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b))
  have p0015 :=
    @gSimpl (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b))
  have p0017 := (Nominal.biimpRefl (synWbr (.cv a) S (.cv b)))
  have p0018 :=
    @gBiimpi (synWbr (.cv a) S (.cv b)) (.classMem (synCop (.cv a) (.cv b)) S) p0017
  have p0019 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      (synWbr (.cv a) S (.cv b)) (.classMem (synCop (.cv a) (.cv b)) S) p0014 p0018
  have p0020 :=
    @gSseldd
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      S (synCxp (synCpw1 D) (synCpw1 D)) (synCop (.cv a) (.cv b)) p0015 p0019
  have p0021 := @gOpelxp (.cv a) (.cv b) (synCpw1 D) (synCpw1 D)
  have p0022 :=
    @gBiimpi (.classMem (synCop (.cv a) (.cv b)) (synCxp (synCpw1 D) (synCpw1 D)))
      (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D))) p0021
  have p0023 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      (.classMem (synCop (.cv a) (.cv b)) (synCxp (synCpw1 D) (synCpw1 D)))
      (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D))) p0020
      p0022
  have p0024 :=
    @gPw1typedbrndv D (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) b a
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0025 := @gSimpl (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D))
  have p0026 := @gPw1argclcl D (.cv a)
  have p0027 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.classMem (.cv a) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv a)) D) (.classEq (.cv a) (synCsn (synCuni (.cv a)))))
      p0025 p0026
  have p0028 :=
    @gSimpl (.classMem (synCuni (.cv a)) D)
      (.classEq (.cv a) (synCsn (synCuni (.cv a))))
  have p0029 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv a)) D) (.classEq (.cv a) (synCsn (synCuni (.cv a)))))
      (.classMem (synCuni (.cv a)) D) p0027 p0028
  have p0030 := @gElex (synCuni (.cv a)) D
  have p0031 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.classMem (synCuni (.cv a)) D) (.classMem (synCuni (.cv a)) (synCvv)) p0029
      p0030
  have p0032 := @gSimpr (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D))
  have p0033 := @gPw1argclcl D (.cv b)
  have p0034 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.classMem (.cv b) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv b)) D) (.classEq (.cv b) (synCsn (synCuni (.cv b)))))
      p0032 p0033
  have p0035 :=
    @gSimpl (.classMem (synCuni (.cv b)) D)
      (.classEq (.cv b) (synCsn (synCuni (.cv b))))
  have p0036 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv b)) D) (.classEq (.cv b) (synCsn (synCuni (.cv b)))))
      (.classMem (synCuni (.cv b)) D) p0034 p0035
  have p0037 := @gElex (synCuni (.cv b)) D
  have p0038 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.classMem (synCuni (.cv b)) D) (.classMem (synCuni (.cv b)) (synCvv)) p0036
      p0037
  have p0039 :=
    @gJca (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.classMem (synCuni (.cv a)) (synCvv)) (.classMem (synCuni (.cv b)) (synCvv))
      p0031 p0038
  have p0040 :=
    @gSimpl (.classEq (.cv x) (synCuni (.cv a))) (.classEq (.cv y) (synCuni (.cv b)))
  have p0041 :=
    @gSneqd
      (synWa (.classEq (.cv x) (synCuni (.cv a))) (.classEq (.cv y) (synCuni (.cv b))))
      (.cv x) (synCuni (.cv a)) p0040
  have p0042 :=
    @gSimpr (.classEq (.cv x) (synCuni (.cv a))) (.classEq (.cv y) (synCuni (.cv b)))
  have p0043 :=
    @gSneqd
      (synWa (.classEq (.cv x) (synCuni (.cv a))) (.classEq (.cv y) (synCuni (.cv b))))
      (.cv y) (synCuni (.cv b)) p0042
  have p0044 :=
    @gBreq12d
      (synWa (.classEq (.cv x) (synCuni (.cv a))) (.classEq (.cv y) (synCuni (.cv b))))
      (synCsn (.cv x)) (synCsn (synCuni (.cv a))) (synCsn (.cv y))
      (synCsn (synCuni (.cv b))) S p0041 p0043
  have p0045 := @gEqid (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
  have p0046 :=
    @gBrabga (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))
      (synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b)))) x y
      (synCuni (.cv a)) (synCuni (.cv b))
      (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCvv) (synCvv)
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0014 p0044 p0045
  have p0047 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv a)) (synCvv)) (.classMem (synCuni (.cv b)) (synCvv)))
      (synWb (synWbr (synCuni (.cv a))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCuni (.cv b)))
        (synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b)))))
      p0039 p0046
  have p0048 :=
    @gBitrd (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWbr (synCuni (.cv a))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCuni (.cv b)))
      (synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b)))) p0024 p0047
  have p0052 :=
    @gSimpr (.classMem (synCuni (.cv a)) D)
      (.classEq (.cv a) (synCsn (synCuni (.cv a))))
  have p0053 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv a)) D) (.classEq (.cv a) (synCsn (synCuni (.cv a)))))
      (.classEq (.cv a) (synCsn (synCuni (.cv a)))) p0027 p0052
  have p0057 :=
    @gSimpr (.classMem (synCuni (.cv b)) D)
      (.classEq (.cv b) (synCsn (synCuni (.cv b))))
  have p0058 :=
    @gSyl (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv b)) D) (.classEq (.cv b) (synCsn (synCuni (.cv b)))))
      (.classEq (.cv b) (synCsn (synCuni (.cv b)))) p0034 p0057
  have p0059 :=
    @gBreq12d (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (.cv a) (synCsn (synCuni (.cv a))) (.cv b) (synCsn (synCuni (.cv b))) S p0053
      p0058
  have p0060 :=
    @gBicomd (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWbr (.cv a) S (.cv b))
      (synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b)))) p0059
  have p0061 :=
    @gBitrd (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWbr (synCsn (synCuni (.cv a))) S (synCsn (synCuni (.cv b))))
      (synWbr (.cv a) S (.cv b)) p0048 p0060
  have p0062 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      (synWa (.classMem (.cv a) (synCpw1 D)) (.classMem (.cv b) (synCpw1 D)))
      (synWb (synWbr (.cv a)
          (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
        (synWbr (.cv a) S (.cv b)))
      p0023 p0061
  have p0063 :=
    @gBiimprd
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWbr (.cv a) S (.cv b)) p0062
  have p0064 :=
    @gMpd
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b)))
      (synWbr (.cv a) S (.cv b))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      p0014 p0063
  have p0065 :=
    @gEx (synWss S (synCxp (synCpw1 D) (synCpw1 D))) (synWbr (.cv a) S (.cv b))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      p0064
  have p0066 :=
    @gImpbid (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWbr (.cv a) S (.cv b)) p0013 p0065
  have p0067 :=
    (Nominal.biimpRefl (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b)))
  have p0068 :=
    @gBicomi
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (.classMem (synCop (.cv a) (.cv b))
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      p0067
  have p0069 :=
    @gA1i
      (synWb (.classMem (synCop (.cv a) (.cv b))
          (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
        (synWbr (.cv a)
          (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b)))
      (synWss S (synCxp (synCpw1 D) (synCpw1 D))) p0068
  have p0071 :=
    @gBicomi (synWbr (.cv a) S (.cv b)) (.classMem (synCop (.cv a) (.cv b)) S) p0017
  have p0072 :=
    @gA1i (synWb (.classMem (synCop (.cv a) (.cv b)) S) (synWbr (.cv a) S (.cv b)))
      (synWss S (synCxp (synCpw1 D) (synCpw1 D))) p0071
  have p0073 :=
    @gN3bitr4d (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (synWbr (.cv a)
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) (.cv b))
      (synWbr (.cv a) S (.cv b))
      (.classMem (synCop (.cv a) (.cv b))
        (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (synCop (.cv a) (.cv b)) S) p0066 p0069 p0072
  have p0074 :=
    @gEqrelrdv (synWss S (synCxp (synCpw1 D) (synCpw1 D))) a b
      (synCsi (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))) S
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

/-- Checked nominal proof certificate identified upstream as `g_sidownsuppclndv`. -/
@[expose]
noncomputable def gSidownsuppclndv (x : Var) (y : Var) (D : Class) (S : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (synWss (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (synCxp D D))) :=
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
  have dv_cache_0008 : a ∉ ((synWss S (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
  have dv_cache_0009 : b ∉ ((synWss S (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
    a ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
    b ∉ ((synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))).fv :=
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
  have dv_cache_0012 : a ∉ ((synCxp D D)).fv :=
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
  have dv_cache_0013 : b ∉ ((synCxp D D)).fv :=
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
    @gSimpl (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
  have p0001 :=
    @gSimpr (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
  have p0002 :=
    (Nominal.biimpRefl
      (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv b)))
  have p0003 :=
    @gBiimpri
      (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv b))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
      p0002
  have p0004 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
      (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv b))
      p0001 p0003
  have p0005 :=
    @gHndownbrclndv x y S a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0006 :=
    @gBiimpi
      (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv b))
      (synWbr (synCsn (.cv a)) S (synCsn (.cv b))) p0005
  have p0007 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (synWbr (.cv a) (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (.cv b))
      (synWbr (synCsn (.cv a)) S (synCsn (.cv b))) p0004 p0006
  have p0008 := (Nominal.biimpRefl (synWbr (synCsn (.cv a)) S (synCsn (.cv b))))
  have p0009 :=
    @gBiimpi (synWbr (synCsn (.cv a)) S (synCsn (.cv b)))
      (.classMem (synCop (synCsn (.cv a)) (synCsn (.cv b))) S) p0008
  have p0010 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (synWbr (synCsn (.cv a)) S (synCsn (.cv b)))
      (.classMem (synCop (synCsn (.cv a)) (synCsn (.cv b))) S) p0007 p0009
  have p0011 :=
    @gSseldd
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      S (synCxp (synCpw1 D) (synCpw1 D)) (synCop (synCsn (.cv a)) (synCsn (.cv b)))
      p0000 p0010
  have p0012 := @gOpelxp (synCsn (.cv a)) (synCsn (.cv b)) (synCpw1 D) (synCpw1 D)
  have p0013 :=
    @gBiimpi
      (.classMem (synCop (synCsn (.cv a)) (synCsn (.cv b)))
        (synCxp (synCpw1 D) (synCpw1 D)))
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      p0012
  have p0014 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (synCop (synCsn (.cv a)) (synCsn (.cv b)))
        (synCxp (synCpw1 D) (synCpw1 D)))
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      p0011 p0013
  have p0015 :=
    @gSimpl (.classMem (synCsn (.cv a)) (synCpw1 D))
      (.classMem (synCsn (.cv b)) (synCpw1 D))
  have p0016 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      (.classMem (synCsn (.cv a)) (synCpw1 D)) p0014 p0015
  have p0017 := @gSnelpw1 (.cv a) D
  have p0018 :=
    @gA1i (synWb (.classMem (synCsn (.cv a)) (synCpw1 D)) (.classMem (.cv a) D))
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      p0017
  have p0019 :=
    @gMpbid
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (synCsn (.cv a)) (synCpw1 D)) (.classMem (.cv a) D) p0016 p0018
  have p0035 :=
    @gSimpr (.classMem (synCsn (.cv a)) (synCpw1 D))
      (.classMem (synCsn (.cv b)) (synCpw1 D))
  have p0036 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      (.classMem (synCsn (.cv b)) (synCpw1 D)) p0014 p0035
  have p0037 := @gSnelpw1 (.cv b) D
  have p0038 :=
    @gA1i (synWb (.classMem (synCsn (.cv b)) (synCpw1 D)) (.classMem (.cv b) D))
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      p0037
  have p0039 :=
    @gMpbid
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (synCsn (.cv b)) (synCpw1 D)) (.classMem (.cv b) D) p0036 p0038
  have p0040 :=
    @gJca
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (.classMem (.cv a) D) (.classMem (.cv b) D) p0019 p0039
  have p0041 := @gOpelxp (.cv a) (.cv b) D D
  have p0042 :=
    @gBiimpri (.classMem (synCop (.cv a) (.cv b)) (synCxp D D))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)) p0041
  have p0043 :=
    @gSyl
      (synWa (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D))
      (.classMem (synCop (.cv a) (.cv b)) (synCxp D D)) p0040 p0042
  have p0044 :=
    @gEx (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
      (.classMem (synCop (.cv a) (.cv b)) (synCxp D D)) p0043
  have p0045 :=
    @gAlrimivv (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (.imp (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
        (.classMem (synCop (.cv a) (.cv b)) (synCxp D D)))
      a b dv_cache_0008 dv_cache_0009 p0044
  have p0046 :=
    @gSsrel a b (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
      (synCxp D D) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0047 :=
    @gA1i
      (synWb (synWss (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y))))
          (synCxp D D)) (.all a (.all b (.imp (.classMem (synCop (.cv a) (.cv b))
                (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
              (.classMem (synCop (.cv a) (.cv b)) (synCxp D D))))))
      (synWss S (synCxp (synCpw1 D) (synCpw1 D))) p0046
  have p0048 :=
    @gMpbird (synWss S (synCxp (synCpw1 D) (synCpw1 D)))
      (synWss (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))) (synCxp D D))
      (.all a (.all b (.imp (.classMem (synCop (.cv a) (.cv b))
              (synCopab x y (synWbr (synCsn (.cv x)) S (synCsn (.cv y)))))
            (.classMem (synCop (.cv a) (.cv b)) (synCxp D D)))))
      p0045 p0047
  exact p0048

/-- Checked nominal proof certificate identified upstream as `g_pw1subunissclndv`. -/
@[expose]
noncomputable def gPw1subunissclndv (A : Class) (S : Class)
    (hyp_pw1subunissclndv_1 : Nominal.NPrf (.classMem S (synCvv))) :
    Nominal.NPrf (.imp (synWss S (synCpw1 A)) (synWss (synCuni S) A)) :=
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
    g ∉ ((Wff.imp (synWss S (synCpw1 A)) (synWss (synCuni S) A))).fv :=
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
  have p0000 := @gId (.classEq (.cv g) S)
  have p0001 := @gSseq1d (.classEq (.cv g) S) (.cv g) S (synCpw1 A) p0000
  have p0003 := @gUnieqd (.classEq (.cv g) S) (.cv g) S p0000
  have p0004 := @gSseq1d (.classEq (.cv g) S) (synCuni (.cv g)) (synCuni S) A p0003
  have p0005 :=
    @gImbi12d (.classEq (.cv g) S) (synWss (.cv g) (synCpw1 A))
      (synWss S (synCpw1 A)) (synWss (synCuni (.cv g)) A) (synWss (synCuni S) A)
      p0001 p0004
  have p0006 := @gPw1subuniss g A
  have p0007 :=
    @gVtoclg (.imp (synWss (.cv g) (synCpw1 A)) (synWss (synCuni (.cv g)) A))
      (.imp (synWss S (synCpw1 A)) (synWss (synCuni S) A)) g S (synCvv) dv_cache_0001
      dv_cache_0002 p0005 p0006
  have p0008 := Nominal.mp hyp_pw1subunissclndv_1 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hnsireversecodememndv`. -/
@[expose]
noncomputable def gHnsireversecodememndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn (synCpw1 A))) (.classMem (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A))) :=
  by
  have dv_cache_0001 : u ∉ ((synCpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cpw1, dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCuni (synCfv (synC2nd) (.cv u)))).fv :=
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
  have dv_cache_0003 : y ∉ ((synCuni (synCfv (synC2nd) (.cv u)))).fv :=
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
  have dv_cache_0004 : x ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
  have dv_cache_0005 : y ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
      ((synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
            (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (A).fv ((synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))).fv
        from (by
          rw [fv_syn_copab];
          exact
            (show
              Disjoint ((A).fv)
                ((((((synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                              (synCsn (.cv y)))).fv).erase
                        y).erase
                    x) ∪
                  (((({ x } : Finset Var)).erase y).erase x))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint ((A).fv)
                      (((((synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                                  (synCsn (.cv y)))).fv).erase
                            y).erase
                        x)
                    from
                    (Disjoint.mono_right (Finset.erase_subset x _)
                      (show
                        Disjoint ((A).fv)
                          ((((synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                                  (synCsn (.cv y)))).fv).erase
                            y)
                        from
                        (Disjoint.mono_right (Finset.erase_subset y _)
                          (show
                            Disjoint ((A).fv)
                              (((synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                                  (synCsn (.cv y)))).fv)
                            from
                            (by
                              rw [fv_syn_wbr];
                              exact
                                (show
                                  Disjoint ((A).fv)
                                    ((((synCsn (.cv x))).fv) ∪ (((synCsn (.cv y))).fv) ∪
                                      (((synCfv (synC1st) (.cv u))).fv))
                                  from
                                  (Finset.disjoint_union_right.mpr
                                    ⟨(Finset.disjoint_union_right.mpr
                                        ⟨(show Disjoint ((A).fv) (((synCsn (.cv x))).fv)
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
                                          (show Disjoint ((A).fv) (((synCsn (.cv y))).fv)
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
                                          (((synCfv (synC1st) (.cv u))).fv)
                                        from
                                        (by
                                          rw [fv_syn_cfv];
                                          exact
                                            (show
                                              Disjoint ((A).fv)
                                                ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                                                    Disjoint ((A).fv) (((synC1st)).fv)
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
  have p0000 := @gHwcnwendv u (synCpw1 A) dv_cache_0001
  have p0001 := @gHwcnbase u (synCpw1 A) dv_cache_0001
  have p0002 := @gPw1ss1c A
  have p0003 :=
    @gA1i (synWss (synCpw1 A) (synC1c)) (.classMem (.cv u) (synChwcn (synCpw1 A)))
      p0002
  have p0004 :=
    @gSstrd (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC2nd) (.cv u))
      (synCpw1 A) (synC1c) p0001 p0003
  have p0005 := @gEqpw1uni (synCfv (synC2nd) (.cv u))
  have p0006 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC2nd) (.cv u)) (synC1c))
      (.classEq (synCfv (synC2nd) (.cv u)) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0004 p0005
  have p0007 :=
    @gBreq2d (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC2nd) (.cv u))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) (synCfv (synC1st) (.cv u))
      (synCwe) p0006
  have p0008 :=
    @gMpbid (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0000 p0007
  have p0009 := @gHwcnsupp u (synCpw1 A)
  have p0022 :=
    @gXpeq12d (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC2nd) (.cv u))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) p0006 p0006
  have p0023 :=
    @gSseq2d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC1st) (.cv u)) p0022
  have p0024 :=
    @gMpbid (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))
      p0009 p0023
  have p0025 :=
    @gSidownrecoverclndv x y (synCuni (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0026 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))
      (.classEq (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCfv (synC1st) (.cv u)))
      p0024 p0025
  have p0027 :=
    @gBreq1d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCsi (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
      (synCfv (synC1st) (.cv u)) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
      (synCwe) p0026
  have p0028 :=
    @gMpbird (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWbr (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCwe) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0008 p0027
  have p0029 := @gFvex (.cv u) (synC1st)
  have p0030 :=
    @gHndownexclndv x y (synCfv (synC1st) (.cv u)) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0029
  have p0031 := @gFvex (.cv u) (synC2nd)
  have p0032 := @gUniex (synCfv (synC2nd) (.cv u)) p0031
  have p0033 :=
    @gSiwereflectndv (synCuni (synCfv (synC2nd) (.cv u)))
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      p0030 p0032
  have p0034 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWbr (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCwe) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCwe) (synCuni (synCfv (synC2nd) (.cv u))))
      p0028 p0033
  have p0037 := @gPw1subunissclndv A (synCfv (synC2nd) (.cv u)) p0031
  have p0038 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC2nd) (.cv u)) (synCpw1 A))
      (synWss (synCuni (synCfv (synC2nd) (.cv u))) A) p0001 p0037
  have p0039 :=
    @gJca (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWbr (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCwe) (synCuni (synCfv (synC2nd) (.cv u))))
      (synWss (synCuni (synCfv (synC2nd) (.cv u))) A) p0034 p0038
  have p0044 :=
    @gElhwcodes A (synCuni (synCfv (synC2nd) (.cv u)))
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      dv_cache_0007 p0030 p0032
  have p0045 :=
    @gBiimpri
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcodes A))
      (synWa (synWbr (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCwe) (synCuni (synCfv (synC2nd) (.cv u))))
        (synWss (synCuni (synCfv (synC2nd) (.cv u))) A))
      p0044
  have p0046 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWa (synWbr (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCwe) (synCuni (synCfv (synC2nd) (.cv u))))
        (synWss (synCuni (synCfv (synC2nd) (.cv u))) A))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcodes A))
      p0039 p0045
  have p0063 :=
    @gSidownsuppclndv x y (synCuni (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0064 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))
      (synWss (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCxp (synCuni (synCfv (synC2nd) (.cv u)))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      p0024 p0063
  have p0069 :=
    @gOpfv1st
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0030 p0032
  have p0074 :=
    @gOpfv2nd
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0030 p0032
  have p0080 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCuni (synCfv (synC2nd) (.cv u)))
      (synCfv (synC2nd) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0074 p0074
  have p0081 :=
    @gSseq12i
      (synCfv (synC1st) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCxp (synCfv (synC2nd) (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCfv (synC2nd) (synCop
            (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCxp (synCuni (synCfv (synC2nd) (.cv u))) (synCuni (synCfv (synC2nd) (.cv u))))
      p0069 p0080
  have p0082 :=
    @gA1i
      (synWb (synWss (synCfv (synC1st) (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd) (synCop
                (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                    (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u)))))
            (synCfv (synC2nd) (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))) (synWss (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCxp (synCuni (synCfv (synC2nd) (.cv u)))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn (synCpw1 A))) p0081
  have p0083 :=
    @gMpbird (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd) (synCop
              (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                  (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC2nd) (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      (synWss (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCxp (synCuni (synCfv (synC2nd) (.cv u)))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      p0064 p0082
  have p0084 :=
    @gJca (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcodes A))
      (synWss (synCfv (synC1st) (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd) (synCop
              (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                  (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC2nd) (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      p0046 p0083
  have p0089 :=
    @gOpex
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0030 p0032
  have p0090 :=
    @gElhwcncl A
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
  have p0091 := Nominal.mp p0089 p0090
  have p0092 :=
    @gBiimpri
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A))
      (synWa (.classMem (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcodes A)) (synWss
          (synCfv (synC1st) (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd) (synCop
                (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                    (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u)))))
            (synCfv (synC2nd) (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))))
      p0091
  have p0093 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWa (.classMem (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcodes A)) (synWss
          (synCfv (synC1st) (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd) (synCop
                (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                    (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u)))))
            (synCfv (synC2nd) (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A))
      p0084 p0092
  exact p0093

/-- Checked nominal proof certificate identified upstream as `g_hnsireversecodeidndv`. -/
@[expose]
noncomputable def gHnsireversecodeidndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (_dv_A_x : x ∉ A.fv) (_dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn (synCpw1 A))) (.classEq (.cv u) (synCop (synCsi
              (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                  (synCsn (.cv y))))) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))) :=
  by
  have dv_cache_0001 : u ∉ ((synCpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cpw1, dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCuni (synCfv (synC2nd) (.cv u)))).fv :=
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
  have dv_cache_0003 : y ∉ ((synCuni (synCfv (synC2nd) (.cv u)))).fv :=
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
  have dv_cache_0004 : x ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
  have dv_cache_0005 : y ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
  have p0000 := @gHwcnpair u (synCpw1 A)
  have p0001 := @gHwcnsupp u (synCpw1 A)
  have p0002 := @gHwcnbase u (synCpw1 A) dv_cache_0001
  have p0003 := @gPw1ss1c A
  have p0004 :=
    @gA1i (synWss (synCpw1 A) (synC1c)) (.classMem (.cv u) (synChwcn (synCpw1 A)))
      p0003
  have p0005 :=
    @gSstrd (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC2nd) (.cv u))
      (synCpw1 A) (synC1c) p0002 p0004
  have p0006 := @gEqpw1uni (synCfv (synC2nd) (.cv u))
  have p0007 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC2nd) (.cv u)) (synC1c))
      (.classEq (synCfv (synC2nd) (.cv u)) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0005 p0006
  have p0014 :=
    @gXpeq12d (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC2nd) (.cv u))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) p0007 p0007
  have p0015 :=
    @gSseq2d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC1st) (.cv u)) p0014
  have p0016 :=
    @gMpbid (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))
      p0001 p0015
  have p0017 :=
    @gSidownrecoverclndv x y (synCuni (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0018 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))))
      (.classEq (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCfv (synC1st) (.cv u)))
      p0016 p0017
  have p0019 :=
    @gEqcomd (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCsi (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
      (synCfv (synC1st) (.cv u)) p0018
  have p0026 :=
    @gOpeq12d (.classMem (.cv u) (synChwcn (synCpw1 A))) (synCfv (synC1st) (.cv u))
      (synCsi (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
      (synCfv (synC2nd) (.cv u)) (synCpw1 (synCuni (synCfv (synC2nd) (.cv u))))
      p0019 p0007
  have p0027 :=
    @gEqtrd (.classMem (.cv u) (synChwcn (synCpw1 A))) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCop (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
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

/-- Checked nominal proof certificate identified upstream as `g_sieqdndv`. -/
@[expose]
noncomputable def gSieqdndv (ph : Wff) (A : Class) (B : Class)
    (hyp_sieqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCsi A) (synCsi B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSi x y z w A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @gA1i
      (.classEq (synCsi A) (synCopab x y (synWex z (synWex w
              (synW3a (.classEq (.cv x) (synCsn (.cv z)))
                (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) A (.cv w)))))))
      ph p0000
  have p0002 := @gBreqd ph A B (.cv z) (.cv w) hyp_sieqdndv_1
  have p0003 :=
    @gN3anbi3d ph (synWbr (.cv z) A (.cv w)) (synWbr (.cv z) B (.cv w))
      (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w))) p0002
  have p0004 :=
    @gN2exbidv ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) A (.cv w)))
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) B (.cv w)))
      z w dv_cache_0011 dv_cache_0012 p0003
  have p0005 :=
    @gOpabbidv ph
      (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) A (.cv w)))))
      (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) B (.cv w)))))
      x y dv_cache_0013 dv_cache_0014 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSi x y z w B
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @gEqcomi (synCsi B)
      (synCopab x y (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
              (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) B (.cv w))))))
      p0006
  have p0008 :=
    @gA1i
      (.classEq (synCopab x y (synWex z (synWex w
              (synW3a (.classEq (.cv x) (synCsn (.cv z)))
                (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) B (.cv w))))))
        (synCsi B))
      ph p0007
  have p0009 :=
    @gN3eqtrd ph (synCsi A)
      (synCopab x y (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
              (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) A (.cv w))))))
      (synCopab x y (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
              (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) B (.cv w))))))
      (synCsi B) p0001 p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapvalclndv`. -/
@[expose]
noncomputable def gHnsicodemapvalclndv (A : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 (synChwcn A))) (.classEq (synCfv (synChnsicodemap A) Q)
          (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
            (synCpw1 (synCfv (synC2nd) (synCuni Q)))))) :=
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
      ((Wff.imp (.classMem Q (synCpw1 (synChwcn A)))
          (.classEq (synCfv (synChnsicodemap A) Q)
            (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
              (synCpw1 (synCfv (synC2nd) (synCuni Q))))))).fv :=
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
  have p0000 := @gElex Q (synCpw1 (synChwcn A))
  have p0001 := @gId (.classEq (.cv q) Q)
  have p0002 := @gEleq1d (.classEq (.cv q) Q) (.cv q) Q (synCpw1 (synChwcn A)) p0001
  have p0004 := @gFveq2d (.classEq (.cv q) Q) (.cv q) Q (synChnsicodemap A) p0001
  have p0006 := @gUnieqd (.classEq (.cv q) Q) (.cv q) Q p0001
  have p0007 :=
    @gFveq2d (.classEq (.cv q) Q) (synCuni (.cv q)) (synCuni Q) (synC1st) p0006
  have p0008 :=
    @gSieqdndv (.classEq (.cv q) Q) (synCfv (synC1st) (synCuni (.cv q)))
      (synCfv (synC1st) (synCuni Q)) p0007
  have p0011 :=
    @gFveq2d (.classEq (.cv q) Q) (synCuni (.cv q)) (synCuni Q) (synC2nd) p0006
  have p0012 :=
    @gPw1eq (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni Q))
  have p0013 :=
    @gSyl (.classEq (.cv q) Q)
      (.classEq (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni Q)))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni Q))))
      p0011 p0012
  have p0014 :=
    @gOpeq12d (.classEq (.cv q) Q) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCsi (synCfv (synC1st) (synCuni Q)))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
      (synCpw1 (synCfv (synC2nd) (synCuni Q))) p0008 p0013
  have p0015 :=
    @gEqeq12d (.classEq (.cv q) Q) (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synChnsicodemap A) Q)
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
        (synCpw1 (synCfv (synC2nd) (synCuni Q))))
      p0004 p0014
  have p0016 :=
    @gImbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem Q (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (.cv q))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      (.classEq (synCfv (synChnsicodemap A) Q)
        (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
          (synCpw1 (synCfv (synC2nd) (synCuni Q)))))
      p0002 p0015
  have p0017 := @gHnsicodemapvalndv A q dv_cache_0001
  have p0018 :=
    @gVtoclg
      (.imp (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))))
      (.imp (.classMem Q (synCpw1 (synChwcn A))) (.classEq (synCfv (synChnsicodemap A) Q)
          (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
            (synCpw1 (synCfv (synC2nd) (synCuni Q))))))
      q Q (synCvv) dv_cache_0002 dv_cache_0003 p0016 p0017
  have p0019 :=
    @gMpcom (.classMem Q (synCvv)) (.classMem Q (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) Q)
        (synCop (synCsi (synCfv (synC1st) (synCuni Q)))
          (synCpw1 (synCfv (synC2nd) (synCuni Q)))))
      p0000 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapfondv`. -/
@[expose]
noncomputable def gHnsicodemapfondv (A : Class) :
    Nominal.NPrf
      (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))) :=
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
  have dv_cache_0007 : x ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
  have dv_cache_0008 : y ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
      ((synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u)))))).fv :=
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
  have dv_cache_0010 : q ∉ ((synCpw1 (synChwcn A))).fv :=
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
      ((Wff.classEq (.cv u) (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u)))))))).fv :=
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
  have dv_cache_0012 : u ∉ ((synCpw1 (synChwcn A))).fv :=
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
  have dv_cache_0013 : q ∉ ((synChwcn (synCpw1 A))).fv :=
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
  have dv_cache_0014 : u ∉ ((synChwcn (synCpw1 A))).fv :=
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
  have dv_cache_0015 : q ∉ ((synChnsicodemap A)).fv :=
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
  have dv_cache_0016 : u ∉ ((synChnsicodemap A)).fv :=
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
  have p0000 := @gHnsicodemapfndv A
  have p0001 :=
    @gHnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @gSnelpw1
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (synChwcn A)
  have p0003 :=
    @gA1i
      (synWb (.classMem (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u))))) (synCpw1 (synChwcn A))) (.classMem
          (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A)))
      (.classMem (.cv u) (synChwcn (synCpw1 A))) p0002
  have p0004 :=
    @gMpbird (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCpw1 (synChwcn A)))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A))
      p0001 p0003
  have p0005 :=
    @gHnsireversecodeidndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0010 :=
    @gHnsicodemapvalclndv A
      (synCsn (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
  have p0011 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))) (synCop (synCsi (synCfv (synC1st)
              (synCuni (synCsn (synCop (synCopab x y
                      (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                        (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u))))))))
          (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                      (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u))
                        (synCsn (.cv y)))) (synCuni (synCfv (synC2nd) (.cv u))))))))))
      p0004 p0010
  have p0013 :=
    @gElex
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (synChwcn A)
  have p0014 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synChwcn A))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synCvv))
      p0001 p0013
  have p0015 :=
    @gUnisng
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (synCvv)
  have p0016 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))) (synCvv))
      (.classEq (synCuni (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      p0014 p0015
  have p0017 :=
    @gFveq2d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCuni (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (synC1st) p0016
  have p0018 := @gFvex (.cv u) (synC1st)
  have p0019 :=
    @gHndownexclndv x y (synCfv (synC1st) (.cv u)) dv_cache_0007 dv_cache_0008
      dv_cache_0006 p0018
  have p0020 := @gFvex (.cv u) (synC2nd)
  have p0021 := @gUniex (synCfv (synC2nd) (.cv u)) p0020
  have p0022 :=
    @gOpfv1st
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0019 p0021
  have p0023 :=
    @gA1i
      (.classEq (synCfv (synC1st) (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
      (.classMem (.cv u) (synChwcn (synCpw1 A))) p0022
  have p0024 :=
    @gEqtrd (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCfv (synC1st) (synCuni (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      (synCfv (synC1st) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      p0017 p0023
  have p0025 :=
    @gSieqdndv (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCfv (synC1st) (synCuni (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      p0024
  have p0031 :=
    @gFveq2d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCuni (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCop (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (synC2nd) p0016
  have p0036 :=
    @gOpfv2nd
      (synCopab x y (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0019 p0021
  have p0037 :=
    @gA1i
      (.classEq (synCfv (synC2nd) (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCuni (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn (synCpw1 A))) p0036
  have p0038 :=
    @gEqtrd (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      (synCfv (synC2nd) (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCuni (synCfv (synC2nd) (.cv u))) p0031 p0037
  have p0039 :=
    @gPw1eq
      (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      (synCuni (synCfv (synC2nd) (.cv u)))
  have p0040 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classEq (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u)))))))
        (synCuni (synCfv (synC2nd) (.cv u))))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                    (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                  (synCuni (synCfv (synC2nd) (.cv u))))))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0038 p0039
  have p0041 :=
    @gOpeq12d (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCsi (synCfv (synC1st) (synCuni (synCsn (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))))
      (synCsi (synCopab x y
          (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))))
      (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))) p0025 p0040
  have p0042 :=
    @gEqtrd (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn (synCop (synCopab x y
                    (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                  (synCuni (synCfv (synC2nd) (.cv u)))))))) (synCpw1 (synCfv (synC2nd)
            (synCuni (synCsn (synCop (synCopab x y
                    (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                  (synCuni (synCfv (synC2nd) (.cv u)))))))))
      (synCop (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0011 p0041
  have p0043 :=
    @gEqcomd (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCop (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      p0042
  have p0044 :=
    @gEqtrd (.classMem (.cv u) (synChwcn (synCpw1 A))) (.cv u)
      (synCop (synCsi (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y)))))
        (synCpw1 (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      p0005 p0043
  have p0045 :=
    @gJca (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))) (synCpw1 (synChwcn A)))
      (.classEq (.cv u) (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      p0004 p0044
  have p0046 :=
    @gId
      (.classEq (.cv q) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
  have p0047 :=
    @gFveq2d
      (.classEq (.cv q) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (.cv q)
      (synCsn (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synChnsicodemap A) p0046
  have p0048 :=
    @gEqeq2d
      (.classEq (.cv q) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
              (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
            (synCuni (synCfv (synC2nd) (.cv u))))))
      (.cv u) p0047
  have p0049 :=
    @gRspcev (.classEq (.cv u) (synCfv (synChnsicodemap A) (.cv q)))
      (.classEq (.cv u) (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u)))))))
      q
      (synCsn (synCop (synCopab x y
            (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
          (synCuni (synCfv (synC2nd) (.cv u)))))
      (synCpw1 (synChwcn A)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0048
  have p0050 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 A)))
      (synWa (.classMem (synCsn (synCop (synCopab x y
                (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
              (synCuni (synCfv (synC2nd) (.cv u))))) (synCpw1 (synChwcn A)))
        (.classEq (.cv u) (synCfv (synChnsicodemap A) (synCsn (synCop (synCopab x y
                  (synWbr (synCsn (.cv x)) (synCfv (synC1st) (.cv u)) (synCsn (.cv y))))
                (synCuni (synCfv (synC2nd) (.cv u))))))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv u) (synCfv (synChnsicodemap A) (.cv q))))
      p0045 p0049
  have p0051 :=
    @gRgen
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv u) (synCfv (synChnsicodemap A) (.cv q))))
      u (synChwcn (synCpw1 A)) p0050
  have p0052 :=
    @gPm32i
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWral u (synChwcn (synCpw1 A)) (synWrex q (synCpw1 (synChwcn A))
          (.classEq (.cv u) (synCfv (synChnsicodemap A) (.cv q)))))
      p0000 p0051
  have p0053 :=
    @gDffo3 q u (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synChnsicodemap A)
      dv_cache_0010 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017
  have p0054 :=
    @gBiimpri
      (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (synWral u (synChwcn (synCpw1 A)) (synWrex q (synCpw1 (synChwcn A))
            (.classEq (.cv u) (synCfv (synChnsicodemap A) (.cv q))))))
      p0053
  have p0055 := Nominal.mp p0052 p0054
  exact p0055

/-- Checked nominal proof certificate identified upstream as `g_siinjndv`. -/
@[expose]
noncomputable def gSiinjndv (ph : Wff) (R : Class) (S : Class)
    (hyp_siinjndv_1 : Nominal.NPrf (.imp ph (.classEq (synCsi R) (synCsi S)))) :
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
    @gBreqd ph (synCsi R) (synCsi S) (synCsn (.cv x)) (synCsn (.cv y)) hyp_siinjndv_1
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gBrsnsi (.cv x) (.cv y) R p0001 p0002
  have p0004 :=
    @gA1i
      (synWb (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      ph p0003
  have p0005 :=
    @gBicomd ph (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0004
  have p0008 := @gBrsnsi (.cv x) (.cv y) S p0001 p0002
  have p0009 :=
    @gA1i
      (synWb (synWbr (synCsn (.cv x)) (synCsi S) (synCsn (.cv y)))
        (synWbr (.cv x) S (.cv y)))
      ph p0008
  have p0010 :=
    @gBicomd ph (synWbr (synCsn (.cv x)) (synCsi S) (synCsn (.cv y)))
      (synWbr (.cv x) S (.cv y)) p0009
  have p0011 :=
    @gN3bitr4d ph (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
      (synWbr (synCsn (.cv x)) (synCsi S) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv y)) p0000 p0005 p0010
  have p0012 := (Nominal.biimpRefl (synWbr (.cv x) R (.cv y)))
  have p0013 :=
    @gBicomi (synWbr (.cv x) R (.cv y)) (.classMem (synCop (.cv x) (.cv y)) R) p0012
  have p0014 :=
    @gA1i (synWb (.classMem (synCop (.cv x) (.cv y)) R) (synWbr (.cv x) R (.cv y))) ph
      p0013
  have p0015 := (Nominal.biimpRefl (synWbr (.cv x) S (.cv y)))
  have p0016 :=
    @gBicomi (synWbr (.cv x) S (.cv y)) (.classMem (synCop (.cv x) (.cv y)) S) p0015
  have p0017 :=
    @gA1i (synWb (.classMem (synCop (.cv x) (.cv y)) S) (synWbr (.cv x) S (.cv y))) ph
      p0016
  have p0018 :=
    @gN3bitr4d ph (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) R) (.classMem (synCop (.cv x) (.cv y)) S)
      p0011 p0014 p0017
  have p0019 :=
    @gEqrelrdv ph x y R S dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_hwcnpairclndv`. -/
@[expose]
noncomputable def gHwcnpairclndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A))
        (.classEq B (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B)))) :=
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
      ((Wff.imp (.classMem B (synChwcn A))
          (.classEq B (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B))))).fv :=
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
  have p0000 := @gElex B (synChwcn A)
  have p0001 := @gId (.classEq (.cv u) B)
  have p0002 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0001
  have p0005 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC1st) p0001
  have p0007 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC2nd) p0001
  have p0008 :=
    @gOpeq12d (.classEq (.cv u) B) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B)
      (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B) p0005 p0007
  have p0009 :=
    @gEqeq12d (.classEq (.cv u) B) (.cv u) B
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B)) p0001 p0008
  have p0010 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classEq B (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B))) p0002 p0009
  have p0011 := @gHwcnpair u A
  have p0012 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem B (synChwcn A))
        (.classEq B (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B))))
      u B (synCvv) dv_cache_0001 dv_cache_0002 p0010 p0011
  have p0013 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B (synChwcn A))
      (.classEq B (synCop (synCfv (synC1st) B) (synCfv (synC2nd) B))) p0000 p0012
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

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapf1ndv`. -/
@[expose]
noncomputable def gHnsicodemapf1ndv (A : Class) :
    Nominal.NPrf
      (synWf1 (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))) :=
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
  have dv_cache_0003 : r ∉ ((Wff.classMem (.cv q) (synCpw1 (synChwcn A)))).fv :=
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
  have dv_cache_0004 : q ∉ ((synCpw1 (synChwcn A))).fv :=
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
  have dv_cache_0005 : r ∉ ((synCpw1 (synChwcn A))).fv :=
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
  have dv_cache_0006 : q ∉ ((synChnsicodemap A)).fv :=
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
  have dv_cache_0007 : r ∉ ((synChnsicodemap A)).fv :=
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
  have p0000 := @gHnsicodemapfndv A
  have p0001 :=
    @gSimpl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) (.cv r)))
  have p0002 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv q) (synCpw1 (synChwcn A))) p0001 p0002
  have p0004 := @gHnwpw1argcl (synChwcn A) q
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0003 p0004
  have p0006 :=
    @gSimpr (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005 p0006
  have p0013 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChwcn A)) p0005 p0013
  have p0015 := @gHwcnpairclndv A (synCuni (.cv q))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0014 p0015
  have p0020 := @gHnsicodemapvalndv A q dv_cache_0001
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (.cv q))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      p0003 p0020
  have p0022 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      p0021
  have p0023 :=
    @gSimpr
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) (.cv r)))
  have p0025 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv r) (synCpw1 (synChwcn A))) p0001 p0025
  have p0027 := @gHnsicodemapvalndv A r dv_cache_0002
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (.cv r))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0026 p0027
  have p0029 :=
    @gN3eqtrd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) (.cv r))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      p0022 p0023 p0028
  have p0030 :=
    @gOpth (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
      (synCsi (synCfv (synC1st) (synCuni (.cv r))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))
  have p0031 :=
    @gBiimpi
      (.classEq (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (synWa (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
        (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classEq (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (synWa (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
        (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0029 p0031
  have p0033 :=
    @gSimpl
      (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
        (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
      p0032 p0033
  have p0035 :=
    @gSiinjndv
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC1st) (synCuni (.cv r)))
      p0034
  have p0052 :=
    @gSimpr
      (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
  have p0053 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classEq (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
        (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      p0032 p0052
  have p0054 :=
    @gPw111 (synCfv (synC2nd) (synCuni (.cv q)))
      (synCfv (synC2nd) (synCuni (.cv r)))
  have p0055 :=
    @gBiimpi
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (.classEq (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv r))))
      p0054
  have p0056 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classEq (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (.classEq (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv r))))
      p0053 p0055
  have p0057 :=
    @gOpeq12d
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC1st) (synCuni (.cv r)))
      (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv r)))
      p0035 p0056
  have p0061 := @gHnwpw1argcl (synChwcn A) r
  have p0062 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      p0026 p0061
  have p0063 :=
    @gSimpl (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
  have p0064 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      (.classMem (synCuni (.cv r)) (synChwcn A)) p0062 p0063
  have p0065 := @gHwcnpairclndv A (synCuni (.cv r))
  have p0066 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (synCuni (.cv r)) (synCop (synCfv (synC1st) (synCuni (.cv r)))
          (synCfv (synC2nd) (synCuni (.cv r)))))
      p0064 p0065
  have p0067 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCuni (.cv r))
      (synCop (synCfv (synC1st) (synCuni (.cv r))) (synCfv (synC2nd) (synCuni (.cv r))))
      p0066
  have p0068 :=
    @gN3eqtrd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCuni (.cv q))
      (synCop (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv q))))
      (synCop (synCfv (synC1st) (synCuni (.cv r))) (synCfv (synC2nd) (synCuni (.cv r))))
      (synCuni (.cv r)) p0016 p0057 p0067
  have p0069 :=
    @gSneqd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synCuni (.cv q)) (synCuni (.cv r)) p0068
  have p0075 :=
    @gSimpr (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
  have p0076 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      (.classEq (.cv r) (synCsn (synCuni (.cv r)))) p0062 p0075
  have p0077 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.cv r) (synCsn (synCuni (.cv r))) p0076
  have p0078 :=
    @gN3eqtrd
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))))
      (.cv q) (synCsn (synCuni (.cv q))) (synCsn (synCuni (.cv r))) (.cv r) p0007
      p0069 p0077
  have p0079 :=
    @gEx
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0078
  have p0080 :=
    @gEx (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.imp (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))
      p0079
  have p0081 :=
    @gRalrimiv (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.imp (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))
      r (synCpw1 (synChwcn A)) dv_cache_0003 p0080
  have p0082 :=
    @gRgen
      (synWral r (synCpw1 (synChwcn A)) (.imp
          (.classEq (synCfv (synChnsicodemap A) (.cv q))
            (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))
      q (synCpw1 (synChwcn A)) p0081
  have p0083 :=
    @gPm32i
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWral q (synCpw1 (synChwcn A)) (synWral r (synCpw1 (synChwcn A)) (.imp
            (.classEq (synCfv (synChnsicodemap A) (.cv q))
              (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0000 p0082
  have p0084 :=
    @gDff13 q r (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synChnsicodemap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0085_e00_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
          (synWral q (synCpw1 (synChwcn A)) (synWral r (synCpw1 (synChwcn A)) (.imp
                (.classEq (synCfv (synChnsicodemap A) (.cv q))
                  (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synChnsicodemap synCres
          synChnsicodeliftfn synCtxp synClnpwsirelfn synClnpwpw1secondfn synCpw1
          synChwcn
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
    @gBiimpri
      (synWf1 (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (synWral q (synCpw1 (synChwcn A)) (synWral r (synCpw1 (synChwcn A)) (.imp
              (.classEq (synCfv (synChnsicodemap A) (.cv q))
                (synCfv (synChnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0085_e00_recanon
  have p0086 := Nominal.mp p0083 p0085
  exact p0086

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapf1ondv`. -/
@[expose]
noncomputable def gHnsicodemapf1ondv (A : Class) :
    Nominal.NPrf
      (synWf1o (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))) :=
  by
  have p0000 := @gHnsicodemapf1ndv A
  have p0001 := @gHnsicodemapfondv A
  have p0002 :=
    @gPm32i
      (synWf1 (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (synWf1o (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))))
  have p0004 :=
    @gBiimpri
      (synWf1o (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (synWf1 (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))))
      p0003
  have p0005 := Nominal.mp p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapexgndv`. -/
@[expose]
noncomputable def gHnsiquomapexgndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (.classMem (synChnsiquomap A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnsiquomap A))
  have p0001 :=
    @gA1i
      (.classEq (synChnsiquomap A)
        (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
          (synCpw1 (synChnord A))))
      (.classMem A (synCvv)) p0000
  have p0002 := @gHnsicodemapexgndv A
  have p0003 := @gImageexg (synChnsicodemap A) (synCvv)
  have p0004 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChnsicodemap A) (synCvv))
      (.classMem (synCimage (synChnsicodemap A)) (synCvv)) p0002 p0003
  have p0005 := @gPw1fnex
  have p0006 := @gA1i (.classMem (synCpw1fn) (synCvv)) (.classMem A (synCvv)) p0005
  have p0007 :=
    @gJca (.classMem A (synCvv)) (.classMem (synCimage (synChnsicodemap A)) (synCvv))
      (.classMem (synCpw1fn) (synCvv)) p0004 p0006
  have p0008 :=
    @gCoexg (synCimage (synChnsicodemap A)) (synCpw1fn) (synCvv) (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCimage (synChnsicodemap A)) (synCvv))
        (.classMem (synCpw1fn) (synCvv)))
      (.classMem (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (synCvv))
      p0007 p0008
  have p0010 := @gHnordexg A
  have p0011 := @gPw1exg (synChnord A) (synCvv)
  have p0012 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChnord A) (synCvv))
      (.classMem (synCpw1 (synChnord A)) (synCvv)) p0010 p0011
  have p0013 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (synCvv))
      (.classMem (synCpw1 (synChnord A)) (synCvv)) p0009 p0012
  have p0014 :=
    @gResexg (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
      (synCpw1 (synChnord A)) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (synCvv))
        (.classMem (synCpw1 (synChnord A)) (synCvv)))
      (.classMem (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
          (synCpw1 (synChnord A))) (synCvv))
      p0013 p0014
  have p0016 :=
    @gEqeltrd (.classMem A (synCvv)) (synChnsiquomap A)
      (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
        (synCpw1 (synChnord A)))
      (synCvv) p0001 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapfnndv`. -/
@[expose]
noncomputable def gHnsiquomapfnndv (A : Class)
    (hyp_hnsiquomapfnndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWfn (synChnsiquomap A) (synCpw1 (synChnord A))) :=
  by
  have p0000 := @gHnsicodemapexgndv A
  have p0001 := Nominal.mp hyp_hnsiquomapfnndv_1 p0000
  have p0002 := @gWppimagefn (synChnsicodemap A) p0001
  have p0003 := @gFnpw1fn
  have p0004 := @gSsv (synCrn (synCpw1fn))
  have p0005 :=
    @gN3pm32i (synWfn (synCimage (synChnsicodemap A)) (synCvv))
      (synWfn (synCpw1fn) (synC1c)) (synWss (synCrn (synCpw1fn)) (synCvv)) p0002
      p0003 p0004
  have p0006 := @gFnco (synCvv) (synC1c) (synCimage (synChnsicodemap A)) (synCpw1fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gPw1ss1c (synChnord A)
  have p0009 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (synC1c))
      (synWss (synCpw1 (synChnord A)) (synC1c)) p0007 p0008
  have p0010 :=
    @gFnssres (synC1c) (synCpw1 (synChnord A))
      (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := (Nominal.classEqRefl (synChnsiquomap A))
  have p0013 :=
    @gFneq1i (synCpw1 (synChnord A)) (synChnsiquomap A)
      (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
        (synCpw1 (synChnord A)))
      p0012
  have p0014 :=
    @gMpbir (synWfn (synChnsiquomap A) (synCpw1 (synChnord A)))
      (synWfn (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
          (synCpw1 (synChnord A))) (synCpw1 (synChnord A)))
      p0011 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapvalndv`. -/
@[expose]
noncomputable def gHnsiquomapvalndv (A : Class) (q : Var) (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomapvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((synCpw1 (synCuni (.cv q)))).fv ((synChnsicodemap A)).fv := by
    exact
      (show Disjoint ((synCpw1 (synCuni (.cv q)))).fv ((synChnsicodemap A)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap];
          exact
            (show Disjoint (((synCuni (.cv q))).fv) ((A).fv) from
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
  have p0000 := (Nominal.classEqRefl (synChnsiquomap A))
  have p0001 :=
    @gFveq1i (.cv q) (synChnsiquomap A)
      (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
        (synCpw1 (synChnord A)))
      p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv
          (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
            (synCpw1 (synChnord A))) (.cv q)))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0001
  have p0003 :=
    @gFvres (.cv q) (synCpw1 (synChnord A))
      (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
  have p0004 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCfv (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn))
          (synCpw1 (synChnord A))) (.cv q))
      (synCfv (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (.cv q)) p0002
      p0003
  have p0005 := @gFnpw1fn
  have p0006 :=
    @gA1i (synWfn (synCpw1fn) (synC1c)) (.classMem (.cv q) (synCpw1 (synChnord A)))
      p0005
  have p0007 := @gId (.classMem (.cv q) (synCpw1 (synChnord A)))
  have p0008 := @gPw1ss1c (synChnord A)
  have p0009 := @gSseli (synCpw1 (synChnord A)) (synC1c) (.cv q) p0008
  have p0010 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (.cv q) (synCpw1 (synChnord A))) (.classMem (.cv q) (synC1c)) p0007
      p0009
  have p0011 :=
    @gJca (.classMem (.cv q) (synCpw1 (synChnord A))) (synWfn (synCpw1fn) (synC1c))
      (.classMem (.cv q) (synC1c)) p0006 p0010
  have p0012 := @gFvco2 (synC1c) (.cv q) (synCimage (synChnsicodemap A)) (synCpw1fn)
  have p0013 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (synWfn (synCpw1fn) (synC1c)) (.classMem (.cv q) (synC1c)))
      (.classEq (synCfv (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (.cv q))
        (synCfv (synCimage (synChnsicodemap A)) (synCfv (synCpw1fn) (.cv q))))
      p0011 p0012
  have p0014 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCfv (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (.cv q))
      (synCfv (synCimage (synChnsicodemap A)) (synCfv (synCpw1fn) (.cv q))) p0004
      p0013
  have p0015 := @gHnwpw1argcl (synChnord A) q
  have p0016 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0015
  have p0017 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synChnord A))) (.cv q)
      (synCsn (synCuni (.cv q))) (synCpw1fn) p0016
  have p0018 := @gVex q
  have p0019 := @gUniex (.cv q) p0018
  have p0020 := @gPw1fnval (synCuni (.cv q)) p0019
  have p0021 :=
    @gA1i
      (.classEq (synCfv (synCpw1fn) (synCsn (synCuni (.cv q))))
        (synCpw1 (synCuni (.cv q))))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0020
  have p0022 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChnord A))) (synCfv (synCpw1fn) (.cv q))
      (synCfv (synCpw1fn) (synCsn (synCuni (.cv q)))) (synCpw1 (synCuni (.cv q)))
      p0017 p0021
  have p0023 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synChnord A))) (synCfv (synCpw1fn) (.cv q))
      (synCpw1 (synCuni (.cv q))) (synCimage (synChnsicodemap A)) p0022
  have p0024 := @gHnsicodemapexgndv A
  have p0025 := Nominal.mp hyp_hnsiquomapvalndv_1 p0024
  have p0028 := @gPw1ex (synCuni (.cv q)) p0019
  have p0029 :=
    @gWppfvimage (synCpw1 (synCuni (.cv q))) (synChnsicodemap A) dv_cache_0001 p0025
      p0028
  have p0030 :=
    @gA1i
      (.classEq (synCfv (synCimage (synChnsicodemap A)) (synCpw1 (synCuni (.cv q))))
        (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0029
  have p0031 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synCfv (synCimage (synChnsicodemap A)) (synCfv (synCpw1fn) (.cv q)))
      (synCfv (synCimage (synChnsicodemap A)) (synCpw1 (synCuni (.cv q))))
      (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))) p0023 p0030
  have p0032 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCfv (synCimage (synChnsicodemap A)) (synCfv (synCpw1fn) (.cv q)))
      (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))) p0014 p0031
  exact p0032


end NFChoice.DirectNominalPrf.WPPReplay

end
