/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_f1oiso`. -/
@[expose]
noncomputable def gF1oiso (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) (B : Class)
    (R : Class) (S : Class) (H : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_H_w : w ∉ H.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_H_z : z ∉ H.fv)
    (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (synWf1o H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A
                  (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                      (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
        (synWiso H R S A B)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
                ({ w } : Finset Var) ∪
              A.fv ∪
            B.fv ∪
          R.fv ∪
        S.fv ∪
      H.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_B : v ∉ B.fv := by
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
  have fresh_v_not_H : v ∉ H.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_H : u ∉ H.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (synCfv H (.cv v)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, dv_x_z, fresh_x_ne_v, dv_H_x, or_false,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (synCfv H (.cv v)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, dv_y_z, fresh_y_ne_v, dv_H_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv w) (synCfv H (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_w_x), fresh_x_ne_u, dv_H_x, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv w) (synCfv H (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_w_y), fresh_y_ne_u, dv_H_y, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCfv H (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_v, dv_H_z, or_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((synCfv H (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_v, dv_H_w, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCfv H (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, dv_H_z, or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((synCfv H (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, dv_H_w, or_false, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((synWrex x A (synWrex y A (synWa
              (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
                (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))))
              (synWbr (.cv x) R (.cv y)))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_z, fresh_z_ne_v, dv_H_z,
          (Ne.symm dv_x_z), fresh_z_ne_u, (Ne.symm dv_y_z), dv_R_z, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    w ∉
      ((synWrex x A (synWrex y A (synWa
              (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
                (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))))
              (synWbr (.cv x) R (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_w, fresh_w_ne_v, dv_H_w, dv_w_x,
          fresh_w_ne_u, dv_w_y, dv_R_w, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show z ≠ w from (by exact Ne.symm dv_w_z))
  have dv_cache_0012 :
    y ∉
      ((synWa (synWa (synWf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, dv_B_y, dv_H_y, fresh_y_ne_v, (Ne.symm dv_x_y),
          or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classEq (.cv x) (.cv v))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ ((synWa (synWf1 H A B) (.classMem (.cv v) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, dv_B_x, dv_H_x, fresh_x_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Class.cv v)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0017 :
    x ∉
      ((synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
            (synWbr (.cv v) R (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_u, dv_H_x, dv_x_y,
          fresh_x_ne_v, dv_R_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((synWa (synWf1 H A B) (.classMem (.cv u) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, dv_B_y, dv_H_y, fresh_y_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0020 : y ∉ (A).fv :=
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
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((synWbr (.cv v) R (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_v, fresh_y_ne_u, dv_R_y, or_false,
          not_false_eq_true])
  have dv_cache_0022 : u ∉ (A).fv :=
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
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0023 :
    v ∉
      ((synWa (synWf1 H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                    (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                      (.classEq (.cv w) (synCfv H (.cv y))))
                    (synWbr (.cv x) R (.cv y))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_A, fresh_v_not_B,
          fresh_v_not_H, fresh_v_not_S, fresh_v_ne_z, fresh_v_ne_x, fresh_v_ne_w,
          fresh_v_ne_y, fresh_v_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0024 :
    u ∉
      ((synWa (synWf1 H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                    (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                      (.classEq (.cv w) (synCfv H (.cv y))))
                    (synWbr (.cv x) R (.cv y))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B,
          fresh_u_not_H, fresh_u_not_S, fresh_u_ne_z, fresh_u_ne_x, fresh_u_ne_w,
          fresh_u_ne_y, fresh_u_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0025 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0026 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0027 : v ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0028 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0029 : v ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_H, not_false_eq_true])
  have dv_cache_0030 : u ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_H, not_false_eq_true])
  have dv_cache_0031 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0032 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0033 : v ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_S, not_false_eq_true])
  have dv_cache_0034 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have p0000 :=
    @gSimpl (synWf1o H A B)
      (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
  have p0001 := @gF1of1 A B H
  have p0002 := (Nominal.biimpRefl (synWbr (synCfv H (.cv v)) S (synCfv H (.cv u))))
  have p0003 :=
    @gEleq2 S
      (synCopab z w (synWrex x A (synWrex y A (synWa
              (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))))
      (synCop (synCfv H (.cv v)) (synCfv H (.cv u)))
  have p0004 := @gFvex (.cv v) H
  have p0005 := @gFvex (.cv u) H
  have p0006 := @gEqeq1 (.cv z) (synCfv H (.cv v)) (synCfv H (.cv x))
  have p0007 :=
    @gAnbi1d (.classEq (.cv z) (synCfv H (.cv v)))
      (.classEq (.cv z) (synCfv H (.cv x)))
      (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
      (.classEq (.cv w) (synCfv H (.cv y))) p0006
  have p0008 :=
    @gAnbi1d (.classEq (.cv z) (synCfv H (.cv v)))
      (synWa (.classEq (.cv z) (synCfv H (.cv x))) (.classEq (.cv w) (synCfv H (.cv y))))
      (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
        (.classEq (.cv w) (synCfv H (.cv y))))
      (synWbr (.cv x) R (.cv y)) p0007
  have p0009 :=
    @gN2rexbidv (.classEq (.cv z) (synCfv H (.cv v)))
      (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
          (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
          (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      x y A A dv_cache_0001 dv_cache_0002 p0008
  have p0010 := @gEqeq1 (.cv w) (synCfv H (.cv u)) (synCfv H (.cv y))
  have p0011 :=
    @gAnbi2d (.classEq (.cv w) (synCfv H (.cv u)))
      (.classEq (.cv w) (synCfv H (.cv y)))
      (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
      (.classEq (synCfv H (.cv v)) (synCfv H (.cv x))) p0010
  have p0012 :=
    @gAnbi1d (.classEq (.cv w) (synCfv H (.cv u)))
      (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
        (.classEq (.cv w) (synCfv H (.cv y))))
      (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
        (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))))
      (synWbr (.cv x) R (.cv y)) p0011
  have p0013 :=
    @gN2rexbidv (.classEq (.cv w) (synCfv H (.cv u)))
      (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
          (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
          (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      x y A A dv_cache_0003 dv_cache_0004 p0012
  have p0014 :=
    @gOpelopab
      (synWrex x A (synWrex y A (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
              (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWrex x A (synWrex y A (synWa
            (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
              (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWrex x A (synWrex y A (synWa
            (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
              (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      z w (synCfv H (.cv v)) (synCfv H (.cv u)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0004 p0005
      p0009 p0013
  have p0015 :=
    @gAnass (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
      (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y))
  have p0016 := @gF1fveq A B (.cv v) (.cv x) H
  have p0017 := @gEqcom (.cv v) (.cv x)
  have p0018 :=
    @gSyl6bb
      (synWa (synWf1 H A B) (synWa (.classMem (.cv v) A) (.classMem (.cv x) A)))
      (.classEq (synCfv H (.cv v)) (synCfv H (.cv x))) (.classEq (.cv v) (.cv x))
      (.classEq (.cv x) (.cv v)) p0016 p0017
  have p0019 :=
    @gAnassrs (synWf1 H A B) (.classMem (.cv v) A) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv H (.cv v)) (synCfv H (.cv x))) (.classEq (.cv x) (.cv v)))
      p0018
  have p0020 :=
    @gAnbi1d
      (synWa (synWa (synWf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (.classEq (synCfv H (.cv v)) (synCfv H (.cv x))) (.classEq (.cv x) (.cv v))
      (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y)))
      p0019
  have p0021 :=
    @gSyl5bb
      (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
          (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
        (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y))))
      (synWa (synWa (synWf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (synWa (.classEq (.cv x) (.cv v))
        (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y))))
      p0015 p0020
  have p0022 :=
    @gRexbidv
      (synWa (synWa (synWf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
          (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (.cv x) (.cv v))
        (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y))))
      y A dv_cache_0012 p0021
  have p0023 :=
    @gR1942v (.classEq (.cv x) (.cv v))
      (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y)))
      y A dv_cache_0013
  have p0024 :=
    @gSyl6bb
      (synWa (synWa (synWf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (synWrex y A (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
            (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))
      (synWrex y A (synWa (.classEq (.cv x) (.cv v))
          (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      (synWa (.classEq (.cv x) (.cv v)) (synWrex y A
          (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      p0022 p0023
  have p0025 :=
    @gRexbidva (synWa (synWf1 H A B) (.classMem (.cv v) A))
      (synWrex y A (synWa (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
            (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))
      (synWa (.classEq (.cv x) (.cv v)) (synWrex y A
          (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      x A dv_cache_0014 p0024
  have p0026 := @gBreq1 (.cv x) (.cv v) (.cv y) R
  have p0027 :=
    @gAnbi2d (.classEq (.cv x) (.cv v)) (synWbr (.cv x) R (.cv y))
      (synWbr (.cv v) R (.cv y)) (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) p0026
  have p0028 :=
    @gRexbidv (.classEq (.cv x) (.cv v))
      (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv v) R (.cv y)))
      y A dv_cache_0013 p0027
  have p0029 :=
    @gCeqsrexv
      (synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
          (synWbr (.cv x) R (.cv y))))
      (synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
          (synWbr (.cv v) R (.cv y))))
      x (.cv v) A dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @gAdantl (.classMem (.cv v) A)
      (synWb (synWrex x A (synWa (.classEq (.cv x) (.cv v)) (synWrex y A
              (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
                (synWbr (.cv x) R (.cv y)))))) (synWrex y A
          (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
            (synWbr (.cv v) R (.cv y)))))
      (synWf1 H A B) p0029
  have p0031 :=
    @gBitrd (synWa (synWf1 H A B) (.classMem (.cv v) A))
      (synWrex x A (synWrex y A (synWa
            (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
              (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWrex x A (synWa (.classEq (.cv x) (.cv v)) (synWrex y A
            (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
              (synWbr (.cv x) R (.cv y))))))
      (synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
          (synWbr (.cv v) R (.cv y))))
      p0025 p0030
  have p0032 := @gF1fveq A B (.cv u) (.cv y) H
  have p0033 := @gEqcom (.cv u) (.cv y)
  have p0034 :=
    @gSyl6bb
      (synWa (synWf1 H A B) (synWa (.classMem (.cv u) A) (.classMem (.cv y) A)))
      (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (.classEq (.cv u) (.cv y))
      (.classEq (.cv y) (.cv u)) p0032 p0033
  have p0035 :=
    @gAnassrs (synWf1 H A B) (.classMem (.cv u) A) (.classMem (.cv y) A)
      (synWb (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (.classEq (.cv y) (.cv u)))
      p0034
  have p0036 :=
    @gAnbi1d
      (synWa (synWa (synWf1 H A B) (.classMem (.cv u) A)) (.classMem (.cv y) A))
      (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (.classEq (.cv y) (.cv u))
      (synWbr (.cv v) R (.cv y)) p0035
  have p0037 :=
    @gRexbidva (synWa (synWf1 H A B) (.classMem (.cv u) A))
      (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))) (synWbr (.cv v) R (.cv y)))
      (synWa (.classEq (.cv y) (.cv u)) (synWbr (.cv v) R (.cv y))) y A dv_cache_0018
      p0036
  have p0038 := @gBreq2 (.cv y) (.cv u) (.cv v) R
  have p0039 :=
    @gCeqsrexv (synWbr (.cv v) R (.cv y)) (synWbr (.cv v) R (.cv u)) y (.cv u) A
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0038
  have p0040 :=
    @gAdantl (.classMem (.cv u) A)
      (synWb (synWrex y A (synWa (.classEq (.cv y) (.cv u)) (synWbr (.cv v) R (.cv y))))
        (synWbr (.cv v) R (.cv u)))
      (synWf1 H A B) p0039
  have p0041 :=
    @gBitrd (synWa (synWf1 H A B) (.classMem (.cv u) A))
      (synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
          (synWbr (.cv v) R (.cv y))))
      (synWrex y A (synWa (.classEq (.cv y) (.cv u)) (synWbr (.cv v) R (.cv y))))
      (synWbr (.cv v) R (.cv u)) p0037 p0040
  have p0042 :=
    @gSylan9bb (synWa (synWf1 H A B) (.classMem (.cv v) A))
      (synWrex x A (synWrex y A (synWa
            (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
              (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWrex y A (synWa (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))
          (synWbr (.cv v) R (.cv y))))
      (synWa (synWf1 H A B) (.classMem (.cv u) A)) (synWbr (.cv v) R (.cv u)) p0031
      p0041
  have p0043 :=
    @gAnandis (synWf1 H A B) (.classMem (.cv v) A) (.classMem (.cv u) A)
      (synWb (synWrex x A (synWrex y A (synWa
              (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
                (.classEq (synCfv H (.cv u)) (synCfv H (.cv y))))
              (synWbr (.cv x) R (.cv y))))) (synWbr (.cv v) R (.cv u)))
      p0042
  have p0044 :=
    @gSyl5bb
      (.classMem (synCop (synCfv H (.cv v)) (synCfv H (.cv u))) (synCopab z w (synWrex x A
            (synWrex y A (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (synWrex x A (synWrex y A (synWa
            (synWa (.classEq (synCfv H (.cv v)) (synCfv H (.cv x)))
              (.classEq (synCfv H (.cv u)) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWa (synWf1 H A B) (synWa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (synWbr (.cv v) R (.cv u)) p0014 p0043
  have p0045 :=
    @gSylan9bbr
      (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (.classMem (synCop (synCfv H (.cv v)) (synCfv H (.cv u))) S)
      (.classMem (synCop (synCfv H (.cv v)) (synCfv H (.cv u))) (synCopab z w (synWrex x A
            (synWrex y A (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (synWa (synWf1 H A B) (synWa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (synWbr (.cv v) R (.cv u)) p0003 p0044
  have p0046 :=
    @gAn32s (synWf1 H A B) (synWa (.classMem (.cv v) A) (.classMem (.cv u) A))
      (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (synWb (.classMem (synCop (synCfv H (.cv v)) (synCfv H (.cv u))) S)
        (synWbr (.cv v) R (.cv u)))
      p0045
  have p0047 :=
    @gSyl5rbb (synWbr (synCfv H (.cv v)) S (synCfv H (.cv u)))
      (.classMem (synCop (synCfv H (.cv v)) (synCfv H (.cv u))) S)
      (synWa (synWa (synWf1 H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A
                  (synWa (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                      (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
        (synWa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (synWbr (.cv v) R (.cv u)) p0002 p0046
  have p0048 :=
    @gRalrimivva
      (synWa (synWf1 H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                  (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                    (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWb (synWbr (.cv v) R (.cv u)) (synWbr (synCfv H (.cv v)) S (synCfv H (.cv u))))
      v u A A dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0047
  have p0049 :=
    @gSylan (synWf1o H A B) (synWf1 H A B)
      (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                  (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (synWral v A (synWral u A (synWb (synWbr (.cv v) R (.cv u))
            (synWbr (synCfv H (.cv v)) S (synCfv H (.cv u))))))
      p0001 p0048
  have p0050 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso v u A B R S H
      dv_cache_0026 dv_cache_0022 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0025
  have p0051 :=
    @gSylanbrc
      (synWa (synWf1o H A B) (.classEq S (synCopab z w (synWrex x A (synWrex y A (synWa
                  (synWa (.classEq (.cv z) (synCfv H (.cv x)))
                    (.classEq (.cv w) (synCfv H (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWf1o H A B)
      (synWral v A (synWral u A (synWb (synWbr (.cv v) R (.cv u))
            (synWbr (synCfv H (.cv v)) S (synCfv H (.cv u))))))
      (synWiso H R S A B) p0000 p0049 p0050
  exact p0051


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_f1oiso2`. -/
@[expose]
noncomputable def gF1oiso2 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_f1oiso2_1 : Nominal.NPrf (.classEq S (synCopab x y
            (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
              (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))))) :
    Nominal.NPrf (.imp (synWf1o H A B) (synWiso H R S A B)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((synCfv (synCcnv H) (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0003 :
    w ∉
      ((synWa (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
            (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, fresh_w_ne_y, fresh_w_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Wff.classEq (.cv z) (synCfv (synCcnv H) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_not_H, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCfv (synCcnv H) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_H, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 :
    z ∉
      ((synWrex w A (synWa
            (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
              (.classEq (.cv y) (synCfv H (.cv w))))
            (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x,
          fresh_z_not_H, fresh_z_ne_y, fresh_z_ne_w, fresh_z_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_ne_y, fresh_z_not_H,
          fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0009 :
    w ∉
      ((synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_B, fresh_w_ne_y, fresh_w_not_H,
          fresh_w_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((synWf1o H A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, fresh_z_not_H, or_false,
          not_false_eq_true])
  have dv_cache_0011 : w ∉ ((synWf1o H A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, fresh_w_not_A, fresh_w_not_B, fresh_w_not_H, or_false,
          not_false_eq_true])
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0013 : x ∉ ((synWf1o H A B)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, dv_A_x, dv_B_x, dv_H_x, or_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((synWf1o H A B)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, dv_A_y, dv_B_y, dv_H_y, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0017 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0018 : w ∉ (B).fv :=
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
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0019 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_H_y, not_false_eq_true])
  have dv_cache_0020 : z ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_H, not_false_eq_true])
  have dv_cache_0021 : w ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_H, not_false_eq_true])
  have dv_cache_0022 : x ∉ (H).fv :=
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
        simp only [dv_H_x, not_false_eq_true])
  have dv_cache_0023 : y ∉ (R).fv :=
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
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0024 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0025 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0026 : x ∉ (R).fv :=
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
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0027 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0028 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0029 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0030 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0031 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have p0000 := @gF1ocnvdm A B (.cv x) H
  have p0001 :=
    @gAdantrr (synWf1o H A B) (.classMem (.cv x) B)
      (.classMem (synCfv (synCcnv H) (.cv x)) A) (.classMem (.cv y) B) p0000
  have p0002 :=
    @gN3adant3 (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (synCfv (synCcnv H) (.cv x)) A)
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))) p0001
  have p0003 := @gF1ocnvdm A B (.cv y) H
  have p0004 :=
    @gAdantrl (synWf1o H A B) (.classMem (.cv y) B)
      (.classMem (synCfv (synCcnv H) (.cv y)) A) (.classMem (.cv x) B) p0003
  have p0005 :=
    @gN3adant3 (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (synCfv (synCcnv H) (.cv y)) A)
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))) p0004
  have p0006 := @gF1ocnvfv2 A B (.cv x) H
  have p0007 :=
    @gEqcomd (synWa (synWf1o H A B) (.classMem (.cv x) B))
      (synCfv H (synCfv (synCcnv H) (.cv x))) (.cv x) p0006
  have p0008 := @gF1ocnvfv2 A B (.cv y) H
  have p0009 :=
    @gEqcomd (synWa (synWf1o H A B) (.classMem (.cv y) B))
      (synCfv H (synCfv (synCcnv H) (.cv y))) (.cv y) p0008
  have p0010 :=
    @gAnim12dan (synWf1o H A B) (.classMem (.cv x) B)
      (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x)))) (.classMem (.cv y) B)
      (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))) p0007 p0009
  have p0011 :=
    @gN3adant3 (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
        (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))) p0010
  have p0012 :=
    @gSimp3 (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y)))
  have p0013 := @gFveq2 (.cv w) (synCfv (synCcnv H) (.cv y)) H
  have p0014 :=
    @gEqeq2d (.classEq (.cv w) (synCfv (synCcnv H) (.cv y))) (synCfv H (.cv w))
      (synCfv H (synCfv (synCcnv H) (.cv y))) (.cv y) p0013
  have p0015 :=
    @gAnbi2d (.classEq (.cv w) (synCfv (synCcnv H) (.cv y)))
      (.classEq (.cv y) (synCfv H (.cv w)))
      (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y))))
      (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x)))) p0014
  have p0016 :=
    @gBreq2 (.cv w) (synCfv (synCcnv H) (.cv y)) (synCfv (synCcnv H) (.cv x)) R
  have p0017 :=
    @gAnbi12d (.classEq (.cv w) (synCfv (synCcnv H) (.cv y)))
      (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
        (.classEq (.cv y) (synCfv H (.cv w))))
      (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
        (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))) p0015
      p0016
  have p0018 :=
    @gRspcev
      (synWa (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
          (.classEq (.cv y) (synCfv H (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w)))
      (synWa (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
          (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      w (synCfv (synCcnv H) (.cv y)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @gSyl12anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      (.classMem (synCfv (synCcnv H) (.cv y)) A)
      (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
        (.classEq (.cv y) (synCfv H (synCfv (synCcnv H) (.cv y)))))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y)))
      (synWrex w A (synWa
          (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
            (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w))))
      p0005 p0011 p0012 p0018
  have p0020 := @gFveq2 (.cv z) (synCfv (synCcnv H) (.cv x)) H
  have p0021 :=
    @gEqeq2d (.classEq (.cv z) (synCfv (synCcnv H) (.cv x))) (synCfv H (.cv z))
      (synCfv H (synCfv (synCcnv H) (.cv x))) (.cv x) p0020
  have p0022 :=
    @gAnbi1d (.classEq (.cv z) (synCfv (synCcnv H) (.cv x)))
      (.classEq (.cv x) (synCfv H (.cv z)))
      (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
      (.classEq (.cv y) (synCfv H (.cv w))) p0021
  have p0023 := @gBreq1 (.cv z) (synCfv (synCcnv H) (.cv x)) (.cv w) R
  have p0024 :=
    @gAnbi12d (.classEq (.cv z) (synCfv (synCcnv H) (.cv x)))
      (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
      (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
        (.classEq (.cv y) (synCfv H (.cv w))))
      (synWbr (.cv z) R (.cv w)) (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w)) p0022
      p0023
  have p0025 :=
    @gRexbidv (.classEq (.cv z) (synCfv (synCcnv H) (.cv x)))
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
      (synWa (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
          (.classEq (.cv y) (synCfv H (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w)))
      w A dv_cache_0004 p0024
  have p0026 :=
    @gRspcev
      (synWrex w A (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
            (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w))))
      (synWrex w A (synWa
          (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
            (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w))))
      z (synCfv (synCcnv H) (.cv x)) A dv_cache_0005 dv_cache_0006 dv_cache_0007 p0025
  have p0027 :=
    @gSyl2anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      (.classMem (synCfv (synCcnv H) (.cv x)) A)
      (synWrex w A (synWa
          (synWa (.classEq (.cv x) (synCfv H (synCfv (synCcnv H) (.cv x))))
            (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (.cv w))))
      (synWrex z A (synWrex w A (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
              (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))))
      p0002 p0019 p0026
  have p0028 :=
    @gN3expib (synWf1o H A B) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y)))
      (synWrex z A (synWrex w A (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
              (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))))
      p0027
  have p0029 :=
    @gSimp3ll (.classEq (.cv x) (synCfv H (.cv z)))
      (.classEq (.cv y) (synCfv H (.cv w))) (synWbr (.cv z) R (.cv w)) (synWf1o H A B)
      (synWa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0030 :=
    @gSimp1 (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
  have p0031 :=
    @gSimp2l (synWf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A)
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
  have p0032 := @gF1of A B H
  have p0033 := @gFfvelrn A B (.cv z) H
  have p0034 :=
    @gSylan (synWf1o H A B) (synWf H A B) (.classMem (.cv z) A)
      (.classMem (synCfv H (.cv z)) B) p0032 p0033
  have p0035 :=
    @gSyl2anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (synWf1o H A B) (.classMem (.cv z) A) (.classMem (synCfv H (.cv z)) B) p0030 p0031
      p0034
  have p0036 :=
    @gEqeltrd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.cv x) (synCfv H (.cv z)) B p0029 p0035
  have p0037 :=
    @gSimp3lr (.classEq (.cv x) (synCfv H (.cv z)))
      (.classEq (.cv y) (synCfv H (.cv w))) (synWbr (.cv z) R (.cv w)) (synWf1o H A B)
      (synWa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0038 :=
    @gSimp2r (synWf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A)
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
  have p0039 := @gFfvelrn A B (.cv w) H
  have p0040 :=
    @gSylan (synWf1o H A B) (synWf H A B) (.classMem (.cv w) A)
      (.classMem (synCfv H (.cv w)) B) p0032 p0039
  have p0041 :=
    @gSyl2anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (synWf1o H A B) (.classMem (.cv w) A) (.classMem (synCfv H (.cv w)) B) p0030 p0038
      p0040
  have p0042 :=
    @gEqeltrd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.cv y) (synCfv H (.cv w)) B p0037 p0041
  have p0043 :=
    @gSimp3r (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
      (synWbr (.cv z) R (.cv w))
  have p0044 :=
    @gEqcomd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.cv x) (synCfv H (.cv z)) p0029
  have p0045 := @gF1ocnvfv A B (.cv z) (.cv x) H
  have p0046 :=
    @gSyl2anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (synWf1o H A B) (.classMem (.cv z) A)
      (.imp (.classEq (synCfv H (.cv z)) (.cv x))
        (.classEq (synCfv (synCcnv H) (.cv x)) (.cv z)))
      p0030 p0031 p0045
  have p0047 :=
    @gMpd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.classEq (synCfv H (.cv z)) (.cv x))
      (.classEq (synCfv (synCcnv H) (.cv x)) (.cv z)) p0044 p0046
  have p0048 :=
    @gEqcomd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.cv y) (synCfv H (.cv w)) p0037
  have p0049 := @gF1ocnvfv A B (.cv w) (.cv y) H
  have p0050 :=
    @gSyl2anc
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (synWf1o H A B) (.classMem (.cv w) A)
      (.imp (.classEq (synCfv H (.cv w)) (.cv y))
        (.classEq (synCfv (synCcnv H) (.cv y)) (.cv w)))
      p0030 p0038 p0049
  have p0051 :=
    @gMpd
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.classEq (synCfv H (.cv w)) (.cv y))
      (.classEq (synCfv (synCcnv H) (.cv y)) (.cv w)) p0048 p0050
  have p0052 :=
    @gN3brtr4d
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.cv z) (.cv w) (synCfv (synCcnv H) (.cv x)) (synCfv (synCcnv H) (.cv y)) R
      p0043 p0047 p0051
  have p0053 :=
    @gJca31
      (synW3a (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A)) (synWa
          (synWa (.classEq (.cv x) (synCfv H (.cv z))) (.classEq (.cv y) (synCfv H (.cv w))))
          (synWbr (.cv z) R (.cv w))))
      (.classMem (.cv x) B) (.classMem (.cv y) B)
      (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))) p0036
      p0042 p0052
  have p0054 :=
    @gN3exp (synWf1o H A B) (synWa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      p0053
  have p0055 :=
    @gRexlimdvv (synWf1o H A B)
      (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
          (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      z w A A dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0054
  have p0056 :=
    @gImpbid (synWf1o H A B)
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      (synWrex z A (synWrex w A (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
              (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))))
      p0028 p0055
  have p0057 :=
    @gOpabbidv (synWf1o H A B)
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y))))
      (synWrex z A (synWrex w A (synWa (synWa (.classEq (.cv x) (synCfv H (.cv z)))
              (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))))
      x y dv_cache_0013 dv_cache_0014 p0056
  have p0058 :=
    @gSyl5eq (synWf1o H A B) S
      (synCopab x y (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (synWbr (synCfv (synCcnv H) (.cv x)) R (synCfv (synCcnv H) (.cv y)))))
      (synCopab x y (synWrex z A (synWrex w A (synWa
              (synWa (.classEq (.cv x) (synCfv H (.cv z)))
                (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w))))))
      hyp_f1oiso2_1 p0057
  have p0059 :=
    @gF1oiso z w x y A B R S H dv_cache_0015 dv_cache_0006 dv_cache_0002 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
      dv_cache_0029 dv_cache_0012 dv_cache_0030 dv_cache_0031
  have p0060 :=
    @gMpdan (synWf1o H A B)
      (.classEq S (synCopab x y (synWrex z A (synWrex w A (synWa
                (synWa (.classEq (.cv x) (synCfv H (.cv z)))
                  (.classEq (.cv y) (synCfv H (.cv w)))) (synWbr (.cv z) R (.cv w)))))))
      (synWiso H R S A B) p0058 p0059
  exact p0060

/-- Checked nominal proof certificate identified upstream as `g_opbr1st`. -/
@[expose]
noncomputable def gOpbr1st (A : Class) (B : Class) (C : Class)
    (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr (synCop A B) (synC1st) C) (.classEq A C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((synCop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synWbr (synCop A B) (synC1st) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true])
  have p0000 := @gBrex (synCop A B) C (synC1st)
  have p0001 :=
    @gSimprd (synWbr (synCop A B) (synC1st) C) (.classMem (synCop A B) (synCvv))
      (.classMem C (synCvv)) p0000
  have p0002 := @gEleq1 A C (synCvv)
  have p0003 :=
    @gMpbii (.classEq A C) (.classMem A (synCvv)) (.classMem C (synCvv)) hyp_opbr1st_1
      p0002
  have p0004 := @gBreq2 (.cv x) C (synCop A B) (synC1st)
  have p0005 := @gEqeq2 (.cv x) C A
  have p0006 := @gVex x
  have p0007 := @gBr1st y (synCop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @gBiidd (.classEq (.cv y) B) (.classEq (.cv x) A)
  have p0009 :=
    @gCeqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) y B dv_cache_0003 dv_cache_0004
      hyp_opbr1st_2 p0008
  have p0010 := @gEqcom (synCop A B) (synCop (.cv x) (.cv y))
  have p0011 := @gOpth (.cv x) (.cv y) A B
  have p0012 := @gAncom (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0013 :=
    @gBitri (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0011 p0012
  have p0014 :=
    @gBitri (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0010 p0013
  have p0015 :=
    @gExbii (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (synWa (.classEq (.cv y) B) (.classEq (.cv x) A)) y p0014
  have p0016 := @gEqcom A (.cv x)
  have p0017 :=
    @gN3bitr4i (synWex y (synWa (.classEq (.cv y) B) (.classEq (.cv x) A)))
      (.classEq (.cv x) A) (synWex y (.classEq (synCop A B) (synCop (.cv x) (.cv y))))
      (.classEq A (.cv x)) p0009 p0015 p0016
  have p0018 :=
    @gBitri (synWbr (synCop A B) (synC1st) (.cv x))
      (synWex y (.classEq (synCop A B) (synCop (.cv x) (.cv y)))) (.classEq A (.cv x))
      p0007 p0017
  have p0019 :=
    @gVtoclbg (synWbr (synCop A B) (synC1st) (.cv x)) (.classEq A (.cv x))
      (synWbr (synCop A B) (synC1st) C) (.classEq A C) x C (synCvv) dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0004 p0005 p0018
  have p0020 :=
    @gPm521nii (synWbr (synCop A B) (synC1st) C) (.classMem C (synCvv))
      (.classEq A C) p0001 p0003 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_opbr2nd`. -/
@[expose]
noncomputable def gOpbr2nd (A : Class) (B : Class) (C : Class)
    (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr (synCop A B) (synC2nd) C) (.classEq B C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((synCop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
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
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synWbr (synCop A B) (synC2nd) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have p0000 := @gBrex (synCop A B) C (synC2nd)
  have p0001 :=
    @gSimprd (synWbr (synCop A B) (synC2nd) C) (.classMem (synCop A B) (synCvv))
      (.classMem C (synCvv)) p0000
  have p0002 := @gEleq1 B C (synCvv)
  have p0003 :=
    @gMpbii (.classEq B C) (.classMem B (synCvv)) (.classMem C (synCvv)) hyp_opbr1st_2
      p0002
  have p0004 := @gBreq2 (.cv x) C (synCop A B) (synC2nd)
  have p0005 := @gEqeq2 (.cv x) C B
  have p0006 := @gVex x
  have p0007 := @gBr2nd y (synCop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @gBiidd (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0009 :=
    @gCeqsexv (.classEq (.cv x) B) (.classEq (.cv x) B) y A dv_cache_0003 dv_cache_0004
      hyp_opbr1st_1 p0008
  have p0010 := @gEqcom (synCop A B) (synCop (.cv y) (.cv x))
  have p0011 := @gOpth (.cv y) (.cv x) A B
  have p0012 :=
    @gBitri (.classEq (synCop A B) (synCop (.cv y) (.cv x)))
      (.classEq (synCop (.cv y) (.cv x)) (synCop A B))
      (synWa (.classEq (.cv y) A) (.classEq (.cv x) B)) p0010 p0011
  have p0013 :=
    @gExbii (.classEq (synCop A B) (synCop (.cv y) (.cv x)))
      (synWa (.classEq (.cv y) A) (.classEq (.cv x) B)) y p0012
  have p0014 := @gEqcom B (.cv x)
  have p0015 :=
    @gN3bitr4i (synWex y (synWa (.classEq (.cv y) A) (.classEq (.cv x) B)))
      (.classEq (.cv x) B) (synWex y (.classEq (synCop A B) (synCop (.cv y) (.cv x))))
      (.classEq B (.cv x)) p0009 p0013 p0014
  have p0016 :=
    @gBitri (synWbr (synCop A B) (synC2nd) (.cv x))
      (synWex y (.classEq (synCop A B) (synCop (.cv y) (.cv x)))) (.classEq B (.cv x))
      p0007 p0015
  have p0017 :=
    @gVtoclbg (synWbr (synCop A B) (synC2nd) (.cv x)) (.classEq B (.cv x))
      (synWbr (synCop A B) (synC2nd) C) (.classEq B C) x C (synCvv) dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0004 p0005 p0016
  have p0018 :=
    @gPm521nii (synWbr (synCop A B) (synC2nd) C) (.classMem C (synCvv))
      (.classEq B C) p0001 p0003 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfid4`. -/
@[expose]
noncomputable def gDfid4 :
    Nominal.NPrf (.classEq (synCid) (synCin (synCsset) (synCcnv (synCsset)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((synCid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCid)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCin (synCsset) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCin (synCsset) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gEqss (.cv x) (.cv y)
  have p0001 := @gVex y
  have p0002 := @gIdeq (.cv x) (.cv y) p0001
  have p0003 := @gBrin (.cv x) (.cv y) (synCsset) (synCcnv (synCsset))
  have p0004 := @gVex x
  have p0005 := @gBrsset (.cv x) (.cv y) p0004 p0001
  have p0006 := @gBrcnv (.cv x) (.cv y) (synCsset)
  have p0007 := @gBrsset (.cv y) (.cv x) p0001 p0004
  have p0008 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCsset)) (.cv y))
      (synWbr (.cv y) (synCsset) (.cv x)) (synWss (.cv y) (.cv x)) p0006 p0007
  have p0009 :=
    @gAnbi12i (synWbr (.cv x) (synCsset) (.cv y)) (synWss (.cv x) (.cv y))
      (synWbr (.cv x) (synCcnv (synCsset)) (.cv y)) (synWss (.cv y) (.cv x)) p0005
      p0008
  have p0010 :=
    @gBitri (synWbr (.cv x) (synCin (synCsset) (synCcnv (synCsset))) (.cv y))
      (synWa (synWbr (.cv x) (synCsset) (.cv y))
        (synWbr (.cv x) (synCcnv (synCsset)) (.cv y)))
      (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x))) p0003 p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (.objEq x y) (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWss synCin synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0000
  have p0011_e01_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0011 :=
    @gN3bitr4i (.objEq x y) (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x)))
      (synWbr (.cv x) (synCid) (.cv y))
      (synWbr (.cv x) (synCin (synCsset) (synCcnv (synCsset))) (.cv y))
      p0011_e00_recanon p0011_e01_recanon p0010
  have p0012 :=
    @gEqbrriv x y (synCid) (synCin (synCsset) (synCcnv (synCsset))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_idex`. -/
@[expose]
noncomputable def gIdex : Nominal.NPrf (.classMem (synCid) (synCvv)) :=
  by
  have p0000 := @gDfid4
  have p0001 := @gSsetex
  have p0003 := @gCnvex (synCsset) p0001
  have p0004 := @gInex (synCsset) (synCcnv (synCsset)) p0001 p0003
  have p0005 :=
    @gEqeltri (synCid) (synCin (synCsset) (synCcnv (synCsset))) (synCvv) p0000
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_n_1stfo`. -/
@[expose]
noncomputable def gN1stfo : Nominal.NPrf (synWfo (synC1st) (synCvv) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have dv_cache_0001 : x ∉ ((synC1st)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv y)).fv :=
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
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_z, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((Wff.classEq (.cv x) (synCop (.cv y) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Wff.classEq (.cv x) (synCop (.cv z) (.cv t)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_ne_t, or_false,
          not_false_eq_true])
  have dv_cache_0013 : w ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCdm (synC1st))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((synCrn (synC1st))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z (synC1st) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gVex y
  have p0002 := @gBr1st w (.cv x) (.cv y) dv_cache_0007 dv_cache_0008 p0001
  have p0003 := @gVex z
  have p0004 := @gBr1st t (.cv x) (.cv z) dv_cache_0009 dv_cache_0010 p0003
  have p0005 :=
    @gAnbi12i (synWbr (.cv x) (synC1st) (.cv y))
      (synWex w (.classEq (.cv x) (synCop (.cv y) (.cv w))))
      (synWbr (.cv x) (synC1st) (.cv z))
      (synWex t (.classEq (.cv x) (synCop (.cv z) (.cv t)))) p0002 p0004
  have p0006 :=
    @gEeanv (.classEq (.cv x) (synCop (.cv y) (.cv w)))
      (.classEq (.cv x) (synCop (.cv z) (.cv t))) w t dv_cache_0011 dv_cache_0012
  have p0007 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synC1st) (.cv y)) (synWbr (.cv x) (synC1st) (.cv z)))
      (synWa (synWex w (.classEq (.cv x) (synCop (.cv y) (.cv w))))
        (synWex t (.classEq (.cv x) (synCop (.cv z) (.cv t)))))
      (synWex w (synWex t (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv z) (.cv t))))))
      p0005 p0006
  have p0008 := @gEqtr2 (.cv x) (synCop (.cv y) (.cv w)) (synCop (.cv z) (.cv t))
  have p0009 := @gOpth (.cv y) (.cv w) (.cv z) (.cv t)
  have p0010_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv z) (.cv t)))
        (synWa (.objEq y z) (.objEq w t))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gSimplbi (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv z) (.cv t))) (.objEq y z)
      (.objEq w t) p0010_e00_recanon
  have p0011 :=
    @gSyl
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv z) (.cv t))))
      (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv z) (.cv t))) (.objEq y z) p0008
      p0010
  have p0012 :=
    @gExlimivv
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv z) (.cv t))))
      (.objEq y z) w t dv_cache_0013 dv_cache_0014 p0011
  have p0013 :=
    @gSylbi
      (synWa (synWbr (.cv x) (synC1st) (.cv y)) (synWbr (.cv x) (synC1st) (.cv z)))
      (synWex w (synWex t (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv z) (.cv t))))))
      (.objEq y z) p0007 p0012
  have p0014 :=
    @gGen2
      (.imp (synWa (synWbr (.cv x) (synC1st) (.cv y)) (synWbr (.cv x) (synC1st) (.cv z)))
        (.objEq y z))
      y z p0013
  have p0015 :=
    @gMpgbir (synWfun (synC1st))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) (synC1st) (.cv y))
              (synWbr (.cv x) (synC1st) (.cv z))) (.objEq y z))))
      x p0000 p0014
  have p0016 := @gEqv x (synCdm (synC1st)) dv_cache_0015
  have p0017 := @gOpeq (.cv x)
  have p0018 := @gEqid (synCproj1 (.cv x))
  have p0019 := @gVex x
  have p0020 := @gProj1ex (.cv x) p0019
  have p0021 := @gProj2ex (.cv x) p0019
  have p0022 :=
    @gOpbr1st (synCproj1 (.cv x)) (synCproj2 (.cv x)) (synCproj1 (.cv x)) p0020 p0021
  have p0023 :=
    @gMpbir
      (synWbr (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synC1st)
        (synCproj1 (.cv x)))
      (.classEq (synCproj1 (.cv x)) (synCproj1 (.cv x))) p0018 p0022
  have p0024 :=
    @gBreldm (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synCproj1 (.cv x))
      (synC1st)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gEqeltri (.cv x) (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCdm (synC1st)) p0017 p0025
  have p0027 :=
    @gMpgbir (.classEq (synCdm (synC1st)) (synCvv))
      (.classMem (.cv x) (synCdm (synC1st))) x p0016 p0026
  have p0028 := (Nominal.biimpRefl (synWfn (synC1st) (synCvv)))
  have p0029 :=
    @gMpbir2an (synWfn (synC1st) (synCvv)) (synWfun (synC1st))
      (.classEq (synCdm (synC1st)) (synCvv)) p0015 p0027 p0028
  have p0030 := @gEqv x (synCrn (synC1st)) dv_cache_0016
  have p0031 := @gEqid (.cv x)
  have p0032 := @gOpbr1st (.cv x) (.cv x) (.cv x) p0019 p0019
  have p0033_e00_recanon : Nominal.NPrf (.objEq x x) :=
    Nominal.RecanonTransportDev.transport
      (by exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _) p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv x)) (synC1st) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @gMpbir (synWbr (synCop (.cv x) (.cv x)) (synC1st) (.cv x)) (.objEq x x)
      p0033_e00_recanon p0033_e01_recanon
  have p0034 := @gBrelrn (synCop (.cv x) (.cv x)) (.cv x) (synC1st)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gMpgbir (.classEq (synCrn (synC1st)) (synCvv))
      (.classMem (.cv x) (synCrn (synC1st))) x p0030 p0035
  have p0037 := (Nominal.biimpRefl (synWfo (synC1st) (synCvv) (synCvv)))
  have p0038 :=
    @gMpbir2an (synWfo (synC1st) (synCvv) (synCvv)) (synWfn (synC1st) (synCvv))
      (.classEq (synCrn (synC1st)) (synCvv)) p0029 p0036 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_n_2ndfo`. -/
@[expose]
noncomputable def gN2ndfo : Nominal.NPrf (synWfo (synC2nd) (synCvv) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have dv_cache_0001 : x ∉ ((synC2nd)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv y)).fv :=
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
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_z, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((Wff.classEq (.cv x) (synCop (.cv w) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_w, fresh_t_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Wff.classEq (.cv x) (synCop (.cv t) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_t, fresh_w_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0013 : w ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCdm (synC2nd))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((synCrn (synC2nd))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z (synC2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gVex y
  have p0002 := @gBr2nd w (.cv x) (.cv y) dv_cache_0007 dv_cache_0008 p0001
  have p0003 := @gVex z
  have p0004 := @gBr2nd t (.cv x) (.cv z) dv_cache_0009 dv_cache_0010 p0003
  have p0005 :=
    @gAnbi12i (synWbr (.cv x) (synC2nd) (.cv y))
      (synWex w (.classEq (.cv x) (synCop (.cv w) (.cv y))))
      (synWbr (.cv x) (synC2nd) (.cv z))
      (synWex t (.classEq (.cv x) (synCop (.cv t) (.cv z)))) p0002 p0004
  have p0006 :=
    @gEeanv (.classEq (.cv x) (synCop (.cv w) (.cv y)))
      (.classEq (.cv x) (synCop (.cv t) (.cv z))) w t dv_cache_0011 dv_cache_0012
  have p0007 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synC2nd) (.cv y)) (synWbr (.cv x) (synC2nd) (.cv z)))
      (synWa (synWex w (.classEq (.cv x) (synCop (.cv w) (.cv y))))
        (synWex t (.classEq (.cv x) (synCop (.cv t) (.cv z)))))
      (synWex w (synWex t (synWa (.classEq (.cv x) (synCop (.cv w) (.cv y)))
            (.classEq (.cv x) (synCop (.cv t) (.cv z))))))
      p0005 p0006
  have p0008 := @gEqtr2 (.cv x) (synCop (.cv w) (.cv y)) (synCop (.cv t) (.cv z))
  have p0009 := @gOpth (.cv w) (.cv y) (.cv t) (.cv z)
  have p0010_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv t) (.cv z)))
        (synWa (.objEq w t) (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gSimprbi (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv t) (.cv z))) (.objEq w t)
      (.objEq y z) p0010_e00_recanon
  have p0011 :=
    @gSyl
      (synWa (.classEq (.cv x) (synCop (.cv w) (.cv y)))
        (.classEq (.cv x) (synCop (.cv t) (.cv z))))
      (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv t) (.cv z))) (.objEq y z) p0008
      p0010
  have p0012 :=
    @gExlimivv
      (synWa (.classEq (.cv x) (synCop (.cv w) (.cv y)))
        (.classEq (.cv x) (synCop (.cv t) (.cv z))))
      (.objEq y z) w t dv_cache_0013 dv_cache_0014 p0011
  have p0013 :=
    @gSylbi
      (synWa (synWbr (.cv x) (synC2nd) (.cv y)) (synWbr (.cv x) (synC2nd) (.cv z)))
      (synWex w (synWex t (synWa (.classEq (.cv x) (synCop (.cv w) (.cv y)))
            (.classEq (.cv x) (synCop (.cv t) (.cv z))))))
      (.objEq y z) p0007 p0012
  have p0014 :=
    @gGen2
      (.imp (synWa (synWbr (.cv x) (synC2nd) (.cv y)) (synWbr (.cv x) (synC2nd) (.cv z)))
        (.objEq y z))
      y z p0013
  have p0015 :=
    @gMpgbir (synWfun (synC2nd))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) (synC2nd) (.cv y))
              (synWbr (.cv x) (synC2nd) (.cv z))) (.objEq y z))))
      x p0000 p0014
  have p0016 := @gEqv x (synCdm (synC2nd)) dv_cache_0015
  have p0017 := @gOpeq (.cv x)
  have p0018 := @gEqid (synCproj2 (.cv x))
  have p0019 := @gVex x
  have p0020 := @gProj1ex (.cv x) p0019
  have p0021 := @gProj2ex (.cv x) p0019
  have p0022 :=
    @gOpbr2nd (synCproj1 (.cv x)) (synCproj2 (.cv x)) (synCproj2 (.cv x)) p0020 p0021
  have p0023 :=
    @gMpbir
      (synWbr (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synC2nd)
        (synCproj2 (.cv x)))
      (.classEq (synCproj2 (.cv x)) (synCproj2 (.cv x))) p0018 p0022
  have p0024 :=
    @gBreldm (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synCproj2 (.cv x))
      (synC2nd)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gEqeltri (.cv x) (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCdm (synC2nd)) p0017 p0025
  have p0027 :=
    @gMpgbir (.classEq (synCdm (synC2nd)) (synCvv))
      (.classMem (.cv x) (synCdm (synC2nd))) x p0016 p0026
  have p0028 := (Nominal.biimpRefl (synWfn (synC2nd) (synCvv)))
  have p0029 :=
    @gMpbir2an (synWfn (synC2nd) (synCvv)) (synWfun (synC2nd))
      (.classEq (synCdm (synC2nd)) (synCvv)) p0015 p0027 p0028
  have p0030 := @gEqv x (synCrn (synC2nd)) dv_cache_0016
  have p0031 := @gEquid x
  have p0032 := @gOpbr2nd (.cv x) (.cv x) (.cv x) p0019 p0019
  have p0033_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv x)) (synC2nd) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC2nd synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @gMpbir (synWbr (synCop (.cv x) (.cv x)) (synC2nd) (.cv x)) (.objEq x x) p0031
      p0033_e01_recanon
  have p0034 := @gBrelrn (synCop (.cv x) (.cv x)) (.cv x) (synC2nd)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gMpgbir (.classEq (synCrn (synC2nd)) (synCvv))
      (.classMem (.cv x) (synCrn (synC2nd))) x p0030 p0035
  have p0037 := (Nominal.biimpRefl (synWfo (synC2nd) (synCvv) (synCvv)))
  have p0038 :=
    @gMpbir2an (synWfo (synC2nd) (synCvv) (synCvv)) (synWfn (synC2nd) (synCvv))
      (.classEq (synCrn (synC2nd)) (synCvv)) p0029 p0036 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_dfdm4`. -/
@[expose]
noncomputable def gDfdm4 (A : Class) :
    Nominal.NPrf (.classEq (synCdm A) (synCima (synC1st) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : z ≠ y := by
    clear dv_cache_0001
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0003 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0010 : x ∉ ((synCima (synC1st) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gRexcom4 (.classEq (.cv z) (synCop (.cv x) (.cv y))) z y A dv_cache_0001
      dv_cache_0002
  have p0001 := @gVex x
  have p0002 := @gBr1st y (.cv z) (.cv x) dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @gRexbii (synWbr (.cv z) (synC1st) (.cv x))
      (synWex y (.classEq (.cv z) (synCop (.cv x) (.cv y)))) z A p0002
  have p0004 := @gRisset z (synCop (.cv x) (.cv y)) A dv_cache_0005 dv_cache_0006
  have p0005 :=
    @gExbii (.classMem (synCop (.cv x) (.cv y)) A)
      (synWrex z A (.classEq (.cv z) (synCop (.cv x) (.cv y)))) y p0004
  have p0006 :=
    @gN3bitr4ri (synWrex z A (synWex y (.classEq (.cv z) (synCop (.cv x) (.cv y)))))
      (synWex y (synWrex z A (.classEq (.cv z) (synCop (.cv x) (.cv y)))))
      (synWrex z A (synWbr (.cv z) (synC1st) (.cv x)))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) A)) p0000 p0003 p0005
  have p0007 := @gEldm2 y (.cv x) A dv_cache_0004 dv_cache_0001
  have p0008 := @gElima z (.cv x) (synC1st) A dv_cache_0007 dv_cache_0008 dv_cache_0006
  have p0009 :=
    @gN3bitr4i (synWex y (.classMem (synCop (.cv x) (.cv y)) A))
      (synWrex z A (synWbr (.cv z) (synC1st) (.cv x))) (.classMem (.cv x) (synCdm A))
      (.classMem (.cv x) (synCima (synC1st) A)) p0006 p0007 p0008
  have p0010 :=
    @gEqriv x (synCdm A) (synCima (synC1st) A) dv_cache_0009 dv_cache_0010 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfrn5`. -/
@[expose]
noncomputable def gDfrn5 (A : Class) :
    Nominal.NPrf (.classEq (synCrn A) (synCima (synC2nd) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : z ≠ x := by
    clear dv_cache_0001
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0003 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCrn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCima (synC2nd) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gRexcom4 (.classEq (.cv z) (synCop (.cv x) (.cv y))) z x A dv_cache_0001
      dv_cache_0002
  have p0001 := @gVex y
  have p0002 := @gBr2nd x (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @gRexbii (synWbr (.cv z) (synC2nd) (.cv y))
      (synWex x (.classEq (.cv z) (synCop (.cv x) (.cv y)))) z A p0002
  have p0004 := @gRisset z (synCop (.cv x) (.cv y)) A dv_cache_0005 dv_cache_0006
  have p0005 :=
    @gExbii (.classMem (synCop (.cv x) (.cv y)) A)
      (synWrex z A (.classEq (.cv z) (synCop (.cv x) (.cv y)))) x p0004
  have p0006 :=
    @gN3bitr4ri (synWrex z A (synWex x (.classEq (.cv z) (synCop (.cv x) (.cv y)))))
      (synWex x (synWrex z A (.classEq (.cv z) (synCop (.cv x) (.cv y)))))
      (synWrex z A (synWbr (.cv z) (synC2nd) (.cv y)))
      (synWex x (.classMem (synCop (.cv x) (.cv y)) A)) p0000 p0003 p0005
  have p0007 := @gElrn2 x (.cv y) A dv_cache_0004 dv_cache_0001
  have p0008 := @gElima z (.cv y) (synC2nd) A dv_cache_0007 dv_cache_0008 dv_cache_0006
  have p0009 :=
    @gN3bitr4i (synWex x (.classMem (synCop (.cv x) (.cv y)) A))
      (synWrex z A (synWbr (.cv z) (synC2nd) (.cv y))) (.classMem (.cv y) (synCrn A))
      (.classMem (.cv y) (synCima (synC2nd) A)) p0006 p0007 p0008
  have p0010 :=
    @gEqriv y (synCrn A) (synCima (synC2nd) A) dv_cache_0009 dv_cache_0010 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_brswap`. -/
@[expose]
noncomputable def gBrswap (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWbr A (synCswap) B) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (.classEq B (synCop (.cv y) (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
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
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
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
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 :
    x ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          dv_B_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_y,
          dv_B_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, dv_A_y, or_false, not_false_eq_true])
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
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv b) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_b, dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ a from (by exact fresh_y_ne_a))
  have dv_cache_0008 : y ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ b from (by exact fresh_y_ne_b))
  have dv_cache_0009 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0013 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0014 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0015 : a ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0016 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0017 :
    a ∉
      ((synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (.classEq B (synCop (.cv y) (.cv x))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_B,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    b ∉
      ((synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (.classEq B (synCop (.cv y) (.cv x))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_B,
          or_false, and_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCswap)
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gOpex (.cv x) (.cv y) p0001 p0002
  have p0004 := @gEleq1 A (synCop (.cv x) (.cv y)) (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A (synCop (.cv x) (.cv y))) (.classMem A (synCvv))
      (.classMem (synCop (.cv x) (.cv y)) (synCvv)) p0003 p0004
  have p0006 := @gOpex (.cv y) (.cv x) p0002 p0001
  have p0007 := @gEleq1 B (synCop (.cv y) (.cv x)) (synCvv)
  have p0008 :=
    @gMpbiri (.classEq B (synCop (.cv y) (.cv x))) (.classMem B (synCvv))
      (.classMem (synCop (.cv y) (.cv x)) (synCvv)) p0006 p0007
  have p0009 :=
    @gAnim12i (.classEq A (synCop (.cv x) (.cv y))) (.classMem A (synCvv))
      (.classEq B (synCop (.cv y) (.cv x))) (.classMem B (synCvv)) p0005 p0008
  have p0010 :=
    @gExlimivv
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv y) (.cv x))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) x y dv_cache_0001
      dv_cache_0002 p0009
  have p0011 := @gEqeq1 (.cv a) A (synCop (.cv x) (.cv y))
  have p0012 :=
    @gAnbi1d (.classEq (.cv a) A) (.classEq (.cv a) (synCop (.cv x) (.cv y)))
      (.classEq A (synCop (.cv x) (.cv y))) (.classEq (.cv b) (synCop (.cv y) (.cv x)))
      p0011
  have p0013 :=
    @gN2exbidv (.classEq (.cv a) A)
      (synWa (.classEq (.cv a) (synCop (.cv x) (.cv y)))
        (.classEq (.cv b) (synCop (.cv y) (.cv x))))
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (.classEq (.cv b) (synCop (.cv y) (.cv x))))
      x y dv_cache_0003 dv_cache_0004 p0012
  have p0014 := @gEqeq1 (.cv b) B (synCop (.cv y) (.cv x))
  have p0015 :=
    @gAnbi2d (.classEq (.cv b) B) (.classEq (.cv b) (synCop (.cv y) (.cv x)))
      (.classEq B (synCop (.cv y) (.cv x))) (.classEq A (synCop (.cv x) (.cv y))) p0014
  have p0016 :=
    @gN2exbidv (.classEq (.cv b) B)
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (.classEq (.cv b) (synCop (.cv y) (.cv x))))
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv y) (.cv x))))
      x y dv_cache_0005 dv_cache_0006 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSwap a b x y
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @gBrabg
      (synWex x (synWex y (synWa (.classEq (.cv a) (synCop (.cv x) (.cv y)))
            (.classEq (.cv b) (synCop (.cv y) (.cv x))))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq (.cv b) (synCop (.cv y) (.cv x))))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv y) (.cv x))))))
      a b A B (synCvv) (synCvv) (synCswap) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0010 p0013 p0016 p0017
  have p0019 :=
    @gPm521nii (synWbr A (synCswap) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv y) (.cv x))))))
      p0000 p0010 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_cnvswap`. -/
@[expose]
noncomputable def gCnvswap :
    Nominal.NPrf (.classEq (synCcnv (synCswap)) (synCswap)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Class.cv b)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : a ∉ ((synCcnv (synCswap))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((synCcnv (synCswap))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((synCswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((synCswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @gAncom (.classEq (.cv b) (synCop (.cv y) (.cv x)))
      (.classEq (.cv a) (synCop (.cv x) (.cv y)))
  have p0001 :=
    @gN2exbii
      (synWa (.classEq (.cv b) (synCop (.cv y) (.cv x)))
        (.classEq (.cv a) (synCop (.cv x) (.cv y))))
      (synWa (.classEq (.cv a) (synCop (.cv x) (.cv y)))
        (.classEq (.cv b) (synCop (.cv y) (.cv x))))
      x y p0000
  have p0002 := @gBrcnv (.cv a) (.cv b) (synCswap)
  have p0003 :=
    @gBrswap y x (.cv b) (.cv a) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0004 :=
    @gExcom
      (synWa (.classEq (.cv b) (synCop (.cv y) (.cv x)))
        (.classEq (.cv a) (synCop (.cv x) (.cv y))))
      y x
  have p0005 :=
    @gN3bitri (synWbr (.cv a) (synCcnv (synCswap)) (.cv b))
      (synWbr (.cv b) (synCswap) (.cv a))
      (synWex y (synWex x (synWa (.classEq (.cv b) (synCop (.cv y) (.cv x)))
            (.classEq (.cv a) (synCop (.cv x) (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv b) (synCop (.cv y) (.cv x)))
            (.classEq (.cv a) (synCop (.cv x) (.cv y))))))
      p0002 p0003 p0004
  have p0006 :=
    @gBrswap x y (.cv a) (.cv b) dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0001
      dv_cache_0006
  have p0007 :=
    @gN3bitr4i
      (synWex x (synWex y (synWa (.classEq (.cv b) (synCop (.cv y) (.cv x)))
            (.classEq (.cv a) (synCop (.cv x) (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv a) (synCop (.cv x) (.cv y)))
            (.classEq (.cv b) (synCop (.cv y) (.cv x))))))
      (synWbr (.cv a) (synCcnv (synCswap)) (.cv b))
      (synWbr (.cv a) (synCswap) (.cv b)) p0001 p0005 p0006
  have p0008 :=
    @gEqbrriv a b (synCcnv (synCswap)) (synCswap) dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_swapf1o`. -/
@[expose]
noncomputable def gSwapf1o : Nominal.NPrf (synWf1o (synCswap) (synCvv) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have dv_cache_0001 : x ∉ ((synCswap)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCswap)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ ((synCdm (synCswap))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z (synCswap) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gOpeq (.cv y)
  have p0002 :=
    @gBreq2i (.cv y) (synCop (synCproj1 (.cv y)) (synCproj2 (.cv y))) (.cv x)
      (synCswap) p0001
  have p0003 := @gVex y
  have p0004 := @gProj1ex (.cv y) p0003
  have p0005 := @gProj2ex (.cv y) p0003
  have p0006 := @gBrswap2 (.cv x) (synCproj1 (.cv y)) (synCproj2 (.cv y)) p0004 p0005
  have p0007 :=
    @gBitri (synWbr (.cv x) (synCswap) (.cv y))
      (synWbr (.cv x) (synCswap) (synCop (synCproj1 (.cv y)) (synCproj2 (.cv y))))
      (.classEq (.cv x) (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y)))) p0002 p0006
  have p0008 := @gOpeq (.cv z)
  have p0009 :=
    @gBreq2i (.cv z) (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) (.cv x)
      (synCswap) p0008
  have p0010 := @gVex z
  have p0011 := @gProj1ex (.cv z) p0010
  have p0012 := @gProj2ex (.cv z) p0010
  have p0013 := @gBrswap2 (.cv x) (synCproj1 (.cv z)) (synCproj2 (.cv z)) p0011 p0012
  have p0014 :=
    @gBitri (synWbr (.cv x) (synCswap) (.cv z))
      (synWbr (.cv x) (synCswap) (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))))
      (.classEq (.cv x) (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z)))) p0009 p0013
  have p0015 :=
    @gEqtr2 (.cv x) (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y)))
      (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z)))
  have p0016 :=
    @gAncom (.classEq (synCproj2 (.cv y)) (synCproj2 (.cv z)))
      (.classEq (synCproj1 (.cv y)) (synCproj1 (.cv z)))
  have p0017 :=
    @gOpth (synCproj2 (.cv y)) (synCproj1 (.cv y)) (synCproj2 (.cv z))
      (synCproj1 (.cv z))
  have p0018 :=
    @gEqeq12i (.cv y) (synCop (synCproj1 (.cv y)) (synCproj2 (.cv y))) (.cv z)
      (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) p0001 p0008
  have p0019 :=
    @gOpth (synCproj1 (.cv y)) (synCproj2 (.cv y)) (synCproj1 (.cv z))
      (synCproj2 (.cv z))
  have p0020_e00_recanon :
    Nominal.NPrf
      (synWb (.objEq y z) (.classEq (synCop (synCproj1 (.cv y)) (synCproj2 (.cv y)))
          (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCproj1 synCproj2
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0018
  have p0020 :=
    @gBitri (.objEq y z)
      (.classEq (synCop (synCproj1 (.cv y)) (synCproj2 (.cv y)))
        (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))))
      (synWa (.classEq (synCproj1 (.cv y)) (synCproj1 (.cv z)))
        (.classEq (synCproj2 (.cv y)) (synCproj2 (.cv z))))
      p0020_e00_recanon p0019
  have p0021 :=
    @gN3bitr4i
      (synWa (.classEq (synCproj2 (.cv y)) (synCproj2 (.cv z)))
        (.classEq (synCproj1 (.cv y)) (synCproj1 (.cv z))))
      (synWa (.classEq (synCproj1 (.cv y)) (synCproj1 (.cv z)))
        (.classEq (synCproj2 (.cv y)) (synCproj2 (.cv z))))
      (.classEq (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y)))
        (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z))))
      (.objEq y z) p0016 p0017 p0020
  have p0022 :=
    @gSylib
      (synWa (.classEq (.cv x) (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y))))
        (.classEq (.cv x) (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z)))))
      (.classEq (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y)))
        (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z))))
      (.objEq y z) p0015 p0021
  have p0023 :=
    @gSyl2anb (synWbr (.cv x) (synCswap) (.cv y))
      (.classEq (.cv x) (synCop (synCproj2 (.cv y)) (synCproj1 (.cv y))))
      (.classEq (.cv x) (synCop (synCproj2 (.cv z)) (synCproj1 (.cv z)))) (.objEq y z)
      (synWbr (.cv x) (synCswap) (.cv z)) p0007 p0014 p0022
  have p0024 :=
    @gGen2
      (.imp (synWa (synWbr (.cv x) (synCswap) (.cv y)) (synWbr (.cv x) (synCswap) (.cv z)))
        (.objEq y z))
      y z p0023
  have p0025 :=
    @gMpgbir (synWfun (synCswap))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCswap) (.cv y))
              (synWbr (.cv x) (synCswap) (.cv z))) (.objEq y z))))
      x p0000 p0024
  have p0026 := @gEqv x (synCdm (synCswap)) dv_cache_0007
  have p0027 := @gOpeq (.cv x)
  have p0028 := @gEqid (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
  have p0029 := @gVex x
  have p0030 := @gProj2ex (.cv x) p0029
  have p0031 := @gProj1ex (.cv x) p0029
  have p0032 :=
    @gBrswap2 (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synCproj2 (.cv x))
      (synCproj1 (.cv x)) p0030 p0031
  have p0033 :=
    @gMpbir
      (synWbr (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synCswap)
        (synCop (synCproj2 (.cv x)) (synCproj1 (.cv x))))
      (.classEq (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
        (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))))
      p0028 p0032
  have p0034 :=
    @gBreldm (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCop (synCproj2 (.cv x)) (synCproj1 (.cv x))) (synCswap)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gEqeltri (.cv x) (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCdm (synCswap)) p0027 p0035
  have p0037 :=
    @gMpgbir (.classEq (synCdm (synCswap)) (synCvv))
      (.classMem (.cv x) (synCdm (synCswap))) x p0026 p0036
  have p0038 := (Nominal.biimpRefl (synWfn (synCswap) (synCvv)))
  have p0039 :=
    @gMpbir2an (synWfn (synCswap) (synCvv)) (synWfun (synCswap))
      (.classEq (synCdm (synCswap)) (synCvv)) p0025 p0037 p0038
  have p0040 := @gCnvswap
  have p0041 := @gFneq1i (synCvv) (synCcnv (synCswap)) (synCswap) p0040
  have p0042 :=
    @gMpbir (synWfn (synCcnv (synCswap)) (synCvv)) (synWfn (synCswap) (synCvv))
      p0039 p0041
  have p0043 := @gDff1o4 (synCvv) (synCvv) (synCswap)
  have p0044 :=
    @gMpbir2an (synWf1o (synCswap) (synCvv) (synCvv)) (synWfn (synCswap) (synCvv))
      (synWfn (synCcnv (synCswap)) (synCvv)) p0039 p0042 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_swapres`. -/
@[expose]
noncomputable def gSwapres (A : Class) :
    Nominal.NPrf (synWf1o (synCres (synCswap) A) A (synCcnv A)) :=
  by
  have p0000 := @gSwapf1o
  have p0001 := @gF1of1 (synCvv) (synCvv) (synCswap)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gSsv A
  have p0004 := @gF1ores (synCvv) (synCvv) A (synCswap)
  have p0005 :=
    @gMp2an (synWf1 (synCswap) (synCvv) (synCvv)) (synWss A (synCvv))
      (synWf1o (synCres (synCswap) A) A (synCima (synCswap) A)) p0002 p0003 p0004
  have p0006 := @gDfcnv2 A
  have p0007 := @gF1oeq3 (synCcnv A) (synCima (synCswap) A) A (synCres (synCswap) A)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gMpbir (synWf1o (synCres (synCswap) A) A (synCcnv A))
      (synWf1o (synCres (synCswap) A) A (synCima (synCswap) A)) p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_xpnedisj`. -/
@[expose]
noncomputable def gXpnedisj (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpnedisj_1 : Nominal.NPrf (.classMem C (synCvv)))
    (hyp_xpnedisj_2 : Nominal.NPrf (synWne C D)) :
    Nominal.NPrf
      (.classEq (synCin (synCxp A (synCsn C)) (synCxp B (synCsn D))) (synC0)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((synCxp A (synCsn C))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCxp B (synCsn D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synCsn C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_C,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synCsn C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_C,
          not_false_eq_true])
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.classEq (.cv x) (synCop (.cv y) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.neg (.classMem (.cv x) (synCxp B (synCsn D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_not_D, or_false,
          not_false_eq_true])
  have p0000 :=
    @gDisj x (synCxp A (synCsn C)) (synCxp B (synCsn D)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gElxp2 y z (.cv x) A (synCsn C) dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 := @gOpeq2 (.cv z) C (.cv y)
  have p0003 :=
    @gEqeq2d (.classEq (.cv z) C) (synCop (.cv y) (.cv z)) (synCop (.cv y) C) (.cv x)
      p0002
  have p0004 :=
    @gRexsn (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (.classEq (.cv x) (synCop (.cv y) C)) z C dv_cache_0010 dv_cache_0011
      hyp_xpnedisj_1 p0003
  have p0005 :=
    @gRexbii (synWrex z (synCsn C) (.classEq (.cv x) (synCop (.cv y) (.cv z))))
      (.classEq (.cv x) (synCop (.cv y) C)) y A p0004
  have p0006 :=
    @gBitri (.classMem (.cv x) (synCxp A (synCsn C)))
      (synWrex y A (synWrex z (synCsn C) (.classEq (.cv x) (synCop (.cv y) (.cv z)))))
      (synWrex y A (.classEq (.cv x) (synCop (.cv y) C))) p0001 p0005
  have p0007 := (Nominal.biimpRefl (synWne C D))
  have p0008 := @gMpbi (synWne C D) (.neg (.classEq C D)) hyp_xpnedisj_2 p0007
  have p0009 := @gElsni C D
  have p0010 := @gMto (.classMem C (synCsn D)) (.classEq C D) p0008 p0009
  have p0011 := @gIntnan (.classMem C (synCsn D)) (.classMem (.cv y) B) p0010
  have p0012 := @gEleq1 (.cv x) (synCop (.cv y) C) (synCxp B (synCsn D))
  have p0013 := @gOpelxp (.cv y) C B (synCsn D)
  have p0014 :=
    @gSyl6bb (.classEq (.cv x) (synCop (.cv y) C))
      (.classMem (.cv x) (synCxp B (synCsn D)))
      (.classMem (synCop (.cv y) C) (synCxp B (synCsn D)))
      (synWa (.classMem (.cv y) B) (.classMem C (synCsn D))) p0012 p0013
  have p0015 :=
    @gMtbiri (.classEq (.cv x) (synCop (.cv y) C))
      (.classMem (.cv x) (synCxp B (synCsn D)))
      (synWa (.classMem (.cv y) B) (.classMem C (synCsn D))) p0011 p0014
  have p0016 :=
    @gRexlimivw (.classEq (.cv x) (synCop (.cv y) C))
      (.neg (.classMem (.cv x) (synCxp B (synCsn D)))) y A dv_cache_0012 p0015
  have p0017 :=
    @gSylbi (.classMem (.cv x) (synCxp A (synCsn C)))
      (synWrex y A (.classEq (.cv x) (synCop (.cv y) C)))
      (.neg (.classMem (.cv x) (synCxp B (synCsn D)))) p0006 p0016
  have p0018 :=
    @gMprgbir
      (.classEq (synCin (synCxp A (synCsn C)) (synCxp B (synCsn D))) (synC0))
      (.neg (.classMem (.cv x) (synCxp B (synCsn D)))) x (synCxp A (synCsn C)) p0000
      p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_opfv1st`. -/
@[expose]
noncomputable def gOpfv1st (A : Class) (B : Class)
    (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synC1st) (synCop A B)) A) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gOpbr1st A B A hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 := @gMpbir (synWbr (synCop A B) (synC1st) A) (.classEq A A) p0000 p0001
  have p0003 := @gN1stfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gOpex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 := @gFnbrfvb (synCvv) (synCop A B) A (synC1st)
  have p0008 :=
    @gMp2an (synWfn (synC1st) (synCvv)) (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synC1st) (synCop A B)) A)
        (synWbr (synCop A B) (synC1st) A))
      p0005 p0006 p0007
  have p0009 :=
    @gMpbir (.classEq (synCfv (synC1st) (synCop A B)) A)
      (synWbr (synCop A B) (synC1st) A) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_opfv2nd`. -/
@[expose]
noncomputable def gOpfv2nd (A : Class) (B : Class)
    (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synC2nd) (synCop A B)) B) :=
  by
  have p0000 := @gEqid B
  have p0001 := @gOpbr2nd A B B hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 := @gMpbir (synWbr (synCop A B) (synC2nd) B) (.classEq B B) p0000 p0001
  have p0003 := @gN2ndfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gOpex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 := @gFnbrfvb (synCvv) (synCop A B) B (synC2nd)
  have p0008 :=
    @gMp2an (synWfn (synC2nd) (synCvv)) (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synC2nd) (synCop A B)) B)
        (synWbr (synCop A B) (synC2nd) B))
      p0005 p0006 p0007
  have p0009 :=
    @gMpbir (.classEq (synCfv (synC2nd) (synCop A B)) B)
      (synWbr (synCop A B) (synC2nd) B) p0002 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
