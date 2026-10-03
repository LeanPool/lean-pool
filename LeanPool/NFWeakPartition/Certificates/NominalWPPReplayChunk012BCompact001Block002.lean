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

@[expose]
noncomputable def g_f1oiso (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) (B : Class)
    (R : Class) (S : Class) (H : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_H_w : w ∉ H.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_H_z : z ∉ H.fv)
    (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A
                  (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                      (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
        (syn_wiso H R S A B)) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (syn_cfv H (.cv v)))).fv := by
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
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (syn_cfv H (.cv v)))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv w) (syn_cfv H (.cv u)))).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv w) (syn_cfv H (.cv u)))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cfv H (.cv v))).fv :=
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
  have dv_cache_0006 : w ∉ ((syn_cfv H (.cv v))).fv :=
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
  have dv_cache_0007 : z ∉ ((syn_cfv H (.cv u))).fv :=
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
  have dv_cache_0008 : w ∉ ((syn_cfv H (.cv u))).fv :=
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
      ((syn_wrex x A (syn_wrex y A (syn_wa
              (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
                (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))))
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
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
      ((syn_wrex x A (syn_wrex y A (syn_wa
              (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
                (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))))
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
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
      ((syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))).fv :=
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
  have dv_cache_0014 : x ∉ ((syn_wa (syn_wf1 H A B) (.classMem (.cv v) A))).fv :=
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
      ((syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
            (syn_wbr (.cv v) R (.cv y))))).fv :=
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
  have dv_cache_0018 : y ∉ ((syn_wa (syn_wf1 H A B) (.classMem (.cv u) A))).fv :=
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
  have dv_cache_0021 : y ∉ ((syn_wbr (.cv v) R (.cv u))).fv :=
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
      ((syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                    (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                      (.classEq (.cv w) (syn_cfv H (.cv y))))
                    (syn_wbr (.cv x) R (.cv y))))))))).fv :=
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
      ((syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                    (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                      (.classEq (.cv w) (syn_cfv H (.cv y))))
                    (syn_wbr (.cv x) R (.cv y))))))))).fv :=
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
    @g_simpl (syn_wf1o H A B)
      (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
  have p0001 := @g_f1of1 A B H
  have p0002 := (Nominal.biimpRefl (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u))))
  have p0003 :=
    @g_eleq2 S
      (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
              (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))
      (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u)))
  have p0004 := @g_fvex (.cv v) H
  have p0005 := @g_fvex (.cv u) H
  have p0006 := @g_eqeq1 (.cv z) (syn_cfv H (.cv v)) (syn_cfv H (.cv x))
  have p0007 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv H (.cv v)))
      (.classEq (.cv z) (syn_cfv H (.cv x)))
      (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
      (.classEq (.cv w) (syn_cfv H (.cv y))) p0006
  have p0008 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv H (.cv v)))
      (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y))))
      (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
        (.classEq (.cv w) (syn_cfv H (.cv y))))
      (syn_wbr (.cv x) R (.cv y)) p0007
  have p0009 :=
    @g_n_2rexbidv (.classEq (.cv z) (syn_cfv H (.cv v)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
          (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
          (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      x y A A dv_cache_0001 dv_cache_0002 p0008
  have p0010 := @g_eqeq1 (.cv w) (syn_cfv H (.cv u)) (syn_cfv H (.cv y))
  have p0011 :=
    @g_anbi2d (.classEq (.cv w) (syn_cfv H (.cv u)))
      (.classEq (.cv w) (syn_cfv H (.cv y)))
      (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
      (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) p0010
  have p0012 :=
    @g_anbi1d (.classEq (.cv w) (syn_cfv H (.cv u)))
      (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
        (.classEq (.cv w) (syn_cfv H (.cv y))))
      (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
        (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))))
      (syn_wbr (.cv x) R (.cv y)) p0011
  have p0013 :=
    @g_n_2rexbidv (.classEq (.cv w) (syn_cfv H (.cv u)))
      (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
          (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
          (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      x y A A dv_cache_0003 dv_cache_0004 p0012
  have p0014 :=
    @g_opelopab
      (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
              (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wrex x A (syn_wrex y A (syn_wa
            (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
              (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wrex x A (syn_wrex y A (syn_wa
            (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
              (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      z w (syn_cfv H (.cv v)) (syn_cfv H (.cv u)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0004 p0005
      p0009 p0013
  have p0015 :=
    @g_anass (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
      (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0016 := @g_f1fveq A B (.cv v) (.cv x) H
  have p0017 := @g_eqcom (.cv v) (.cv x)
  have p0018 :=
    @g_syl6bb
      (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv x) A)))
      (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv v) (.cv x))
      (.classEq (.cv x) (.cv v)) p0016 p0017
  have p0019 :=
    @g_anassrs (syn_wf1 H A B) (.classMem (.cv v) A) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv x) (.cv v)))
      p0018
  have p0020 :=
    @g_anbi1d
      (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv x) (.cv v))
      (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      p0019
  have p0021 :=
    @g_syl5bb
      (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
          (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
        (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (syn_wa (.classEq (.cv x) (.cv v))
        (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      p0015 p0020
  have p0022 :=
    @g_rexbidv
      (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
          (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (.cv x) (.cv v))
        (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      y A dv_cache_0012 p0021
  have p0023 :=
    @g_r19_42v (.classEq (.cv x) (.cv v))
      (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      y A dv_cache_0013
  have p0024 :=
    @g_syl6bb
      (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))
      (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
            (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))
      (syn_wrex y A (syn_wa (.classEq (.cv x) (.cv v))
          (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A
          (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      p0022 p0023
  have p0025 :=
    @g_rexbidva (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A))
      (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
            (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))
      (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A
          (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      x A dv_cache_0014 p0024
  have p0026 := @g_breq1 (.cv x) (.cv v) (.cv y) R
  have p0027 :=
    @g_anbi2d (.classEq (.cv x) (.cv v)) (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (.cv v) R (.cv y)) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) p0026
  have p0028 :=
    @g_rexbidv (.classEq (.cv x) (.cv v))
      (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))
      y A dv_cache_0013 p0027
  have p0029 :=
    @g_ceqsrexv
      (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
          (syn_wbr (.cv x) R (.cv y))))
      (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
          (syn_wbr (.cv v) R (.cv y))))
      x (.cv v) A dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @g_adantl (.classMem (.cv v) A)
      (syn_wb (syn_wrex x A (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A
              (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
                (syn_wbr (.cv x) R (.cv y)))))) (syn_wrex y A
          (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
            (syn_wbr (.cv v) R (.cv y)))))
      (syn_wf1 H A B) p0029
  have p0031 :=
    @g_bitrd (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A))
      (syn_wrex x A (syn_wrex y A (syn_wa
            (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
              (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wrex x A (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A
            (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
              (syn_wbr (.cv x) R (.cv y))))))
      (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
          (syn_wbr (.cv v) R (.cv y))))
      p0025 p0030
  have p0032 := @g_f1fveq A B (.cv u) (.cv y) H
  have p0033 := @g_eqcom (.cv u) (.cv y)
  have p0034 :=
    @g_syl6bb
      (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv u) A) (.classMem (.cv y) A)))
      (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv u) (.cv y))
      (.classEq (.cv y) (.cv u)) p0032 p0033
  have p0035 :=
    @g_anassrs (syn_wf1 H A B) (.classMem (.cv u) A) (.classMem (.cv y) A)
      (syn_wb (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv y) (.cv u)))
      p0034
  have p0036 :=
    @g_anbi1d
      (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (.classMem (.cv y) A))
      (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv y) (.cv u))
      (syn_wbr (.cv v) R (.cv y)) p0035
  have p0037 :=
    @g_rexbidva (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A))
      (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))
      (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y))) y A dv_cache_0018
      p0036
  have p0038 := @g_breq2 (.cv y) (.cv u) (.cv v) R
  have p0039 :=
    @g_ceqsrexv (syn_wbr (.cv v) R (.cv y)) (syn_wbr (.cv v) R (.cv u)) y (.cv u) A
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0038
  have p0040 :=
    @g_adantl (.classMem (.cv u) A)
      (syn_wb (syn_wrex y A (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y))))
        (syn_wbr (.cv v) R (.cv u)))
      (syn_wf1 H A B) p0039
  have p0041 :=
    @g_bitrd (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A))
      (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
          (syn_wbr (.cv v) R (.cv y))))
      (syn_wrex y A (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y))))
      (syn_wbr (.cv v) R (.cv u)) p0037 p0040
  have p0042 :=
    @g_sylan9bb (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A))
      (syn_wrex x A (syn_wrex y A (syn_wa
            (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
              (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))
          (syn_wbr (.cv v) R (.cv y))))
      (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (syn_wbr (.cv v) R (.cv u)) p0031
      p0041
  have p0043 :=
    @g_anandis (syn_wf1 H A B) (.classMem (.cv v) A) (.classMem (.cv u) A)
      (syn_wb (syn_wrex x A (syn_wrex y A (syn_wa
              (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
                (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))) (syn_wbr (.cv v) R (.cv u)))
      p0042
  have p0044 :=
    @g_syl5bb
      (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) (syn_copab z w (syn_wrex x A
            (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (syn_wrex x A (syn_wrex y A (syn_wa
            (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x)))
              (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (syn_wbr (.cv v) R (.cv u)) p0014 p0043
  have p0045 :=
    @g_sylan9bbr
      (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S)
      (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) (syn_copab z w (syn_wrex x A
            (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (syn_wbr (.cv v) R (.cv u)) p0003 p0044
  have p0046 :=
    @g_an32s (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A))
      (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (syn_wb (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S)
        (syn_wbr (.cv v) R (.cv u)))
      p0045
  have p0047 :=
    @g_syl5rbb (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u)))
      (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S)
      (syn_wa (syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A
                  (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                      (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
        (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A)))
      (syn_wbr (.cv v) R (.cv u)) p0002 p0046
  have p0048 :=
    @g_ralrimivva
      (syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                  (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                    (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wb (syn_wbr (.cv v) R (.cv u)) (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u))))
      v u A A dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0047
  have p0049 :=
    @g_sylan (syn_wf1o H A B) (syn_wf1 H A B)
      (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                  (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (syn_wral v A (syn_wral u A (syn_wb (syn_wbr (.cv v) R (.cv u))
            (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u))))))
      p0001 p0048
  have p0050 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso v u A B R S H
      dv_cache_0026 dv_cache_0022 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0025
  have p0051 :=
    @g_sylanbrc
      (syn_wa (syn_wf1o H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa
                  (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x)))
                    (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wf1o H A B)
      (syn_wral v A (syn_wral u A (syn_wb (syn_wbr (.cv v) R (.cv u))
            (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u))))))
      (syn_wiso H R S A B) p0000 p0049 p0050
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

@[expose]
noncomputable def g_f1oiso2 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_f1oiso2_1 : Nominal.NPrf (.classEq S (syn_copab x y
            (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
              (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))))) :
    Nominal.NPrf (.imp (syn_wf1o H A B) (syn_wiso H R S A B)) :=
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
  have dv_cache_0001 : w ∉ ((syn_cfv (syn_ccnv H) (.cv y))).fv := by
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
      ((syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
            (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv :=
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
  have dv_cache_0004 : w ∉ ((Wff.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x)))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cfv (syn_ccnv H) (.cv x))).fv :=
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
      ((syn_wrex w A (syn_wa
            (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
              (.classEq (.cv y) (syn_cfv H (.cv w))))
            (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv :=
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
  have dv_cache_0010 : z ∉ ((syn_wf1o H A B)).fv :=
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
  have dv_cache_0011 : w ∉ ((syn_wf1o H A B)).fv :=
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
  have dv_cache_0013 : x ∉ ((syn_wf1o H A B)).fv :=
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
  have dv_cache_0014 : y ∉ ((syn_wf1o H A B)).fv :=
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
  have p0000 := @g_f1ocnvdm A B (.cv x) H
  have p0001 :=
    @g_adantrr (syn_wf1o H A B) (.classMem (.cv x) B)
      (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A) (.classMem (.cv y) B) p0000
  have p0002 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A)
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0001
  have p0003 := @g_f1ocnvdm A B (.cv y) H
  have p0004 :=
    @g_adantrl (syn_wf1o H A B) (.classMem (.cv y) B)
      (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A) (.classMem (.cv x) B) p0003
  have p0005 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A)
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0004
  have p0006 := @g_f1ocnvfv2 A B (.cv x) H
  have p0007 :=
    @g_eqcomd (syn_wa (syn_wf1o H A B) (.classMem (.cv x) B))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))) (.cv x) p0006
  have p0008 := @g_f1ocnvfv2 A B (.cv y) H
  have p0009 :=
    @g_eqcomd (syn_wa (syn_wf1o H A B) (.classMem (.cv y) B))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))) (.cv y) p0008
  have p0010 :=
    @g_anim12dan (syn_wf1o H A B) (.classMem (.cv x) B)
      (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classMem (.cv y) B)
      (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))) p0007 p0009
  have p0011 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
        (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0010
  have p0012 :=
    @g_simp3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))
  have p0013 := @g_fveq2 (.cv w) (syn_cfv (syn_ccnv H) (.cv y)) H
  have p0014 :=
    @g_eqeq2d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y))) (syn_cfv H (.cv w))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))) (.cv y) p0013
  have p0015 :=
    @g_anbi2d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y)))
      (.classEq (.cv y) (syn_cfv H (.cv w)))
      (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))
      (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) p0014
  have p0016 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv H) (.cv y)) (syn_cfv (syn_ccnv H) (.cv x)) R
  have p0017 :=
    @g_anbi12d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y)))
      (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
        (.classEq (.cv y) (syn_cfv H (.cv w))))
      (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
        (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0015
      p0016
  have p0018 :=
    @g_rspcev
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
          (.classEq (.cv y) (syn_cfv H (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)))
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
          (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      w (syn_cfv (syn_ccnv H) (.cv y)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @g_syl12anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A)
      (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
        (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))
      (syn_wrex w A (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
            (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))))
      p0005 p0011 p0012 p0018
  have p0020 := @g_fveq2 (.cv z) (syn_cfv (syn_ccnv H) (.cv x)) H
  have p0021 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x))) (syn_cfv H (.cv z))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))) (.cv x) p0020
  have p0022 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x)))
      (.classEq (.cv x) (syn_cfv H (.cv z)))
      (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
      (.classEq (.cv y) (syn_cfv H (.cv w))) p0021
  have p0023 := @g_breq1 (.cv z) (syn_cfv (syn_ccnv H) (.cv x)) (.cv w) R
  have p0024 :=
    @g_anbi12d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x)))
      (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
      (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
        (.classEq (.cv y) (syn_cfv H (.cv w))))
      (syn_wbr (.cv z) R (.cv w)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)) p0022
      p0023
  have p0025 :=
    @g_rexbidv (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x)))
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
          (.classEq (.cv y) (syn_cfv H (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)))
      w A dv_cache_0004 p0024
  have p0026 :=
    @g_rspcev
      (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
            (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))
      (syn_wrex w A (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
            (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))))
      z (syn_cfv (syn_ccnv H) (.cv x)) A dv_cache_0005 dv_cache_0006 dv_cache_0007 p0025
  have p0027 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A)
      (syn_wrex w A (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))))
            (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))))
      (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
              (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))
      p0002 p0019 p0026
  have p0028 :=
    @g_n_3expib (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))
      (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
              (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))
      p0027
  have p0029 :=
    @g_simp3ll (.classEq (.cv x) (syn_cfv H (.cv z)))
      (.classEq (.cv y) (syn_cfv H (.cv w))) (syn_wbr (.cv z) R (.cv w)) (syn_wf1o H A B)
      (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0030 :=
    @g_simp1 (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0031 :=
    @g_simp2l (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A)
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0032 := @g_f1of A B H
  have p0033 := @g_ffvelrn A B (.cv z) H
  have p0034 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B) (.classMem (.cv z) A)
      (.classMem (syn_cfv H (.cv z)) B) p0032 p0033
  have p0035 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (syn_cfv H (.cv z)) B) p0030 p0031
      p0034
  have p0036 :=
    @g_eqeltrd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.cv x) (syn_cfv H (.cv z)) B p0029 p0035
  have p0037 :=
    @g_simp3lr (.classEq (.cv x) (syn_cfv H (.cv z)))
      (.classEq (.cv y) (syn_cfv H (.cv w))) (syn_wbr (.cv z) R (.cv w)) (syn_wf1o H A B)
      (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0038 :=
    @g_simp2r (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A)
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0039 := @g_ffvelrn A B (.cv w) H
  have p0040 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B) (.classMem (.cv w) A)
      (.classMem (syn_cfv H (.cv w)) B) p0032 p0039
  have p0041 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (syn_wf1o H A B) (.classMem (.cv w) A) (.classMem (syn_cfv H (.cv w)) B) p0030 p0038
      p0040
  have p0042 :=
    @g_eqeltrd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.cv y) (syn_cfv H (.cv w)) B p0037 p0041
  have p0043 :=
    @g_simp3r (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
      (syn_wbr (.cv z) R (.cv w))
  have p0044 :=
    @g_eqcomd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.cv x) (syn_cfv H (.cv z)) p0029
  have p0045 := @g_f1ocnvfv A B (.cv z) (.cv x) H
  have p0046 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (syn_wf1o H A B) (.classMem (.cv z) A)
      (.imp (.classEq (syn_cfv H (.cv z)) (.cv x))
        (.classEq (syn_cfv (syn_ccnv H) (.cv x)) (.cv z)))
      p0030 p0031 p0045
  have p0047 :=
    @g_mpd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.classEq (syn_cfv H (.cv z)) (.cv x))
      (.classEq (syn_cfv (syn_ccnv H) (.cv x)) (.cv z)) p0044 p0046
  have p0048 :=
    @g_eqcomd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.cv y) (syn_cfv H (.cv w)) p0037
  have p0049 := @g_f1ocnvfv A B (.cv w) (.cv y) H
  have p0050 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (syn_wf1o H A B) (.classMem (.cv w) A)
      (.imp (.classEq (syn_cfv H (.cv w)) (.cv y))
        (.classEq (syn_cfv (syn_ccnv H) (.cv y)) (.cv w)))
      p0030 p0038 p0049
  have p0051 :=
    @g_mpd
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.classEq (syn_cfv H (.cv w)) (.cv y))
      (.classEq (syn_cfv (syn_ccnv H) (.cv y)) (.cv w)) p0048 p0050
  have p0052 :=
    @g_n_3brtr4d
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.cv z) (.cv w) (syn_cfv (syn_ccnv H) (.cv x)) (syn_cfv (syn_ccnv H) (.cv y)) R
      p0043 p0047 p0051
  have p0053 :=
    @g_jca31
      (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa
          (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))))
          (syn_wbr (.cv z) R (.cv w))))
      (.classMem (.cv x) B) (.classMem (.cv y) B)
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0036
      p0042 p0052
  have p0054 :=
    @g_n_3exp (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      p0053
  have p0055 :=
    @g_rexlimdvv (syn_wf1o H A B)
      (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
          (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      z w A A dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0054
  have p0056 :=
    @g_impbid (syn_wf1o H A B)
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
              (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))
      p0028 p0055
  have p0057 :=
    @g_opabbidv (syn_wf1o H A B)
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))
      (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
              (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))
      x y dv_cache_0013 dv_cache_0014 p0056
  have p0058 :=
    @g_syl5eq (syn_wf1o H A B) S
      (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))))
      (syn_copab x y (syn_wrex z A (syn_wrex w A (syn_wa
              (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
                (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))))
      hyp_f1oiso2_1 p0057
  have p0059 :=
    @g_f1oiso z w x y A B R S H dv_cache_0015 dv_cache_0006 dv_cache_0002 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
      dv_cache_0029 dv_cache_0012 dv_cache_0030 dv_cache_0031
  have p0060 :=
    @g_mpdan (syn_wf1o H A B)
      (.classEq S (syn_copab x y (syn_wrex z A (syn_wrex w A (syn_wa
                (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z)))
                  (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))))
      (syn_wiso H R S A B) p0058 p0059
  exact p0060

@[expose]
noncomputable def g_opbr1st (A : Class) (B : Class) (C : Class)
    (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_c1st) C) (.classEq A C)) :=
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
  have dv_cache_0001 : y ∉ ((syn_cop A B)).fv := by
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
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cop A B) (syn_c1st) C)).fv :=
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
  have p0000 := @g_brex (syn_cop A B) C (syn_c1st)
  have p0001 :=
    @g_simprd (syn_wbr (syn_cop A B) (syn_c1st) C) (.classMem (syn_cop A B) (syn_cvv))
      (.classMem C (syn_cvv)) p0000
  have p0002 := @g_eleq1 A C (syn_cvv)
  have p0003 :=
    @g_mpbii (.classEq A C) (.classMem A (syn_cvv)) (.classMem C (syn_cvv)) hyp_opbr1st_1
      p0002
  have p0004 := @g_breq2 (.cv x) C (syn_cop A B) (syn_c1st)
  have p0005 := @g_eqeq2 (.cv x) C A
  have p0006 := @g_vex x
  have p0007 := @g_br1st y (syn_cop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @g_biidd (.classEq (.cv y) B) (.classEq (.cv x) A)
  have p0009 :=
    @g_ceqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) y B dv_cache_0003 dv_cache_0004
      hyp_opbr1st_2 p0008
  have p0010 := @g_eqcom (syn_cop A B) (syn_cop (.cv x) (.cv y))
  have p0011 := @g_opth (.cv x) (.cv y) A B
  have p0012 := @g_ancom (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0013 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0011 p0012
  have p0014 :=
    @g_bitri (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0010 p0013
  have p0015 :=
    @g_exbii (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) y p0014
  have p0016 := @g_eqcom A (.cv x)
  have p0017 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)))
      (.classEq (.cv x) A) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))))
      (.classEq A (.cv x)) p0009 p0015 p0016
  have p0018 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c1st) (.cv x))
      (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))) (.classEq A (.cv x))
      p0007 p0017
  have p0019 :=
    @g_vtoclbg (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (.classEq A (.cv x))
      (syn_wbr (syn_cop A B) (syn_c1st) C) (.classEq A C) x C (syn_cvv) dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0004 p0005 p0018
  have p0020 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_c1st) C) (.classMem C (syn_cvv))
      (.classEq A C) p0001 p0003 p0019
  exact p0020

@[expose]
noncomputable def g_opbr2nd (A : Class) (B : Class) (C : Class)
    (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classEq B C)) :=
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
  have dv_cache_0001 : y ∉ ((syn_cop A B)).fv := by
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
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cop A B) (syn_c2nd) C)).fv :=
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
  have p0000 := @g_brex (syn_cop A B) C (syn_c2nd)
  have p0001 :=
    @g_simprd (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classMem (syn_cop A B) (syn_cvv))
      (.classMem C (syn_cvv)) p0000
  have p0002 := @g_eleq1 B C (syn_cvv)
  have p0003 :=
    @g_mpbii (.classEq B C) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) hyp_opbr1st_2
      p0002
  have p0004 := @g_breq2 (.cv x) C (syn_cop A B) (syn_c2nd)
  have p0005 := @g_eqeq2 (.cv x) C B
  have p0006 := @g_vex x
  have p0007 := @g_br2nd y (syn_cop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @g_biidd (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0009 :=
    @g_ceqsexv (.classEq (.cv x) B) (.classEq (.cv x) B) y A dv_cache_0003 dv_cache_0004
      hyp_opbr1st_1 p0008
  have p0010 := @g_eqcom (syn_cop A B) (syn_cop (.cv y) (.cv x))
  have p0011 := @g_opth (.cv y) (.cv x) A B
  have p0012 :=
    @g_bitri (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x)))
      (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B))
      (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)) p0010 p0011
  have p0013 :=
    @g_exbii (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x)))
      (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)) y p0012
  have p0014 := @g_eqcom B (.cv x)
  have p0015 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)))
      (.classEq (.cv x) B) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x))))
      (.classEq B (.cv x)) p0009 p0013 p0014
  have p0016 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x))
      (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x)))) (.classEq B (.cv x))
      p0007 p0015
  have p0017 :=
    @g_vtoclbg (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (.classEq B (.cv x))
      (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classEq B C) x C (syn_cvv) dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0004 p0005 p0016
  have p0018 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classMem C (syn_cvv))
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

@[expose]
noncomputable def g_dfid4 :
    Nominal.NPrf (.classEq (syn_cid) (syn_cin (syn_csset) (syn_ccnv (syn_csset)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cin (syn_csset) (syn_ccnv (syn_csset)))).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_cin (syn_csset) (syn_ccnv (syn_csset)))).fv :=
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
  have p0000 := @g_eqss (.cv x) (.cv y)
  have p0001 := @g_vex y
  have p0002 := @g_ideq (.cv x) (.cv y) p0001
  have p0003 := @g_brin (.cv x) (.cv y) (syn_csset) (syn_ccnv (syn_csset))
  have p0004 := @g_vex x
  have p0005 := @g_brsset (.cv x) (.cv y) p0004 p0001
  have p0006 := @g_brcnv (.cv x) (.cv y) (syn_csset)
  have p0007 := @g_brsset (.cv y) (.cv x) p0001 p0004
  have p0008 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_csset)) (.cv y))
      (syn_wbr (.cv y) (syn_csset) (.cv x)) (syn_wss (.cv y) (.cv x)) p0006 p0007
  have p0009 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_csset) (.cv y)) (syn_wss (.cv x) (.cv y))
      (syn_wbr (.cv x) (syn_ccnv (syn_csset)) (.cv y)) (syn_wss (.cv y) (.cv x)) p0005
      p0008
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_cin (syn_csset) (syn_ccnv (syn_csset))) (.cv y))
      (syn_wa (syn_wbr (.cv x) (syn_csset) (.cv y))
        (syn_wbr (.cv x) (syn_ccnv (syn_csset)) (.cv y)))
      (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x))) p0003 p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
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
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_n_3bitr4i (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x)))
      (syn_wbr (.cv x) (syn_cid) (.cv y))
      (syn_wbr (.cv x) (syn_cin (syn_csset) (syn_ccnv (syn_csset))) (.cv y))
      p0011_e00_recanon p0011_e01_recanon p0010
  have p0012 :=
    @g_eqbrriv x y (syn_cid) (syn_cin (syn_csset) (syn_ccnv (syn_csset))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0011
  exact p0012

@[expose]
noncomputable def g_idex : Nominal.NPrf (.classMem (syn_cid) (syn_cvv)) :=
  by
  have p0000 := @g_dfid4
  have p0001 := @g_ssetex
  have p0003 := @g_cnvex (syn_csset) p0001
  have p0004 := @g_inex (syn_csset) (syn_ccnv (syn_csset)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cid) (syn_cin (syn_csset) (syn_ccnv (syn_csset))) (syn_cvv) p0000
      p0004
  exact p0005

@[expose]
noncomputable def g_n_1stfo : Nominal.NPrf (syn_wfo (syn_c1st) (syn_cvv) (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_c1st)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0011 : t ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv w)))).fv :=
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
  have dv_cache_0012 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv z) (.cv t)))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cdm (syn_c1st))).fv :=
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
  have dv_cache_0016 : x ∉ ((syn_crn (syn_c1st))).fv :=
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
    @g_dffun2 x y z (syn_c1st) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_vex y
  have p0002 := @g_br1st w (.cv x) (.cv y) dv_cache_0007 dv_cache_0008 p0001
  have p0003 := @g_vex z
  have p0004 := @g_br1st t (.cv x) (.cv z) dv_cache_0009 dv_cache_0010 p0003
  have p0005 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_c1st) (.cv y))
      (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w))))
      (syn_wbr (.cv x) (syn_c1st) (.cv z))
      (syn_wex t (.classEq (.cv x) (syn_cop (.cv z) (.cv t)))) p0002 p0004
  have p0006 :=
    @g_eeanv (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
      (.classEq (.cv x) (syn_cop (.cv z) (.cv t))) w t dv_cache_0011 dv_cache_0012
  have p0007 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv y)) (syn_wbr (.cv x) (syn_c1st) (.cv z)))
      (syn_wa (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w))))
        (syn_wex t (.classEq (.cv x) (syn_cop (.cv z) (.cv t)))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv z) (.cv t))))))
      p0005 p0006
  have p0008 := @g_eqtr2 (.cv x) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv z) (.cv t))
  have p0009 := @g_opth (.cv y) (.cv w) (.cv z) (.cv t)
  have p0010_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv z) (.cv t)))
        (syn_wa (.objEq y z) (.objEq w t))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_simplbi (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv z) (.cv t))) (.objEq y z)
      (.objEq w t) p0010_e00_recanon
  have p0011 :=
    @g_syl
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv z) (.cv t))))
      (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv z) (.cv t))) (.objEq y z) p0008
      p0010
  have p0012 :=
    @g_exlimivv
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv z) (.cv t))))
      (.objEq y z) w t dv_cache_0013 dv_cache_0014 p0011
  have p0013 :=
    @g_sylbi
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv y)) (syn_wbr (.cv x) (syn_c1st) (.cv z)))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv z) (.cv t))))))
      (.objEq y z) p0007 p0012
  have p0014 :=
    @g_gen2
      (.imp (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv y)) (syn_wbr (.cv x) (syn_c1st) (.cv z)))
        (.objEq y z))
      y z p0013
  have p0015 :=
    @g_mpgbir (syn_wfun (syn_c1st))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv y))
              (syn_wbr (.cv x) (syn_c1st) (.cv z))) (.objEq y z))))
      x p0000 p0014
  have p0016 := @g_eqv x (syn_cdm (syn_c1st)) dv_cache_0015
  have p0017 := @g_opeq (.cv x)
  have p0018 := @g_eqid (syn_cproj1 (.cv x))
  have p0019 := @g_vex x
  have p0020 := @g_proj1ex (.cv x) p0019
  have p0021 := @g_proj2ex (.cv x) p0019
  have p0022 :=
    @g_opbr1st (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x)) p0020 p0021
  have p0023 :=
    @g_mpbir
      (syn_wbr (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_c1st)
        (syn_cproj1 (.cv x)))
      (.classEq (syn_cproj1 (.cv x)) (syn_cproj1 (.cv x))) p0018 p0022
  have p0024 :=
    @g_breldm (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cproj1 (.cv x))
      (syn_c1st)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_cdm (syn_c1st)) p0017 p0025
  have p0027 :=
    @g_mpgbir (.classEq (syn_cdm (syn_c1st)) (syn_cvv))
      (.classMem (.cv x) (syn_cdm (syn_c1st))) x p0016 p0026
  have p0028 := (Nominal.biimpRefl (syn_wfn (syn_c1st) (syn_cvv)))
  have p0029 :=
    @g_mpbir2an (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfun (syn_c1st))
      (.classEq (syn_cdm (syn_c1st)) (syn_cvv)) p0015 p0027 p0028
  have p0030 := @g_eqv x (syn_crn (syn_c1st)) dv_cache_0016
  have p0031 := @g_eqid (.cv x)
  have p0032 := @g_opbr1st (.cv x) (.cv x) (.cv x) p0019 p0019
  have p0033_e00_recanon : Nominal.NPrf (.objEq x x) :=
    Nominal.RecanonTransportDev.transport
      (by exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _) p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv x)) (syn_c1st) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_mpbir (syn_wbr (syn_cop (.cv x) (.cv x)) (syn_c1st) (.cv x)) (.objEq x x)
      p0033_e00_recanon p0033_e01_recanon
  have p0034 := @g_brelrn (syn_cop (.cv x) (.cv x)) (.cv x) (syn_c1st)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_mpgbir (.classEq (syn_crn (syn_c1st)) (syn_cvv))
      (.classMem (.cv x) (syn_crn (syn_c1st))) x p0030 p0035
  have p0037 := (Nominal.biimpRefl (syn_wfo (syn_c1st) (syn_cvv) (syn_cvv)))
  have p0038 :=
    @g_mpbir2an (syn_wfo (syn_c1st) (syn_cvv) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (.classEq (syn_crn (syn_c1st)) (syn_cvv)) p0029 p0036 p0037
  exact p0038

@[expose]
noncomputable def g_n_2ndfo : Nominal.NPrf (syn_wfo (syn_c2nd) (syn_cvv) (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_c2nd)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0011 : t ∉ ((Wff.classEq (.cv x) (syn_cop (.cv w) (.cv y)))).fv :=
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
  have dv_cache_0012 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv t) (.cv z)))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cdm (syn_c2nd))).fv :=
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
  have dv_cache_0016 : x ∉ ((syn_crn (syn_c2nd))).fv :=
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
    @g_dffun2 x y z (syn_c2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_vex y
  have p0002 := @g_br2nd w (.cv x) (.cv y) dv_cache_0007 dv_cache_0008 p0001
  have p0003 := @g_vex z
  have p0004 := @g_br2nd t (.cv x) (.cv z) dv_cache_0009 dv_cache_0010 p0003
  have p0005 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_c2nd) (.cv y))
      (syn_wex w (.classEq (.cv x) (syn_cop (.cv w) (.cv y))))
      (syn_wbr (.cv x) (syn_c2nd) (.cv z))
      (syn_wex t (.classEq (.cv x) (syn_cop (.cv t) (.cv z)))) p0002 p0004
  have p0006 :=
    @g_eeanv (.classEq (.cv x) (syn_cop (.cv w) (.cv y)))
      (.classEq (.cv x) (syn_cop (.cv t) (.cv z))) w t dv_cache_0011 dv_cache_0012
  have p0007 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_c2nd) (.cv y)) (syn_wbr (.cv x) (syn_c2nd) (.cv z)))
      (syn_wa (syn_wex w (.classEq (.cv x) (syn_cop (.cv w) (.cv y))))
        (syn_wex t (.classEq (.cv x) (syn_cop (.cv t) (.cv z)))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv x) (syn_cop (.cv w) (.cv y)))
            (.classEq (.cv x) (syn_cop (.cv t) (.cv z))))))
      p0005 p0006
  have p0008 := @g_eqtr2 (.cv x) (syn_cop (.cv w) (.cv y)) (syn_cop (.cv t) (.cv z))
  have p0009 := @g_opth (.cv w) (.cv y) (.cv t) (.cv z)
  have p0010_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv t) (.cv z)))
        (syn_wa (.objEq w t) (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_simprbi (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv t) (.cv z))) (.objEq w t)
      (.objEq y z) p0010_e00_recanon
  have p0011 :=
    @g_syl
      (syn_wa (.classEq (.cv x) (syn_cop (.cv w) (.cv y)))
        (.classEq (.cv x) (syn_cop (.cv t) (.cv z))))
      (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv t) (.cv z))) (.objEq y z) p0008
      p0010
  have p0012 :=
    @g_exlimivv
      (syn_wa (.classEq (.cv x) (syn_cop (.cv w) (.cv y)))
        (.classEq (.cv x) (syn_cop (.cv t) (.cv z))))
      (.objEq y z) w t dv_cache_0013 dv_cache_0014 p0011
  have p0013 :=
    @g_sylbi
      (syn_wa (syn_wbr (.cv x) (syn_c2nd) (.cv y)) (syn_wbr (.cv x) (syn_c2nd) (.cv z)))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv x) (syn_cop (.cv w) (.cv y)))
            (.classEq (.cv x) (syn_cop (.cv t) (.cv z))))))
      (.objEq y z) p0007 p0012
  have p0014 :=
    @g_gen2
      (.imp (syn_wa (syn_wbr (.cv x) (syn_c2nd) (.cv y)) (syn_wbr (.cv x) (syn_c2nd) (.cv z)))
        (.objEq y z))
      y z p0013
  have p0015 :=
    @g_mpgbir (syn_wfun (syn_c2nd))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_c2nd) (.cv y))
              (syn_wbr (.cv x) (syn_c2nd) (.cv z))) (.objEq y z))))
      x p0000 p0014
  have p0016 := @g_eqv x (syn_cdm (syn_c2nd)) dv_cache_0015
  have p0017 := @g_opeq (.cv x)
  have p0018 := @g_eqid (syn_cproj2 (.cv x))
  have p0019 := @g_vex x
  have p0020 := @g_proj1ex (.cv x) p0019
  have p0021 := @g_proj2ex (.cv x) p0019
  have p0022 :=
    @g_opbr2nd (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)) (syn_cproj2 (.cv x)) p0020 p0021
  have p0023 :=
    @g_mpbir
      (syn_wbr (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_c2nd)
        (syn_cproj2 (.cv x)))
      (.classEq (syn_cproj2 (.cv x)) (syn_cproj2 (.cv x))) p0018 p0022
  have p0024 :=
    @g_breldm (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cproj2 (.cv x))
      (syn_c2nd)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_cdm (syn_c2nd)) p0017 p0025
  have p0027 :=
    @g_mpgbir (.classEq (syn_cdm (syn_c2nd)) (syn_cvv))
      (.classMem (.cv x) (syn_cdm (syn_c2nd))) x p0016 p0026
  have p0028 := (Nominal.biimpRefl (syn_wfn (syn_c2nd) (syn_cvv)))
  have p0029 :=
    @g_mpbir2an (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfun (syn_c2nd))
      (.classEq (syn_cdm (syn_c2nd)) (syn_cvv)) p0015 p0027 p0028
  have p0030 := @g_eqv x (syn_crn (syn_c2nd)) dv_cache_0016
  have p0031 := @g_equid x
  have p0032 := @g_opbr2nd (.cv x) (.cv x) (.cv x) p0019 p0019
  have p0033_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv x)) (syn_c2nd) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c2nd syn_copab
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
    @g_mpbir (syn_wbr (syn_cop (.cv x) (.cv x)) (syn_c2nd) (.cv x)) (.objEq x x) p0031
      p0033_e01_recanon
  have p0034 := @g_brelrn (syn_cop (.cv x) (.cv x)) (.cv x) (syn_c2nd)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_mpgbir (.classEq (syn_crn (syn_c2nd)) (syn_cvv))
      (.classMem (.cv x) (syn_crn (syn_c2nd))) x p0030 p0035
  have p0037 := (Nominal.biimpRefl (syn_wfo (syn_c2nd) (syn_cvv) (syn_cvv)))
  have p0038 :=
    @g_mpbir2an (syn_wfo (syn_c2nd) (syn_cvv) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv))
      (.classEq (syn_crn (syn_c2nd)) (syn_cvv)) p0029 p0036 p0037
  exact p0038

@[expose]
noncomputable def g_dfdm4 (A : Class) :
    Nominal.NPrf (.classEq (syn_cdm A) (syn_cima (syn_c1st) A)) :=
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
  have dv_cache_0005 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_cdm A)).fv :=
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
  have dv_cache_0010 : x ∉ ((syn_cima (syn_c1st) A)).fv :=
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
    @g_rexcom4 (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) z y A dv_cache_0001
      dv_cache_0002
  have p0001 := @g_vex x
  have p0002 := @g_br1st y (.cv z) (.cv x) dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @g_rexbii (syn_wbr (.cv z) (syn_c1st) (.cv x))
      (syn_wex y (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) z A p0002
  have p0004 := @g_risset z (syn_cop (.cv x) (.cv y)) A dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_exbii (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) y p0004
  have p0006 :=
    @g_n_3bitr4ri (syn_wrex z A (syn_wex y (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))))
      (syn_wex y (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))))
      (syn_wrex z A (syn_wbr (.cv z) (syn_c1st) (.cv x)))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) p0000 p0003 p0005
  have p0007 := @g_eldm2 y (.cv x) A dv_cache_0004 dv_cache_0001
  have p0008 := @g_elima z (.cv x) (syn_c1st) A dv_cache_0007 dv_cache_0008 dv_cache_0006
  have p0009 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A))
      (syn_wrex z A (syn_wbr (.cv z) (syn_c1st) (.cv x))) (.classMem (.cv x) (syn_cdm A))
      (.classMem (.cv x) (syn_cima (syn_c1st) A)) p0006 p0007 p0008
  have p0010 :=
    @g_eqriv x (syn_cdm A) (syn_cima (syn_c1st) A) dv_cache_0009 dv_cache_0010 p0009
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

@[expose]
noncomputable def g_dfrn5 (A : Class) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_cima (syn_c2nd) A)) :=
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
  have dv_cache_0005 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_crn A)).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_cima (syn_c2nd) A)).fv :=
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
    @g_rexcom4 (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) z x A dv_cache_0001
      dv_cache_0002
  have p0001 := @g_vex y
  have p0002 := @g_br2nd x (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @g_rexbii (syn_wbr (.cv z) (syn_c2nd) (.cv y))
      (syn_wex x (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) z A p0002
  have p0004 := @g_risset z (syn_cop (.cv x) (.cv y)) A dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_exbii (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) x p0004
  have p0006 :=
    @g_n_3bitr4ri (syn_wrex z A (syn_wex x (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))))
      (syn_wex x (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))))
      (syn_wrex z A (syn_wbr (.cv z) (syn_c2nd) (.cv y)))
      (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) p0000 p0003 p0005
  have p0007 := @g_elrn2 x (.cv y) A dv_cache_0004 dv_cache_0001
  have p0008 := @g_elima z (.cv y) (syn_c2nd) A dv_cache_0007 dv_cache_0008 dv_cache_0006
  have p0009 :=
    @g_n_3bitr4i (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A))
      (syn_wrex z A (syn_wbr (.cv z) (syn_c2nd) (.cv y))) (.classMem (.cv y) (syn_crn A))
      (.classMem (.cv y) (syn_cima (syn_c2nd) A)) p0006 p0007 p0008
  have p0010 :=
    @g_eqriv y (syn_crn A) (syn_cima (syn_c2nd) A) dv_cache_0009 dv_cache_0010 p0009
  exact p0010

@[expose]
noncomputable def g_brswap (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cswap) B) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (.classEq B (syn_cop (.cv y) (.cv x))))))) :=
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
    x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
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
    y ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv :=
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
      ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (.classEq B (syn_cop (.cv y) (.cv x))))))).fv :=
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
      ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (.classEq B (syn_cop (.cv y) (.cv x))))))).fv :=
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
  have p0000 := @g_brex A B (syn_cswap)
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_opex (.cv x) (.cv y) p0001 p0002
  have p0004 := @g_eleq1 A (syn_cop (.cv x) (.cv y)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cvv)) p0003 p0004
  have p0006 := @g_opex (.cv y) (.cv x) p0002 p0001
  have p0007 := @g_eleq1 B (syn_cop (.cv y) (.cv x)) (syn_cvv)
  have p0008 :=
    @g_mpbiri (.classEq B (syn_cop (.cv y) (.cv x))) (.classMem B (syn_cvv))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_anim12i (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (.classEq B (syn_cop (.cv y) (.cv x))) (.classMem B (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_exlimivv
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) x y dv_cache_0001
      dv_cache_0002 p0009
  have p0011 := @g_eqeq1 (.cv a) A (syn_cop (.cv x) (.cv y))
  have p0012 :=
    @g_anbi1d (.classEq (.cv a) A) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
      (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
      p0011
  have p0013 :=
    @g_n_2exbidv (.classEq (.cv a) A)
      (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))
      x y dv_cache_0003 dv_cache_0004 p0012
  have p0014 := @g_eqeq1 (.cv b) B (syn_cop (.cv y) (.cv x))
  have p0015 :=
    @g_anbi2d (.classEq (.cv b) B) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
      (.classEq B (syn_cop (.cv y) (.cv x))) (.classEq A (syn_cop (.cv x) (.cv y))) p0014
  have p0016 :=
    @g_n_2exbidv (.classEq (.cv b) B)
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x))))
      x y dv_cache_0005 dv_cache_0006 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_swap a b x y
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @g_brabg
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
            (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv y) (.cv x))))))
      a b A B (syn_cvv) (syn_cvv) (syn_cswap) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0010 p0013 p0016 p0017
  have p0019 :=
    @g_pm5_21nii (syn_wbr A (syn_cswap) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv y) (.cv x))))))
      p0000 p0010 p0018
  exact p0019

@[expose]
noncomputable def g_cnvswap :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cswap)) (syn_cswap)) :=
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
  have dv_cache_0007 : a ∉ ((syn_ccnv (syn_cswap))).fv :=
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
  have dv_cache_0008 : b ∉ ((syn_ccnv (syn_cswap))).fv :=
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
  have dv_cache_0009 : a ∉ ((syn_cswap)).fv :=
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
  have dv_cache_0010 : b ∉ ((syn_cswap)).fv :=
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
    @g_ancom (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
      (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
  have p0001 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
        (.classEq (.cv a) (syn_cop (.cv x) (.cv y))))
      (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))
      x y p0000
  have p0002 := @g_brcnv (.cv a) (.cv b) (syn_cswap)
  have p0003 :=
    @g_brswap y x (.cv b) (.cv a) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0004 :=
    @g_excom
      (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
        (.classEq (.cv a) (syn_cop (.cv x) (.cv y))))
      y x
  have p0005 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_ccnv (syn_cswap)) (.cv b))
      (syn_wbr (.cv b) (syn_cswap) (.cv a))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
            (.classEq (.cv a) (syn_cop (.cv x) (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
            (.classEq (.cv a) (syn_cop (.cv x) (.cv y))))))
      p0002 p0003 p0004
  have p0006 :=
    @g_brswap x y (.cv a) (.cv b) dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0001
      dv_cache_0006
  have p0007 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))
            (.classEq (.cv a) (syn_cop (.cv x) (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
            (.classEq (.cv b) (syn_cop (.cv y) (.cv x))))))
      (syn_wbr (.cv a) (syn_ccnv (syn_cswap)) (.cv b))
      (syn_wbr (.cv a) (syn_cswap) (.cv b)) p0001 p0005 p0006
  have p0008 :=
    @g_eqbrriv a b (syn_ccnv (syn_cswap)) (syn_cswap) dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007
  exact p0008

@[expose]
noncomputable def g_swapf1o : Nominal.NPrf (syn_wf1o (syn_cswap) (syn_cvv) (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_cswap)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cswap)).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_cswap)).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_cdm (syn_cswap))).fv :=
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
    @g_dffun2 x y z (syn_cswap) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_opeq (.cv y)
  have p0002 :=
    @g_breq2i (.cv y) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (.cv x)
      (syn_cswap) p0001
  have p0003 := @g_vex y
  have p0004 := @g_proj1ex (.cv y) p0003
  have p0005 := @g_proj2ex (.cv y) p0003
  have p0006 := @g_brswap2 (.cv x) (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)) p0004 p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_cswap) (.cv y))
      (syn_wbr (.cv x) (syn_cswap) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))))
      (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))) p0002 p0006
  have p0008 := @g_opeq (.cv z)
  have p0009 :=
    @g_breq2i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) (.cv x)
      (syn_cswap) p0008
  have p0010 := @g_vex z
  have p0011 := @g_proj1ex (.cv z) p0010
  have p0012 := @g_proj2ex (.cv z) p0010
  have p0013 := @g_brswap2 (.cv x) (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)) p0011 p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_cswap) (.cv z))
      (syn_wbr (.cv x) (syn_cswap) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))))
      (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) p0009 p0013
  have p0015 :=
    @g_eqtr2 (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))
      (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))
  have p0016 :=
    @g_ancom (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z)))
      (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z)))
  have p0017 :=
    @g_opth (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)) (syn_cproj2 (.cv z))
      (syn_cproj1 (.cv z))
  have p0018 :=
    @g_eqeq12i (.cv y) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (.cv z)
      (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) p0001 p0008
  have p0019 :=
    @g_opth (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)) (syn_cproj1 (.cv z))
      (syn_cproj2 (.cv z))
  have p0020_e00_recanon :
    Nominal.NPrf
      (syn_wb (.objEq y z) (.classEq (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)))
          (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_cproj1 syn_cproj2
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
    @g_bitri (.objEq y z)
      (.classEq (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)))
        (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))))
      (syn_wa (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z)))
        (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z))))
      p0020_e00_recanon p0019
  have p0021 :=
    @g_n_3bitr4i
      (syn_wa (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z)))
        (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z))))
      (syn_wa (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z)))
        (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z))))
      (.classEq (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))
        (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))))
      (.objEq y z) p0016 p0017 p0020
  have p0022 :=
    @g_sylib
      (syn_wa (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y))))
        (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))))
      (.classEq (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))
        (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))))
      (.objEq y z) p0015 p0021
  have p0023 :=
    @g_syl2anb (syn_wbr (.cv x) (syn_cswap) (.cv y))
      (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y))))
      (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) (.objEq y z)
      (syn_wbr (.cv x) (syn_cswap) (.cv z)) p0007 p0014 p0022
  have p0024 :=
    @g_gen2
      (.imp (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (.cv z)))
        (.objEq y z))
      y z p0023
  have p0025 :=
    @g_mpgbir (syn_wfun (syn_cswap))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv y))
              (syn_wbr (.cv x) (syn_cswap) (.cv z))) (.objEq y z))))
      x p0000 p0024
  have p0026 := @g_eqv x (syn_cdm (syn_cswap)) dv_cache_0007
  have p0027 := @g_opeq (.cv x)
  have p0028 := @g_eqid (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
  have p0029 := @g_vex x
  have p0030 := @g_proj2ex (.cv x) p0029
  have p0031 := @g_proj1ex (.cv x) p0029
  have p0032 :=
    @g_brswap2 (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cproj2 (.cv x))
      (syn_cproj1 (.cv x)) p0030 p0031
  have p0033 :=
    @g_mpbir
      (syn_wbr (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cswap)
        (syn_cop (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x))))
      (.classEq (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
        (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))))
      p0028 p0032
  have p0034 :=
    @g_breldm (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_cop (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x))) (syn_cswap)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_cdm (syn_cswap)) p0027 p0035
  have p0037 :=
    @g_mpgbir (.classEq (syn_cdm (syn_cswap)) (syn_cvv))
      (.classMem (.cv x) (syn_cdm (syn_cswap))) x p0026 p0036
  have p0038 := (Nominal.biimpRefl (syn_wfn (syn_cswap) (syn_cvv)))
  have p0039 :=
    @g_mpbir2an (syn_wfn (syn_cswap) (syn_cvv)) (syn_wfun (syn_cswap))
      (.classEq (syn_cdm (syn_cswap)) (syn_cvv)) p0025 p0037 p0038
  have p0040 := @g_cnvswap
  have p0041 := @g_fneq1i (syn_cvv) (syn_ccnv (syn_cswap)) (syn_cswap) p0040
  have p0042 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cswap)) (syn_cvv)) (syn_wfn (syn_cswap) (syn_cvv))
      p0039 p0041
  have p0043 := @g_dff1o4 (syn_cvv) (syn_cvv) (syn_cswap)
  have p0044 :=
    @g_mpbir2an (syn_wf1o (syn_cswap) (syn_cvv) (syn_cvv)) (syn_wfn (syn_cswap) (syn_cvv))
      (syn_wfn (syn_ccnv (syn_cswap)) (syn_cvv)) p0039 p0042 p0043
  exact p0044

@[expose]
noncomputable def g_swapres (A : Class) :
    Nominal.NPrf (syn_wf1o (syn_cres (syn_cswap) A) A (syn_ccnv A)) :=
  by
  have p0000 := @g_swapf1o
  have p0001 := @g_f1of1 (syn_cvv) (syn_cvv) (syn_cswap)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_ssv A
  have p0004 := @g_f1ores (syn_cvv) (syn_cvv) A (syn_cswap)
  have p0005 :=
    @g_mp2an (syn_wf1 (syn_cswap) (syn_cvv) (syn_cvv)) (syn_wss A (syn_cvv))
      (syn_wf1o (syn_cres (syn_cswap) A) A (syn_cima (syn_cswap) A)) p0002 p0003 p0004
  have p0006 := @g_dfcnv2 A
  have p0007 := @g_f1oeq3 (syn_ccnv A) (syn_cima (syn_cswap) A) A (syn_cres (syn_cswap) A)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbir (syn_wf1o (syn_cres (syn_cswap) A) A (syn_ccnv A))
      (syn_wf1o (syn_cres (syn_cswap) A) A (syn_cima (syn_cswap) A)) p0005 p0008
  exact p0009

@[expose]
noncomputable def g_xpnedisj (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpnedisj_1 : Nominal.NPrf (.classMem C (syn_cvv)))
    (hyp_xpnedisj_2 : Nominal.NPrf (syn_wne C D)) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D))) (syn_c0)) :=
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
  have dv_cache_0001 : x ∉ ((syn_cxp A (syn_csn C))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cxp B (syn_csn D))).fv :=
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
  have dv_cache_0007 : y ∉ ((syn_csn C)).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_csn C)).fv :=
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
  have dv_cache_0011 : z ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) C))).fv :=
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
  have dv_cache_0012 : y ∉ ((Wff.neg (.classMem (.cv x) (syn_cxp B (syn_csn D))))).fv :=
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
    @g_disj x (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elxp2 y z (.cv x) A (syn_csn C) dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 := @g_opeq2 (.cv z) C (.cv y)
  have p0003 :=
    @g_eqeq2d (.classEq (.cv z) C) (syn_cop (.cv y) (.cv z)) (syn_cop (.cv y) C) (.cv x)
      p0002
  have p0004 :=
    @g_rexsn (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (.classEq (.cv x) (syn_cop (.cv y) C)) z C dv_cache_0010 dv_cache_0011
      hyp_xpnedisj_1 p0003
  have p0005 :=
    @g_rexbii (syn_wrex z (syn_csn C) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))
      (.classEq (.cv x) (syn_cop (.cv y) C)) y A p0004
  have p0006 :=
    @g_bitri (.classMem (.cv x) (syn_cxp A (syn_csn C)))
      (syn_wrex y A (syn_wrex z (syn_csn C) (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))
      (syn_wrex y A (.classEq (.cv x) (syn_cop (.cv y) C))) p0001 p0005
  have p0007 := (Nominal.biimpRefl (syn_wne C D))
  have p0008 := @g_mpbi (syn_wne C D) (.neg (.classEq C D)) hyp_xpnedisj_2 p0007
  have p0009 := @g_elsni C D
  have p0010 := @g_mto (.classMem C (syn_csn D)) (.classEq C D) p0008 p0009
  have p0011 := @g_intnan (.classMem C (syn_csn D)) (.classMem (.cv y) B) p0010
  have p0012 := @g_eleq1 (.cv x) (syn_cop (.cv y) C) (syn_cxp B (syn_csn D))
  have p0013 := @g_opelxp (.cv y) C B (syn_csn D)
  have p0014 :=
    @g_syl6bb (.classEq (.cv x) (syn_cop (.cv y) C))
      (.classMem (.cv x) (syn_cxp B (syn_csn D)))
      (.classMem (syn_cop (.cv y) C) (syn_cxp B (syn_csn D)))
      (syn_wa (.classMem (.cv y) B) (.classMem C (syn_csn D))) p0012 p0013
  have p0015 :=
    @g_mtbiri (.classEq (.cv x) (syn_cop (.cv y) C))
      (.classMem (.cv x) (syn_cxp B (syn_csn D)))
      (syn_wa (.classMem (.cv y) B) (.classMem C (syn_csn D))) p0011 p0014
  have p0016 :=
    @g_rexlimivw (.classEq (.cv x) (syn_cop (.cv y) C))
      (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) y A dv_cache_0012 p0015
  have p0017 :=
    @g_sylbi (.classMem (.cv x) (syn_cxp A (syn_csn C)))
      (syn_wrex y A (.classEq (.cv x) (syn_cop (.cv y) C)))
      (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) p0006 p0016
  have p0018 :=
    @g_mprgbir
      (.classEq (syn_cin (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D))) (syn_c0))
      (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) x (syn_cxp A (syn_csn C)) p0000
      p0017
  exact p0018

@[expose]
noncomputable def g_opfv1st (A : Class) (B : Class)
    (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_opbr1st A B A hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 := @g_mpbir (syn_wbr (syn_cop A B) (syn_c1st) A) (.classEq A A) p0000 p0001
  have p0003 := @g_n_1stfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_opex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 := @g_fnbrfvb (syn_cvv) (syn_cop A B) A (syn_c1st)
  have p0008 :=
    @g_mp2an (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A)
        (syn_wbr (syn_cop A B) (syn_c1st) A))
      p0005 p0006 p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A)
      (syn_wbr (syn_cop A B) (syn_c1st) A) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_opfv2nd (A : Class) (B : Class)
    (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B) :=
  by
  have p0000 := @g_eqid B
  have p0001 := @g_opbr2nd A B B hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 := @g_mpbir (syn_wbr (syn_cop A B) (syn_c2nd) B) (.classEq B B) p0000 p0001
  have p0003 := @g_n_2ndfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_opex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 := @g_fnbrfvb (syn_cvv) (syn_cop A B) B (syn_c2nd)
  have p0008 :=
    @g_mp2an (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B)
        (syn_wbr (syn_cop A B) (syn_c2nd) B))
      p0005 p0006 p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B)
      (syn_wbr (syn_cop A B) (syn_c2nd) B) p0002 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
