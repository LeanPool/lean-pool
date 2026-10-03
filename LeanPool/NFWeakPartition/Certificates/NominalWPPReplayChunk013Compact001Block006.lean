/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frd (ph : Wff) (y : Var) (z : Var) (A : Class) (R : Class) (V : Class)
    (X : Class) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_X_y : y ∉ X.fv)
    (dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z)
    (hyp_frd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cfound) A)))
    (hyp_frd_2 : Nominal.NPrf (.imp ph (.classMem X V)))
    (hyp_frd_3 : Nominal.NPrf (.imp ph (syn_wss X A)))
    (hyp_frd_4 : Nominal.NPrf (.imp ph (syn_wne X (syn_c0)))) :
    Nominal.NPrf
      (.imp ph (syn_wrex y X (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_a_ne_z : a ≠ z := by
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
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, dv_R_y, or_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, dv_R_z, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0006 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0007 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0008 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0010 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have dv_cache_0015 : r ∉ (R).fv :=
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
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0016 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0017 : r ∉ (A).fv :=
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0018 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0019 :
    r ∉
      ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex y (.cv x) (syn_wral z (.cv x)
                (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_A,
          fresh_r_ne_z, fresh_r_ne_y, fresh_r_not_R, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex y (.cv x) (syn_wral z (.cv x)
                (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_A,
          fresh_a_ne_z, fresh_a_ne_y, fresh_a_not_R, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0021 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0022 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0023 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_z, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((Class.cv x)).fv :=
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
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0025 : y ∉ (X).fv :=
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
        simp only [dv_X_y, not_false_eq_true])
  have dv_cache_0026 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0027 :
    x ∉
      ((Wff.imp (syn_wa (syn_wss X A) (syn_wne X (syn_c0))) (syn_wrex y X
            (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_not_A,
          fresh_x_ne_z, fresh_x_ne_y, fresh_x_not_R, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_brex R A (syn_cfound)
  have p0001 := @g_breq (.cv z) (.cv y) (.cv r) R
  have p0002 :=
    @g_imbi1d (.classEq (.cv r) R) (syn_wbr (.cv z) (.cv r) (.cv y))
      (syn_wbr (.cv z) R (.cv y)) (.objEq z y) p0001
  have p0003 :=
    @g_rexralbidv (.classEq (.cv r) R)
      (.imp (syn_wbr (.cv z) (.cv r) (.cv y)) (.objEq z y))
      (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) y z (.cv x) (.cv x) dv_cache_0001
      dv_cache_0002 p0002
  have p0004 :=
    @g_imbi2d (.classEq (.cv r) R)
      (syn_wrex y (.cv x)
        (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (.cv r) (.cv y)) (.objEq z y))))
      (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0003
  have p0005 :=
    @g_albidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (.cv r) (.cv y)) (.objEq z y)))))
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      x dv_cache_0003 p0004
  have p0006 := @g_sseq2 (.cv a) A (.cv x)
  have p0007 :=
    @g_anbi1d (.classEq (.cv a) A) (syn_wss (.cv x) (.cv a)) (syn_wss (.cv x) A)
      (syn_wne (.cv x) (syn_c0)) p0006
  have p0008 :=
    @g_imbi1d (.classEq (.cv a) A)
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0)))
      (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      p0007
  have p0009 :=
    @g_albidv (.classEq (.cv a) A)
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      x dv_cache_0004 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found x z y r a
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0011 :=
    @g_brabg
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (.cv r) (.cv y)) (.objEq z y))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))
      r a R A (syn_cvv) (syn_cvv) (syn_cfound) dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0009 p0010
  have p0012 :=
    @g_syl (syn_wbr R (syn_cfound) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_cfound) A) (.all x
          (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
              (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))))
      p0000 p0011
  have p0013 :=
    @g_ibi (syn_wbr R (syn_cfound) A)
      (.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))
      p0012
  have p0014 :=
    @g_syl ph (syn_wbr R (syn_cfound) A)
      (.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))
      hyp_frd_1 p0013
  have p0015 := @g_sseq1 (.cv x) X A
  have p0016 := @g_neeq1 (.cv x) X (syn_c0)
  have p0017 :=
    @g_anbi12d (.classEq (.cv x) X) (syn_wss (.cv x) A) (syn_wss X A)
      (syn_wne (.cv x) (syn_c0)) (syn_wne X (syn_c0)) p0015 p0016
  have p0018 :=
    @g_raleq (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) z (.cv x) X dv_cache_0022
      dv_cache_0023
  have p0019 :=
    @g_rexeqbi1dv (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) y (.cv x) X
      dv_cache_0024 dv_cache_0025 p0018
  have p0020 :=
    @g_imbi12d (.classEq (.cv x) X)
      (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wss X A) (syn_wne X (syn_c0)))
      (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (syn_wrex y X (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))) p0017
      p0019
  have p0021 :=
    @g_spcgv
      (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
          (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      (.imp (syn_wa (syn_wss X A) (syn_wne X (syn_c0)))
        (syn_wrex y X (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      x X V dv_cache_0026 dv_cache_0027 p0020
  have p0022 :=
    @g_sylc ph (.classMem X V)
      (.all x (.imp (syn_wa (syn_wss (.cv x) A) (syn_wne (.cv x) (syn_c0))) (syn_wrex y (.cv x)
            (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))))
      (.imp (syn_wa (syn_wss X A) (syn_wne X (syn_c0)))
        (syn_wrex y X (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))))
      hyp_frd_2 p0014 p0021
  have p0023 :=
    @g_mp2and ph (syn_wss X A) (syn_wne X (syn_c0))
      (syn_wrex y X (syn_wral z X (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      hyp_frd_3 hyp_frd_4 p0022
  exact p0023

@[expose]
noncomputable def g_symd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_symd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_csym) A)))
    (hyp_symd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_symd_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_symd_4 : Nominal.NPrf (.imp ph (syn_wbr X R Y))) :
    Nominal.NPrf (.imp ph (syn_wbr Y R X)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
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
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_Y : y ∉ Y.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_R, or_false, not_false_eq_true])
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
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0008 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0009 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0014 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv :=
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
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0017 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0020 : x ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0021 : y ∉ (X).fv :=
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
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0022 : y ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_Y, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Wff.imp (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_y, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0024 : y ∉ ((Wff.imp (syn_wbr X R Y) (syn_wbr Y R X))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_X, fresh_y_not_Y, fresh_y_not_R, or_false, not_false_eq_true])
  have p0000 := @g_jca ph (.classMem X A) (.classMem Y A) hyp_symd_2 hyp_symd_3
  have p0001 := @g_brex R A (syn_csym)
  have p0002 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0003 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @g_imbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @g_raleq (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sym x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      r a R A (syn_cvv) (syn_cvv) (syn_csym) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0005 p0007 p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_csym) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_csym) A) (syn_wral x A
          (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))))
      p0001 p0009
  have p0011 :=
    @g_ibi (syn_wbr R (syn_csym) A)
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      p0010
  have p0012 :=
    @g_syl ph (syn_wbr R (syn_csym) A)
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      hyp_symd_1 p0011
  have p0013 := @g_breq1 (.cv x) X (.cv y) R
  have p0014 := @g_breq2 (.cv x) X (.cv y) R
  have p0015 :=
    @g_imbi12d (.classEq (.cv x) X) (syn_wbr (.cv x) R (.cv y)) (syn_wbr X R (.cv y))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R X) p0013 p0014
  have p0016 := @g_breq2 (.cv y) Y X R
  have p0017 := @g_breq1 (.cv y) Y X R
  have p0018 :=
    @g_imbi12d (.classEq (.cv y) Y) (syn_wbr X R (.cv y)) (syn_wbr X R Y)
      (syn_wbr (.cv y) R X) (syn_wbr Y R X) p0016 p0017
  have p0019 :=
    @g_rspc2v (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (.imp (syn_wbr X R Y) (syn_wbr Y R X))
      (.imp (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X)) x y X Y A A dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006 dv_cache_0004 dv_cache_0023
      dv_cache_0024 dv_cache_0012 p0015 p0018
  have p0020 :=
    @g_syl3c ph (syn_wa (.classMem X A) (.classMem Y A))
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wbr X R Y) (syn_wbr Y R X) p0000 p0012 hyp_symd_4 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_trrd (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_trrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_trrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_trrd_3 : Nominal.NPrf (.imp (syn_w3a ph
            (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
          (syn_wbr (.cv x) R (.cv z)))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_ctrans) A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪
          R.fv ∪
        V.fv ∪
      W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
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
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, (Ne.symm dv_y_z), or_false,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, dv_R_z, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, dv_R_y, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0011 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv a)).fv :=
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
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0014 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0015 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0016 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0017 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0018 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0019 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0020 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0021 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0022 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0023 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0024 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0025 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0026 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0027 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0028 :
    r ∉
      ((syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          fresh_r_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0029 :
    a ∉
      ((syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          fresh_a_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    (Nominal.biimpRefl
      (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)))
  have p0001 :=
    @g_n_3exp ph
      (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv x) R (.cv z)) hyp_trrd_3
  have p0002 :=
    @g_syl5bir
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.classMem (.cv z) A))
      (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)) ph
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      p0000 p0001
  have p0003 :=
    @g_exp3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.classMem (.cv z) A)
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      p0002
  have p0004 :=
    @g_ralrimdv ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      z A dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @g_ralrimivv ph
      (syn_wral z A (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      x y A A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0004
  have p0006 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0007 := @g_breq (.cv y) (.cv z) (.cv r) R
  have p0008 :=
    @g_anbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))
      (syn_wbr (.cv y) R (.cv z)) p0006 p0007
  have p0009 := @g_breq (.cv x) (.cv z) (.cv r) R
  have p0010 :=
    @g_imbi12d (.classEq (.cv r) R)
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) R (.cv z)) p0008 p0009
  have p0011 :=
    @g_ralbidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
        (syn_wbr (.cv x) (.cv r) (.cv z)))
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      z (.cv a) dv_cache_0007 p0010
  have p0012 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (syn_wral z (.cv a)
        (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (syn_wbr (.cv x) (.cv r) (.cv z))))
      (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      x y (.cv a) (.cv a) dv_cache_0008 dv_cache_0009 p0011
  have p0013 :=
    @g_raleq
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      z (.cv a) A dv_cache_0010 dv_cache_0011
  have p0014 :=
    @g_raleqbi1dv
      (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      (syn_wral z A (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      y (.cv a) A dv_cache_0012 dv_cache_0003 p0013
  have p0015 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (syn_wral z (.cv a)
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
            (syn_wbr (.cv x) R (.cv z)))))
      (syn_wral y A (syn_wral z A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
            (syn_wbr (.cv x) R (.cv z)))))
      x (.cv a) A dv_cache_0013 dv_cache_0014 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x y z r a
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0006 dv_cache_0022 dv_cache_0023
  have p0017 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a)
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      r a R A V W (syn_ctrans) dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 p0012 p0015 p0016
  have p0018 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W)
      (syn_wb (syn_wbr R (syn_ctrans) A) (syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z)))))))
      hyp_trrd_1 hyp_trrd_2 p0017
  have p0019 :=
    @g_mpbird ph (syn_wbr R (syn_ctrans) A)
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      p0005 p0018
  exact p0019

@[expose]
noncomputable def g_refrd (ph : Wff) (x : Var) (A : Class) (R : Class) (V : Class)
    (W : Class) (dv_A_x : x ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_refrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_refrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_refrd_3 :
      Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wbr (.cv x) R (.cv x)))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cref) A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
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
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0006 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0007 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0008 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0009 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0010 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0011 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((syn_wral x A (syn_wbr (.cv x) R (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_not_R, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((syn_wral x A (syn_wbr (.cv x) R (.cv x)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_not_R, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0014 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 := @g_ralrimiva ph (syn_wbr (.cv x) R (.cv x)) x A dv_cache_0001 hyp_refrd_3
  have p0001 := @g_breq (.cv x) (.cv x) (.cv r) R
  have p0002 :=
    @g_ralbidv (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv x))
      (syn_wbr (.cv x) R (.cv x)) x (.cv a) dv_cache_0002 p0001
  have p0003 :=
    @g_raleq (syn_wbr (.cv x) R (.cv x)) x (.cv a) A dv_cache_0003 dv_cache_0004
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref x r a
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_brabg (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x)))
      (syn_wral x (.cv a) (syn_wbr (.cv x) R (.cv x)))
      (syn_wral x A (syn_wbr (.cv x) R (.cv x))) r a R A V W (syn_cref) dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      p0002 p0003 p0004
  have p0006 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W)
      (syn_wb (syn_wbr R (syn_cref) A) (syn_wral x A (syn_wbr (.cv x) R (.cv x))))
      hyp_refrd_1 hyp_refrd_2 p0005
  have p0007 :=
    @g_mpbird ph (syn_wbr R (syn_cref) A) (syn_wral x A (syn_wbr (.cv x) R (.cv x))) p0000
      p0006
  exact p0007

@[expose]
noncomputable def g_refd (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_refd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cref) A)))
    (hyp_refd_2 : Nominal.NPrf (.imp ph (.classMem X A))) :
    Nominal.NPrf (.imp ph (syn_wbr X R X)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
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
  have dv_cache_0004 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0005 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0006 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ x from (by exact fresh_r_ne_x))
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
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0008 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0009 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0010 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((syn_wral x A (syn_wbr (.cv x) R (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_not_R, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_wral x A (syn_wbr (.cv x) R (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_not_R, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0013 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0014 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_wbr X R X)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @g_brex R A (syn_cref)
  have p0001 := @g_breq (.cv x) (.cv x) (.cv r) R
  have p0002 :=
    @g_ralbidv (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv x))
      (syn_wbr (.cv x) R (.cv x)) x (.cv a) dv_cache_0001 p0001
  have p0003 :=
    @g_raleq (syn_wbr (.cv x) R (.cv x)) x (.cv a) A dv_cache_0002 dv_cache_0003
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref x r a
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_brabg (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x)))
      (syn_wral x (.cv a) (syn_wbr (.cv x) R (.cv x)))
      (syn_wral x A (syn_wbr (.cv x) R (.cv x))) r a R A (syn_cvv) (syn_cvv) (syn_cref)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0002 p0003 p0004
  have p0006 :=
    @g_syl (syn_wbr R (syn_cref) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_cref) A) (syn_wral x A (syn_wbr (.cv x) R (.cv x)))) p0000
      p0005
  have p0007 :=
    @g_ibi (syn_wbr R (syn_cref) A) (syn_wral x A (syn_wbr (.cv x) R (.cv x))) p0006
  have p0008 :=
    @g_syl ph (syn_wbr R (syn_cref) A) (syn_wral x A (syn_wbr (.cv x) R (.cv x)))
      hyp_refd_1 p0007
  have p0009 := @g_id (.classEq (.cv x) X)
  have p0010 := @g_breq12d (.classEq (.cv x) X) (.cv x) X (.cv x) X R p0009 p0009
  have p0011 :=
    @g_rspccv (syn_wbr (.cv x) R (.cv x)) (syn_wbr X R X) x X A dv_cache_0014
      dv_cache_0003 dv_cache_0015 p0010
  have p0012 :=
    @g_sylc ph (syn_wral x A (syn_wbr (.cv x) R (.cv x))) (.classMem X A) (syn_wbr X R X)
      p0008 hyp_refd_2 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_antird (ph : Wff) (x : Var) (y : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_antird_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_antird_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_antird_3 : Nominal.NPrf (.imp
          (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cantisym) A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
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
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
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
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, dv_R_y, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0010 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0015 : r ∉ (R).fv :=
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
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0016 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0017 : r ∉ (A).fv :=
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0018 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0019 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x,
          fresh_r_ne_y, fresh_r_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x,
          fresh_a_ne_y, fresh_a_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0021 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    @g_n_3expia ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y)
      hyp_antird_3
  have p0001 :=
    @g_ralrimivva ph
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      x y A A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0003 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @g_anbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @g_imbi1d (.classEq (.cv r) R)
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y) p0004
  have p0006 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
        (.objEq x y))
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      x y (.cv a) (.cv a) dv_cache_0005 dv_cache_0006 p0005
  have p0007 :=
    @g_raleq
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      y (.cv a) A dv_cache_0007 dv_cache_0001
  have p0008 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
          (.objEq x y)))
      (syn_wral y A (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
          (.objEq x y)))
      x (.cv a) A dv_cache_0008 dv_cache_0009 p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0010 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      r a R A V W (syn_cantisym) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0006 p0008 p0009
  have p0011 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W)
      (syn_wb (syn_wbr R (syn_cantisym) A) (syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y)))))
      hyp_antird_1 hyp_antird_2 p0010
  have p0012 :=
    @g_mpbird ph (syn_wbr R (syn_cantisym) A)
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      p0001 p0011
  exact p0012

@[expose]
noncomputable def g_antid (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_antid_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cantisym) A)))
    (hyp_antid_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_antid_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_antid_4 : Nominal.NPrf (.imp ph (syn_wbr X R Y)))
    (hyp_antid_5 : Nominal.NPrf (.imp ph (syn_wbr Y R X))) :
    Nominal.NPrf (.imp ph (.classEq X Y)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
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
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_Y : y ∉ Y.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_R, or_false, not_false_eq_true])
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
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0008 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0009 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0014 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv :=
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
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0017 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x,
          fresh_r_ne_y, fresh_r_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x,
          fresh_a_ne_y, fresh_a_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0020 : x ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0021 : y ∉ (X).fv :=
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
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0022 : y ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_Y, not_false_eq_true])
  have dv_cache_0023 :
    x ∉
      ((Wff.imp (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X))
          (.classEq X (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_y, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0024 :
    y ∉ ((Wff.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq X Y))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, fresh_y_not_X,
          fresh_y_not_Y, fresh_y_not_R, or_false, not_false_eq_true])
  have p0000 := @g_brex R A (syn_cantisym)
  have p0001 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0002 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0003 :=
    @g_anbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0001 p0002
  have p0004 :=
    @g_imbi1d (.classEq (.cv r) R)
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y) p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
        (.objEq x y))
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      x y (.cv a) (.cv a) dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @g_raleq
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      y (.cv a) A dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
          (.objEq x y)))
      (syn_wral y A (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
          (.objEq x y)))
      x (.cv a) A dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      r a R A (syn_cvv) (syn_cvv) (syn_cantisym) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0005 p0007 p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_cantisym) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_cantisym) A) (syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y)))))
      p0000 p0009
  have p0011 :=
    @g_ibi (syn_wbr R (syn_cantisym) A)
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      p0010
  have p0012 :=
    @g_syl ph (syn_wbr R (syn_cantisym) A)
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      hyp_antid_1 p0011
  have p0013 := @g_breq1 (.cv x) X (.cv y) R
  have p0014 := @g_breq2 (.cv x) X (.cv y) R
  have p0015 :=
    @g_anbi12d (.classEq (.cv x) X) (syn_wbr (.cv x) R (.cv y)) (syn_wbr X R (.cv y))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R X) p0013 p0014
  have p0016 := @g_eqeq1 (.cv x) X (.cv y)
  have p0017_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) X) (syn_wb (.objEq x y) (.classEq X (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0016
  have p0017 :=
    @g_imbi12d (.classEq (.cv x) X)
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X)) (.objEq x y)
      (.classEq X (.cv y)) p0015 p0017_e01_recanon
  have p0018 := @g_breq2 (.cv y) Y X R
  have p0019 := @g_breq1 (.cv y) Y X R
  have p0020 :=
    @g_anbi12d (.classEq (.cv y) Y) (syn_wbr X R (.cv y)) (syn_wbr X R Y)
      (syn_wbr (.cv y) R X) (syn_wbr Y R X) p0018 p0019
  have p0021 := @g_eqeq2 (.cv y) Y X
  have p0022 :=
    @g_imbi12d (.classEq (.cv y) Y) (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq X (.cv y)) (.classEq X Y) p0020
      p0021
  have p0023 :=
    @g_rspc2v
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))
      (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq X Y))
      (.imp (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X)) (.classEq X (.cv y))) x y
      X Y A A dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006
      dv_cache_0004 dv_cache_0023 dv_cache_0024 dv_cache_0012 p0017 p0022
  have p0024 :=
    @g_syl2anc ph (.classMem X A) (.classMem Y A)
      (.imp (syn_wral x A (syn_wral y A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
              (.objEq x y)))) (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq X Y)))
      hyp_antid_2 hyp_antid_3 p0023
  have p0025 :=
    @g_mpd ph
      (syn_wral x A (syn_wral y A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (.objEq x y))))
      (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq X Y)) p0012 p0024
  have p0026 :=
    @g_mp2and ph (syn_wbr X R Y) (syn_wbr Y R X) (.classEq X Y) hyp_antid_4 hyp_antid_5
      p0025
  exact p0026

@[expose]
noncomputable def g_connexrd (ph : Wff) (x : Var) (y : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_connexrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_connexrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_connexrd_3 : Nominal.NPrf
        (.imp (syn_w3a ph (.classMem (.cv x) A) (.classMem (.cv y) A))
          (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cconnex) A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
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
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
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
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, dv_R_y, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0010 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0015 : r ∉ (R).fv :=
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
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0016 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0017 : r ∉ (A).fv :=
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0018 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0019 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0021 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    @g_n_3expib ph (.classMem (.cv x) A) (.classMem (.cv y) A)
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) hyp_connexrd_3
  have p0001 :=
    @g_ralrimivv ph (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y A
      A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0003 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @g_orbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0005 dv_cache_0006 p0004
  have p0006 :=
    @g_raleq (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0007 dv_cache_0001
  have p0007 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0008 dv_cache_0009 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0009 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wral x A
        (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      r a R A V W (syn_cconnex) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0007 p0008
  have p0010 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W)
      (syn_wb (syn_wbr R (syn_cconnex) A) (syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))))
      hyp_connexrd_1 hyp_connexrd_2 p0009
  have p0011 :=
    @g_mpbird ph (syn_wbr R (syn_cconnex) A)
      (syn_wral x A
        (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      p0001 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_connexd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_connexd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cconnex) A)))
    (hyp_connexd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_connexd_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (syn_wo (syn_wbr X R Y) (syn_wbr Y R X))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
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
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_Y : y ∉ Y.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_R, or_false, not_false_eq_true])
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
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0008 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0009 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0014 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv :=
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
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0017 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0020 : x ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0021 : y ∉ (X).fv :=
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
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0022 : y ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_Y, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wo (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_y, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_wo (syn_wbr X R Y) (syn_wbr Y R X))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_X, fresh_y_not_Y, fresh_y_not_R, or_false, not_false_eq_true])
  have p0000 := @g_brex R A (syn_cconnex)
  have p0001 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0002 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0003 :=
    @g_orbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0001 p0002
  have p0004 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @g_raleq (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0005 dv_cache_0006 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0008 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wral x A
        (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      r a R A (syn_cvv) (syn_cvv) (syn_cconnex) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0004 p0006 p0007
  have p0009 :=
    @g_syl (syn_wbr R (syn_cconnex) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_cconnex) A) (syn_wral x A (syn_wral y A
            (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))))
      p0000 p0008
  have p0010 :=
    @g_ibi (syn_wbr R (syn_cconnex) A)
      (syn_wral x A
        (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      p0009
  have p0011 := @g_breq1 (.cv x) X (.cv y) R
  have p0012 := @g_breq2 (.cv x) X (.cv y) R
  have p0013 :=
    @g_orbi12d (.classEq (.cv x) X) (syn_wbr (.cv x) R (.cv y)) (syn_wbr X R (.cv y))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R X) p0011 p0012
  have p0014 := @g_breq2 (.cv y) Y X R
  have p0015 := @g_breq1 (.cv y) Y X R
  have p0016 :=
    @g_orbi12d (.classEq (.cv y) Y) (syn_wbr X R (.cv y)) (syn_wbr X R Y)
      (syn_wbr (.cv y) R X) (syn_wbr Y R X) p0014 p0015
  have p0017 :=
    @g_rspc2v (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wo (syn_wbr X R Y) (syn_wbr Y R X))
      (syn_wo (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X)) x y X Y A A dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006 dv_cache_0004 dv_cache_0023
      dv_cache_0024 dv_cache_0012 p0013 p0016
  have p0018 :=
    @g_syl2anc ph (.classMem X A) (.classMem Y A)
      (.imp (syn_wral x A
          (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
        (syn_wo (syn_wbr X R Y) (syn_wbr Y R X)))
      hyp_connexd_2 hyp_connexd_3 p0017
  have p0019 :=
    @g_syl5 (syn_wbr R (syn_cconnex) A)
      (syn_wral x A
        (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      ph (syn_wo (syn_wbr X R Y) (syn_wbr Y R X)) p0010 p0018
  have p0020 :=
    @g_mpd ph (syn_wbr R (syn_cconnex) A) (syn_wo (syn_wbr X R Y) (syn_wbr Y R X))
      hyp_connexd_1 p0019
  exact p0020

@[expose]
noncomputable def g_ersymtr (A : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr R (syn_cer) A)
        (syn_wa (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cer))
  have p0001 := @g_breqi R A (syn_cer) (syn_cin (syn_csym) (syn_ctrans)) p0000
  have p0002 := @g_brin R A (syn_csym) (syn_ctrans)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cer) A) (syn_wbr R (syn_cin (syn_csym) (syn_ctrans)) A)
      (syn_wa (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_porta (A : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr R (syn_cpartial) A)
        (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
          (syn_wbr R (syn_cantisym) A))) :=
  by
  have p0000 := @g_brin R A (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)
  have p0001 := @g_brin R A (syn_cref) (syn_ctrans)
  have p0002 :=
    @g_anbi1i (syn_wbr R (syn_cin (syn_cref) (syn_ctrans)) A)
      (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
      (syn_wbr R (syn_cantisym) A) p0001
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)) A)
      (syn_wa (syn_wbr R (syn_cin (syn_cref) (syn_ctrans)) A) (syn_wbr R (syn_cantisym) A))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
        (syn_wbr R (syn_cantisym) A))
      p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_cpartial))
  have p0005 :=
    @g_breqi R A (syn_cpartial) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym))
      p0004
  have p0006 :=
    (Nominal.biimpRefl (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
        (syn_wbr R (syn_cantisym) A)))
  have p0007 :=
    @g_n_3bitr4i (syn_wbr R (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)) A)
      (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
        (syn_wbr R (syn_cantisym) A))
      (syn_wbr R (syn_cpartial) A)
      (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A))
      p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_sopc (A : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr R (syn_cstrict) A)
        (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cstrict))
  have p0001 := @g_breqi R A (syn_cstrict) (syn_cin (syn_cpartial) (syn_cconnex)) p0000
  have p0002 := @g_brin R A (syn_cpartial) (syn_cconnex)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cin (syn_cpartial) (syn_cconnex)) A)
      (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_frds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_frds_1 : Nominal.NPrf (.classMem (.cab x ps) (syn_cvv)))
    (hyp_frds_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ps ch)))
    (hyp_frds_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ps th)))
    (hyp_frds_4 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cfound) A)))
    (hyp_frds_5 : Nominal.NPrf (.imp ph (syn_wrex x A ps))) :
    Nominal.NPrf
      (.imp ph (syn_wrex y A (syn_wa ch (syn_wral z A
              (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cab x (syn_wa (.classMem (.cv x) A) ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, dv_ps_y, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cab x (syn_wa (.classMem (.cv x) A) ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, dv_ps_z, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : x ∉ ((syn_wa (.classMem (.cv y) A) ch)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_A_x, dv_ch_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0009 : x ∉ ((syn_wa (.classMem (.cv z) A) th)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_z, dv_A_x, dv_th_x, or_false, not_false_eq_true])
  have dv_cache_0010 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show z ≠ x from (by exact Ne.symm dv_x_z))
  have p0000 := @g_dfrab2 ps x A dv_cache_0001
  have p0001 := (Nominal.classEqRefl (syn_crab x A ps))
  have p0002 :=
    @g_eqtr3i (syn_crab x A ps) (syn_cin (.cab x ps) A)
      (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 := @g_brex R A (syn_cfound)
  have p0004 :=
    @g_syl ph (syn_wbr R (syn_cfound) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) hyp_frds_4 p0003
  have p0005 := @g_simprd ph (.classMem R (syn_cvv)) (.classMem A (syn_cvv)) p0004
  have p0006 := @g_inexg (.cab x ps) A (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancr ph (.classMem (.cab x ps) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem (syn_cin (.cab x ps) A) (syn_cvv)) hyp_frds_1 p0005 p0006
  have p0008 :=
    @g_syl5eqelr ph (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_cin (.cab x ps) A)
      (syn_cvv) p0002 p0007
  have p0009 := @g_ssab2 ps x A dv_cache_0001
  have p0010 := @g_a1i (syn_wss (.cab x (syn_wa (.classMem (.cv x) A) ps)) A) ph p0009
  have p0011 := (Nominal.biimpRefl (syn_wrex x A ps))
  have p0012 :=
    @g_sylib ph (syn_wrex x A ps) (syn_wex x (syn_wa (.classMem (.cv x) A) ps)) hyp_frds_5
      p0011
  have p0013 := @g_abn0 (syn_wa (.classMem (.cv x) A) ps) x
  have p0014 :=
    @g_sylibr ph (syn_wex x (syn_wa (.classMem (.cv x) A) ps))
      (syn_wne (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_c0)) p0012 p0013
  have p0015 :=
    @g_frd ph y z A R (syn_cvv) (.cab x (syn_wa (.classMem (.cv x) A) ps)) dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_frds_4 p0008 p0010 p0014
  have p0016 := @g_eleq1 (.cv x) (.cv y) A
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_anbi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A) ps ch
      p0017_e00_recanon hyp_frds_2
  have p0018 :=
    @g_rexab (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv y) A) ch)
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) y x
      dv_cache_0007 dv_cache_0008 p0017
  have p0019 :=
    @g_anass (.classMem (.cv y) A) ch
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))
  have p0020 :=
    @g_exbii
      (syn_wa (syn_wa (.classMem (.cv y) A) ch)
        (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
      (syn_wa (.classMem (.cv y) A) (syn_wa ch
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
      y p0019
  have p0021 :=
    @g_bitri
      (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
      (syn_wex y (syn_wa (syn_wa (.classMem (.cv y) A) ch)
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wa ch
            (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))))
      p0018 p0020
  have p0022 :=
    @g_impexp (.classMem (.cv z) A) th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
  have p0023 := @g_impexp th (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0024 :=
    @g_imbi2i (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (.classMem (.cv z) A)
      p0023
  have p0025 :=
    @g_bitr4i
      (.imp (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (.imp (.classMem (.cv z) A) (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (.imp (.classMem (.cv z) A) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))
      p0022 p0024
  have p0026 :=
    @g_albii
      (.imp (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (.imp (.classMem (.cv z) A) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))
      z p0025
  have p0027 := @g_eleq1 (.cv x) (.cv z) A
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (syn_wb (.classMem (.cv x) A) (.classMem (.cv z) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0028 :=
    @g_anbi12d (.objEq x z) (.classMem (.cv x) A) (.classMem (.cv z) A) ps th
      p0028_e00_recanon hyp_frds_3
  have p0029 :=
    @g_ralab (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv z) A) th)
      (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) z x dv_cache_0009 dv_cache_0010
      p0028
  have p0030 :=
    (Nominal.biimpRefl
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
  have p0031 :=
    @g_n_3bitr4i
      (.all z (.imp (syn_wa (.classMem (.cv z) A) th)
          (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (.all z (.imp (.classMem (.cv z) A)
          (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
      (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) p0026
      p0029 p0030
  have p0032 :=
    @g_rexbii
      (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) y
      (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0031
  have p0033 :=
    (Nominal.biimpRefl (syn_wrex y A (syn_wa ch
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))))
  have p0034 :=
    @g_n_3bitr4i
      (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wa ch
            (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))))
      (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps))
          (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (syn_wrex y A (syn_wa ch
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
      p0021 p0032 p0033
  have p0035 :=
    @g_sylib ph
      (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps))
          (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))
      (syn_wrex y A (syn_wa ch
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
      p0015 p0034
  exact p0035

@[expose]
noncomputable def g_pod (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_pod_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_pod_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_pod_3 :
      Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wbr (.cv x) R (.cv x))))
    (hyp_pod_4 : Nominal.NPrf (.imp (syn_w3a ph
            (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
          (syn_wbr (.cv x) R (.cv z))))
    (hyp_pod_5 : Nominal.NPrf (.imp
          (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cpartial) A)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_refrd ph x A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_pod_1 hyp_pod_2
      hyp_pod_3
  have p0001 :=
    @g_trrd ph x y z A R V W dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_pod_1 hyp_pod_2 hyp_pod_4
  have p0002 :=
    @g_antird ph x y A R V W dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006
      dv_cache_0003 dv_cache_0008 dv_cache_0010 hyp_pod_1 hyp_pod_2 hyp_pod_5
  have p0003 := @g_porta A R
  have p0004 :=
    @g_syl3anbrc ph (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
      (syn_wbr R (syn_cantisym) A) (syn_wbr R (syn_cpartial) A) p0000 p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sod (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_sod_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_sod_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_sod_3 :
      Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wbr (.cv x) R (.cv x))))
    (hyp_sod_4 : Nominal.NPrf (.imp (syn_w3a ph
            (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
          (syn_wbr (.cv x) R (.cv z))))
    (hyp_sod_5 : Nominal.NPrf (.imp
          (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y)))
    (hyp_sod_6 : Nominal.NPrf (.imp (syn_w3a ph (.classMem (.cv x) A) (.classMem (.cv y) A))
          (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cstrict) A)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
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
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_pod ph x y z A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_sod_1 hyp_sod_2 hyp_sod_3 hyp_sod_4 hyp_sod_5
  have p0001 :=
    @g_connexrd ph x y A R V W dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0005
      dv_cache_0007 dv_cache_0008 dv_cache_0010 hyp_sod_1 hyp_sod_2 hyp_sod_6
  have p0002 := @g_sopc A R
  have p0003 :=
    @g_sylanbrc ph (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A)
      (syn_wbr R (syn_cstrict) A) p0000 p0001 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_weds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_weds_1 : Nominal.NPrf (.classMem (.cab x ps) (syn_cvv)))
    (hyp_weds_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ps ch)))
    (hyp_weds_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ps th)))
    (hyp_weds_4 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cwe) A)))
    (hyp_weds_5 : Nominal.NPrf (.imp ph (syn_wrex x A ps))) :
    Nominal.NPrf
      (.imp ph (syn_wrex y A
          (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z))))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0006 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_z, not_false_eq_true])
  have dv_cache_0009 : x ∉ (th).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_th_x, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : z ∉ ((syn_wa ph (.classMem (.cv y) A))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_ph_z, (Ne.symm dv_y_z), dv_A_z, or_false,
          not_false_eq_true])
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
        simp only [dv_ph_y, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simprbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_syl ph (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cfound) A) hyp_weds_4 p0004
  have p0006 :=
    @g_frds ph ps ch th x y z A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_weds_1 hyp_weds_2 hyp_weds_3 p0005 hyp_weds_5
  have p0007 := @g_impexp th (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0008 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0009 :=
    @g_syl ph (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) hyp_weds_4 p0008
  have p0010 := @g_sopc A R
  have p0011 :=
    @g_simprbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cconnex) A) p0010
  have p0012 :=
    @g_syl ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cconnex) A) p0009 p0011
  have p0013 :=
    @g_adantr ph (syn_wbr R (syn_cconnex) A)
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)) p0012
  have p0014 := @g_simprl ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0015 := @g_simprr ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0016 :=
    @g_connexd (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) A R
      (.cv y) (.cv z) p0013 p0014 p0015
  have p0017 :=
    @g_ax1 (syn_wbr (.cv y) R (.cv z)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
  have p0018 :=
    @g_a1i
      (.imp (syn_wbr (.cv y) R (.cv z)) (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
          (syn_wbr (.cv y) R (.cv z))))
      (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) p0017
  have p0019 := @g_pm2_27 (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0020 := @g_porta A R
  have p0021 :=
    @g_simp1bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A)
      (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0020
  have p0022 :=
    @g_adantr (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A)
      (syn_wbr R (syn_cconnex) A) p0021
  have p0023 :=
    @g_sylbi (syn_wbr R (syn_cstrict) A)
      (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A))
      (syn_wbr R (syn_cref) A) p0010 p0022
  have p0024 := @g_syl ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cref) A) p0009 p0023
  have p0025 := @g_adantr ph (syn_wbr R (syn_cref) A) (.classMem (.cv z) A) p0024
  have p0026 := @g_simpr ph (.classMem (.cv z) A)
  have p0027 := @g_refd (syn_wa ph (.classMem (.cv z) A)) A R (.cv z) p0025 p0026
  have p0028 :=
    @g_adantrl ph (.classMem (.cv z) A) (syn_wbr (.cv z) R (.cv z)) (.classMem (.cv y) A)
      p0027
  have p0029 := @g_breq1 (.cv z) (.cv y) (.cv z) R
  have p0030_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (syn_wb (syn_wbr (.cv z) R (.cv z)) (syn_wbr (.cv y) R (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @g_syl5ibcom (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (syn_wbr (.cv z) R (.cv z)) (.objEq z y) (syn_wbr (.cv y) R (.cv z)) p0028
      p0030_e01_recanon
  have p0031 :=
    @g_syl9r (syn_wbr (.cv z) R (.cv y)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
      (.objEq z y) (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (syn_wbr (.cv y) R (.cv z)) p0019 p0030
  have p0032 :=
    @g_jaod (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (syn_wbr (.cv y) R (.cv z))
      (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv z) R (.cv y)) p0018 p0031
  have p0033 :=
    @g_mpd (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (syn_wo (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv z) R (.cv y)))
      (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z)))
      p0016 p0032
  have p0034 :=
    @g_imim2d (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z)) th p0033
  have p0035 :=
    @g_syl5bi (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))
      (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (.imp th (syn_wbr (.cv y) R (.cv z))) p0007 p0034
  have p0036 :=
    @g_anassrs ph (.classMem (.cv y) A) (.classMem (.cv z) A)
      (.imp (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))
        (.imp th (syn_wbr (.cv y) R (.cv z))))
      p0035
  have p0037 :=
    @g_ralimdva (syn_wa ph (.classMem (.cv y) A))
      (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (syn_wbr (.cv y) R (.cv z))) z A dv_cache_0013 p0036
  have p0038 :=
    @g_anim2d (syn_wa ph (.classMem (.cv y) A))
      (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))
      (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z)))) ch p0037
  have p0039 :=
    @g_reximdva ph
      (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))
      (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z))))) y A dv_cache_0014
      p0038
  have p0040 :=
    @g_mpd ph
      (syn_wrex y A (syn_wa ch
          (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
      (syn_wrex y A (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z))))))
      p0006 p0039
  exact p0040

@[expose]
noncomputable def g_iserd (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_iserd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_iserd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_iserd_3 : Nominal.NPrf (.imp
          (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv y) R (.cv x))))
    (hyp_iserd_4 : Nominal.NPrf (.imp (syn_w3a ph
            (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
          (syn_wbr (.cv x) R (.cv z)))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪
          R.fv ∪
        V.fv ∪
      W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
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
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
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
          Finset.mem_singleton, fresh_y_ne_r, dv_R_y, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0010 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0015 : r ∉ (R).fv :=
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
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0016 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0017 : r ∉ (A).fv :=
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0018 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0019 :
    r ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((syn_wral x A (syn_wral y A
            (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0021 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0022 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0023 : x ∉ (R).fv :=
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
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0024 : y ∉ (R).fv :=
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
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0025 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0026 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0027 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0028 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_n_3expia ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)) hyp_iserd_3
  have p0001 :=
    @g_ralrimivva ph (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y A
      A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0003 := @g_breq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @g_imbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0005 dv_cache_0006 p0004
  have p0006 :=
    @g_raleq (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0007 dv_cache_0001
  have p0007 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0008 dv_cache_0009 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sym x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0009 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      r a R A V W (syn_csym) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0007 p0008
  have p0010 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W)
      (syn_wb (syn_wbr R (syn_csym) A) (syn_wral x A
          (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))))
      hyp_iserd_1 hyp_iserd_2 p0009
  have p0011 :=
    @g_mpbird ph (syn_wbr R (syn_csym) A)
      (syn_wral x A
        (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))
      p0001 p0010
  have p0012 :=
    @g_trrd ph x y z A R V W dv_cache_0009 dv_cache_0001 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0002 dv_cache_0003 dv_cache_0026 dv_cache_0004
      dv_cache_0027 dv_cache_0028 hyp_iserd_1 hyp_iserd_2 hyp_iserd_4
  have p0013 := @g_ersymtr A R
  have p0014 :=
    @g_sylanbrc ph (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)
      (syn_wbr R (syn_cer) A) p0011 p0012 p0013
  exact p0014

@[expose]
noncomputable def g_dfec2 (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv)
    (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (syn_cec A R) (.cab y (syn_wbr A R (.cv y)))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cec A R))
  have p0001 := @g_imasn y A R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_eqtri (syn_cec A R) (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y))) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ecexg (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem R B) (.classMem (syn_cec A R) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cec A R))
  have p0001 := @g_snex A
  have p0002 := @g_imaexg R (syn_csn A) B (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem R B) (.classMem (syn_csn A) (syn_cvv))
      (.classMem (syn_cima R (syn_csn A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem R B) (syn_cec A R) (syn_cima R (syn_csn A)) (syn_cvv) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_ecexr (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cec B R)) (.classMem B (syn_cvv))) :=
  by
  have p0000 := @g_n0i (syn_cima R (syn_csn B)) A
  have p0001 := @g_snprc B
  have p0002 := @g_imaeq2 (syn_csn B) (syn_c0) R
  have p0003 :=
    @g_sylbi (.neg (.classMem B (syn_cvv))) (.classEq (syn_csn B) (syn_c0))
      (.classEq (syn_cima R (syn_csn B)) (syn_cima R (syn_c0))) p0001 p0002
  have p0004 := @g_ima0 R
  have p0005 :=
    @g_syl6eq (.neg (.classMem B (syn_cvv))) (syn_cima R (syn_csn B))
      (syn_cima R (syn_c0)) (syn_c0) p0003 p0004
  have p0006 :=
    @g_nsyl2 (.classMem A (syn_cima R (syn_csn B)))
      (.classEq (syn_cima R (syn_csn B)) (syn_c0)) (.classMem B (syn_cvv)) p0000 p0005
  have p0007 := (Nominal.classEqRefl (syn_cec B R))
  have p0008 :=
    @g_eleq2s (.classMem B (syn_cvv)) A (syn_cima R (syn_csn B)) (syn_cec B R) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_ersym (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_ersym_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ersym_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ersym_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ersym_4 : Nominal.NPrf (.imp ph (syn_wbr X R Y))) :
    Nominal.NPrf (.imp ph (syn_wbr Y R X)) :=
  by
  have p0000 := @g_ersymtr A R
  have p0001 :=
    @g_simplbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)
      p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) hyp_ersym_1 p0001
  have p0003 := @g_symd ph A R X Y p0002 hyp_ersym_2 hyp_ersym_3 hyp_ersym_4
  exact p0003

@[expose]
noncomputable def g_ersymb (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_ersymb_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ersymb_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ersymb_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr X R Y) (syn_wbr Y R X))) :=
  by
  have p0000 := @g_adantr ph (syn_wbr R (syn_cer) A) (syn_wbr X R Y) hyp_ersymb_1
  have p0001 := @g_adantr ph (.classMem X A) (syn_wbr X R Y) hyp_ersymb_2
  have p0002 := @g_adantr ph (.classMem Y A) (syn_wbr X R Y) hyp_ersymb_3
  have p0003 := @g_simpr ph (syn_wbr X R Y)
  have p0004 := @g_ersym (syn_wa ph (syn_wbr X R Y)) A R X Y p0000 p0001 p0002 p0003
  have p0005 := @g_adantr ph (syn_wbr R (syn_cer) A) (syn_wbr Y R X) hyp_ersymb_1
  have p0006 := @g_adantr ph (.classMem Y A) (syn_wbr Y R X) hyp_ersymb_3
  have p0007 := @g_adantr ph (.classMem X A) (syn_wbr Y R X) hyp_ersymb_2
  have p0008 := @g_simpr ph (syn_wbr Y R X)
  have p0009 := @g_ersym (syn_wa ph (syn_wbr Y R X)) A R Y X p0005 p0006 p0007 p0008
  have p0010 := @g_impbida ph (syn_wbr X R Y) (syn_wbr Y R X) p0004 p0009
  exact p0010

@[expose]
noncomputable def g_ertr (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) :
    Nominal.NPrf
      (.imp ph (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z))) :=
  by
  have p0000 := @g_ersymtr A R
  have p0001 :=
    @g_simprbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)
      p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_ctrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @g_adantr ph (syn_wbr R (syn_ctrans) A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) p0002
  have p0004 :=
    @g_adantr ph (.classMem X A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_2
  have p0005 :=
    @g_adantr ph (.classMem Y A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_3
  have p0006 :=
    @g_adantr ph (.classMem Z A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_4
  have p0007 := @g_simprl ph (syn_wbr X R Y) (syn_wbr Y R Z)
  have p0008 := @g_simprr ph (syn_wbr X R Y) (syn_wbr Y R Z)
  have p0009 :=
    @g_trd (syn_wa ph (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z))) A R X Y Z p0003 p0004
      p0005 p0006 p0007 p0008
  have p0010 := @g_ex ph (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z) p0009
  exact p0010

@[expose]
noncomputable def g_ertrd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertrd_5 : Nominal.NPrf (.imp ph (syn_wbr X R Y)))
    (hyp_ertrd_6 : Nominal.NPrf (.imp ph (syn_wbr Y R Z))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) :=
  by
  have p0000 := @g_ersymtr A R
  have p0001 :=
    @g_simprbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)
      p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_ctrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @g_trd ph A R X Y Z p0002 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertrd_5 hyp_ertrd_6
  exact p0003

@[expose]
noncomputable def g_ertr3d (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertr3d_5 : Nominal.NPrf (.imp ph (syn_wbr Y R X)))
    (hyp_ertr3d_6 : Nominal.NPrf (.imp ph (syn_wbr Y R Z))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) :=
  by
  have p0000 := @g_ersym ph A R Y X hyp_ertr_1 hyp_ertr_3 hyp_ertr_2 hyp_ertr3d_5
  have p0001 :=
    @g_ertrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 p0000 hyp_ertr3d_6
  exact p0001

@[expose]
noncomputable def g_ertr4d (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertr4d_5 : Nominal.NPrf (.imp ph (syn_wbr X R Y)))
    (hyp_ertr4d_6 : Nominal.NPrf (.imp ph (syn_wbr Z R Y))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) :=
  by
  have p0000 := @g_ersym ph A R Z Y hyp_ertr_1 hyp_ertr_4 hyp_ertr_3 hyp_ertr4d_6
  have p0001 :=
    @g_ertrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertr4d_5 p0000
  exact p0001

@[expose]
noncomputable def g_erref (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_erref_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv))))
    (hyp_erref_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) A)))
    (hyp_erref_3 : Nominal.NPrf (.imp ph (.classMem X A))) :
    Nominal.NPrf (.imp ph (syn_wbr X R X)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (X).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_X, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ ((syn_wbr X R X)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have p0000 := @g_eleq2d ph (syn_cdm R) A X hyp_erref_2
  have p0001 := @g_eldm y X R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv)) (syn_wbr X R (.cv y)) hyp_erref_1
  have p0003 := @g_elex X A
  have p0004 := @g_syl ph (.classMem X A) (.classMem X (syn_cvv)) hyp_erref_3 p0003
  have p0005 := @g_adantr ph (.classMem X (syn_cvv)) (syn_wbr X R (.cv y)) p0004
  have p0006 := @g_vex y
  have p0007 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) (syn_wa ph (syn_wbr X R (.cv y))) p0006
  have p0008 := @g_simpr ph (syn_wbr X R (.cv y))
  have p0009 :=
    @g_ertr4d (syn_wa ph (syn_wbr X R (.cv y))) (syn_cvv) R X (.cv y) X p0002 p0005 p0007
      p0005 p0008 p0008
  have p0010 := @g_ex ph (syn_wbr X R (.cv y)) (syn_wbr X R X) p0009
  have p0011 :=
    @g_exlimdv ph (syn_wbr X R (.cv y)) (syn_wbr X R X) y dv_cache_0003 dv_cache_0004
      p0010
  have p0012 :=
    @g_syl5bi (.classMem X (syn_cdm R)) (syn_wex y (syn_wbr X R (.cv y))) ph
      (syn_wbr X R X) p0001 p0011
  have p0013 :=
    @g_sylbird ph (.classMem X A) (.classMem X (syn_cdm R)) (syn_wbr X R X) p0000 p0012
  have p0014 := @g_mpd ph (.classMem X A) (syn_wbr X R X) hyp_erref_3 p0013
  exact p0014

@[expose]
noncomputable def g_eceq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cec A C) (syn_cec B C))) :=
  by
  have p0000 := @g_sneq A B
  have p0001 := @g_imaeq2d (.classEq A B) (syn_csn A) (syn_csn B) C p0000
  have p0002 := (Nominal.classEqRefl (syn_cec A C))
  have p0003 := (Nominal.classEqRefl (syn_cec B C))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima C (syn_csn A)) (syn_cima C (syn_csn B))
      (syn_cec A C) (syn_cec B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_eceq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cec C A) (syn_cec C B))) :=
  by
  have p0000 := @g_imaeq1 A B (syn_csn C)
  have p0001 := (Nominal.classEqRefl (syn_cec C A))
  have p0002 := (Nominal.classEqRefl (syn_cec C B))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima A (syn_csn C)) (syn_cima B (syn_csn C))
      (syn_cec C A) (syn_cec C B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_elec (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cec B R)) (syn_wbr B R A)) :=
  by
  have p0000 := @g_elimasn R B A
  have p0001 := (Nominal.classEqRefl (syn_cec B R))
  have p0002 := @g_eleq2i (syn_cec B R) (syn_cima R (syn_csn B)) A p0001
  have p0003 := (Nominal.biimpRefl (syn_wbr B R A))
  have p0004 :=
    @g_n_3bitr4i (.classMem A (syn_cima R (syn_csn B))) (.classMem (syn_cop B A) R)
      (.classMem A (syn_cec B R)) (syn_wbr B R A) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_erdmrn (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cdm R) (syn_crn R))) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_y_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdm R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_crn R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (syn_wbr R (syn_cer) (syn_cvv))
  have p0001 := @g_vex x
  have p0002 := @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wbr R (syn_cer) (syn_cvv)) p0001
  have p0003 := @g_vex y
  have p0004 := @g_a1i (.classMem (.cv y) (syn_cvv)) (syn_wbr R (syn_cer) (syn_cvv)) p0003
  have p0005 :=
    @g_ersymb (syn_wbr R (syn_cer) (syn_cvv)) (syn_cvv) R (.cv x) (.cv y) p0000 p0002
      p0004
  have p0006 :=
    @g_exbidv (syn_wbr R (syn_cer) (syn_cvv)) (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (.cv y) R (.cv x)) y dv_cache_0001 p0005
  have p0007 := @g_eldm y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0008 := @g_elrn y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_n_3bitr4g (syn_wbr R (syn_cer) (syn_cvv)) (syn_wex y (syn_wbr (.cv x) R (.cv y)))
      (syn_wex y (syn_wbr (.cv y) R (.cv x))) (.classMem (.cv x) (syn_cdm R))
      (.classMem (.cv x) (syn_crn R)) p0006 p0007 p0008
  have p0010 :=
    @g_eqrdv (syn_wbr R (syn_cer) (syn_cvv)) x (syn_cdm R) (syn_crn R) dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  exact p0010

@[expose]
noncomputable def g_ecss (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_ecss_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv))))
    (hyp_ecss_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_cec A R) X)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cec A R))
  have p0001 := @g_imassrn R (syn_csn A)
  have p0002 := @g_eqsstri (syn_cec A R) (syn_cima R (syn_csn A)) (syn_crn R) p0000 p0001
  have p0003 := @g_erdmrn R
  have p0004 :=
    @g_syl ph (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cdm R) (syn_crn R))
      hyp_ecss_1 p0003
  have p0005 := @g_eqtr3d ph (syn_cdm R) (syn_crn R) X p0004 hyp_ecss_2
  have p0006 := @g_syl5sseq ph (syn_crn R) (syn_cec A R) X p0002 p0005
  exact p0006

@[expose]
noncomputable def g_ecdmn0 (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdm R)) (syn_wne (syn_cec A R) (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_cec A R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, or_false, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have p0000 := @g_elec (.cv x) A R
  have p0001 := @g_exbii (.classMem (.cv x) (syn_cec A R)) (syn_wbr A R (.cv x)) x p0000
  have p0002 := @g_n0 x (syn_cec A R) dv_cache_0001
  have p0003 := @g_eldm x A R dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_n_3bitr4ri (syn_wex x (.classMem (.cv x) (syn_cec A R)))
      (syn_wex x (syn_wbr A R (.cv x))) (syn_wne (syn_cec A R) (syn_c0))
      (.classMem A (syn_cdm R)) p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
