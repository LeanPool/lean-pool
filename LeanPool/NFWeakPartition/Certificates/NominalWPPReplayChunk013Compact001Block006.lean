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

/-- Checked nominal proof certificate identified upstream as `g_frd`. -/
@[expose]
noncomputable def gFrd (ph : Wff) (y : Var) (z : Var) (A : Class) (R : Class) (V : Class)
    (X : Class) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_X_y : y ∉ X.fv)
    (dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z)
    (hyp_frd_1 : Nominal.NPrf (.imp ph (synWbr R (synCfound) A)))
    (hyp_frd_2 : Nominal.NPrf (.imp ph (.classMem X V)))
    (hyp_frd_3 : Nominal.NPrf (.imp ph (synWss X A)))
    (hyp_frd_4 : Nominal.NPrf (.imp ph (synWne X (synC0)))) :
    Nominal.NPrf
      (.imp ph (synWrex y X (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))) :=
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
      ((Wff.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0)))
            (synWrex y (.cv x) (synWral z (.cv x)
                (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))).fv :=
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
      ((Wff.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0)))
            (synWrex y (.cv x) (synWral z (.cv x)
                (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))).fv :=
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
      ((Wff.imp (synWa (synWss X A) (synWne X (synC0))) (synWrex y X
            (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))).fv :=
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
  have p0000 := @gBrex R A (synCfound)
  have p0001 := @gBreq (.cv z) (.cv y) (.cv r) R
  have p0002 :=
    @gImbi1d (.classEq (.cv r) R) (synWbr (.cv z) (.cv r) (.cv y))
      (synWbr (.cv z) R (.cv y)) (.objEq z y) p0001
  have p0003 :=
    @gRexralbidv (.classEq (.cv r) R)
      (.imp (synWbr (.cv z) (.cv r) (.cv y)) (.objEq z y))
      (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) y z (.cv x) (.cv x) dv_cache_0001
      dv_cache_0002 p0002
  have p0004 :=
    @gImbi2d (.classEq (.cv r) R)
      (synWrex y (.cv x)
        (synWral z (.cv x) (.imp (synWbr (.cv z) (.cv r) (.cv y)) (.objEq z y))))
      (synWrex y (.cv x) (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) p0003
  have p0005 :=
    @gAlbidv (.classEq (.cv r) R)
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) (.cv r) (.cv y)) (.objEq z y)))))
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      x dv_cache_0003 p0004
  have p0006 := @gSseq2 (.cv a) A (.cv x)
  have p0007 :=
    @gAnbi1d (.classEq (.cv a) A) (synWss (.cv x) (.cv a)) (synWss (.cv x) A)
      (synWne (.cv x) (synC0)) p0006
  have p0008 :=
    @gImbi1d (.classEq (.cv a) A)
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
      (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0)))
      (synWrex y (.cv x) (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      p0007
  have p0009 :=
    @gAlbidv (.classEq (.cv a) A)
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      x dv_cache_0004 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFound x z y r a
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0011 :=
    @gBrabg
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) (.cv r) (.cv y)) (.objEq z y))))))
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))
      (.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))
      r a R A (synCvv) (synCvv) (synCfound) dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0009 p0010
  have p0012 :=
    @gSyl (synWbr R (synCfound) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCfound) A) (.all x
          (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
              (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))))
      p0000 p0011
  have p0013 :=
    @gIbi (synWbr R (synCfound) A)
      (.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))
      p0012
  have p0014 :=
    @gSyl ph (synWbr R (synCfound) A)
      (.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))
      hyp_frd_1 p0013
  have p0015 := @gSseq1 (.cv x) X A
  have p0016 := @gNeeq1 (.cv x) X (synC0)
  have p0017 :=
    @gAnbi12d (.classEq (.cv x) X) (synWss (.cv x) A) (synWss X A)
      (synWne (.cv x) (synC0)) (synWne X (synC0)) p0015 p0016
  have p0018 :=
    @gRaleq (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) z (.cv x) X dv_cache_0022
      dv_cache_0023
  have p0019 :=
    @gRexeqbi1dv (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))) y (.cv x) X
      dv_cache_0024 dv_cache_0025 p0018
  have p0020 :=
    @gImbi12d (.classEq (.cv x) X)
      (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0)))
      (synWa (synWss X A) (synWne X (synC0)))
      (synWrex y (.cv x) (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (synWrex y X (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))) p0017
      p0019
  have p0021 :=
    @gSpcgv
      (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
          (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      (.imp (synWa (synWss X A) (synWne X (synC0)))
        (synWrex y X (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      x X V dv_cache_0026 dv_cache_0027 p0020
  have p0022 :=
    @gSylc ph (.classMem X V)
      (.all x (.imp (synWa (synWss (.cv x) A) (synWne (.cv x) (synC0))) (synWrex y (.cv x)
            (synWral z (.cv x) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))))
      (.imp (synWa (synWss X A) (synWne X (synC0)))
        (synWrex y X (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))))
      hyp_frd_2 p0014 p0021
  have p0023 :=
    @gMp2and ph (synWss X A) (synWne X (synC0))
      (synWrex y X (synWral z X (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      hyp_frd_3 hyp_frd_4 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_symd`. -/
@[expose]
noncomputable def gSymd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_symd_1 : Nominal.NPrf (.imp ph (synWbr R (synCsym) A)))
    (hyp_symd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_symd_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_symd_4 : Nominal.NPrf (.imp ph (synWbr X R Y))) :
    Nominal.NPrf (.imp ph (synWbr Y R X)) :=
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
      ((synWral x A (synWral y A
            (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
      ((synWral x A (synWral y A
            (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
  have dv_cache_0023 : x ∉ ((Wff.imp (synWbr X R (.cv y)) (synWbr (.cv y) R X))).fv :=
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
  have dv_cache_0024 : y ∉ ((Wff.imp (synWbr X R Y) (synWbr Y R X))).fv :=
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
  have p0000 := @gJca ph (.classMem X A) (.classMem Y A) hyp_symd_2 hyp_symd_3
  have p0001 := @gBrex R A (synCsym)
  have p0002 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0003 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @gImbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (.imp (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @gRaleq (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0003 dv_cache_0004
  have p0007 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSym x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      r a R A (synCvv) (synCvv) (synCsym) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0005 p0007 p0008
  have p0010 :=
    @gSyl (synWbr R (synCsym) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCsym) A) (synWral x A
          (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))))
      p0001 p0009
  have p0011 :=
    @gIbi (synWbr R (synCsym) A)
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      p0010
  have p0012 :=
    @gSyl ph (synWbr R (synCsym) A)
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      hyp_symd_1 p0011
  have p0013 := @gBreq1 (.cv x) X (.cv y) R
  have p0014 := @gBreq2 (.cv x) X (.cv y) R
  have p0015 :=
    @gImbi12d (.classEq (.cv x) X) (synWbr (.cv x) R (.cv y)) (synWbr X R (.cv y))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R X) p0013 p0014
  have p0016 := @gBreq2 (.cv y) Y X R
  have p0017 := @gBreq1 (.cv y) Y X R
  have p0018 :=
    @gImbi12d (.classEq (.cv y) Y) (synWbr X R (.cv y)) (synWbr X R Y)
      (synWbr (.cv y) R X) (synWbr Y R X) p0016 p0017
  have p0019 :=
    @gRspc2v (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (.imp (synWbr X R Y) (synWbr Y R X))
      (.imp (synWbr X R (.cv y)) (synWbr (.cv y) R X)) x y X Y A A dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006 dv_cache_0004 dv_cache_0023
      dv_cache_0024 dv_cache_0012 p0015 p0018
  have p0020 :=
    @gSyl3c ph (synWa (.classMem X A) (.classMem Y A))
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      (synWbr X R Y) (synWbr Y R X) p0000 p0012 hyp_symd_4 p0019
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

/-- Checked nominal proof certificate identified upstream as `g_trrd`. -/
@[expose]
noncomputable def gTrrd (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_trrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_trrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_trrd_3 : Nominal.NPrf (.imp (synW3a ph
            (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
          (synWbr (.cv x) R (.cv z)))) :
    Nominal.NPrf (.imp ph (synWbr R (synCtrans) A)) :=
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
  have dv_cache_0002 : z ∉ ((synWa (.classMem (.cv x) A) (.classMem (.cv y) A))).fv :=
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
      ((synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z))))))).fv :=
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
      ((synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z))))))).fv :=
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
      (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)))
  have p0001 :=
    @gN3exp ph
      (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv x) R (.cv z)) hyp_trrd_3
  have p0002 :=
    @gSyl5bir
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.classMem (.cv z) A))
      (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)) ph
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      p0000 p0001
  have p0003 :=
    @gExp3a ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.classMem (.cv z) A)
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      p0002
  have p0004 :=
    @gRalrimdv ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      z A dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @gRalrimivv ph
      (synWral z A (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      x y A A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0004
  have p0006 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0007 := @gBreq (.cv y) (.cv z) (.cv r) R
  have p0008 :=
    @gAnbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv z))
      (synWbr (.cv y) R (.cv z)) p0006 p0007
  have p0009 := @gBreq (.cv x) (.cv z) (.cv r) R
  have p0010 :=
    @gImbi12d (.classEq (.cv r) R)
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv x) (.cv r) (.cv z)) (synWbr (.cv x) R (.cv z)) p0008 p0009
  have p0011 :=
    @gRalbidv (.classEq (.cv r) R)
      (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
        (synWbr (.cv x) (.cv r) (.cv z)))
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      z (.cv a) dv_cache_0007 p0010
  have p0012 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (synWral z (.cv a)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (synWbr (.cv x) (.cv r) (.cv z))))
      (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      x y (.cv a) (.cv a) dv_cache_0008 dv_cache_0009 p0011
  have p0013 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      z (.cv a) A dv_cache_0010 dv_cache_0011
  have p0014 :=
    @gRaleqbi1dv
      (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      (synWral z A (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      y (.cv a) A dv_cache_0012 dv_cache_0003 p0013
  have p0015 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (synWral z (.cv a)
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
            (synWbr (.cv x) R (.cv z)))))
      (synWral y A (synWral z A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
            (synWbr (.cv x) R (.cv z)))))
      x (.cv a) A dv_cache_0013 dv_cache_0014 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans x y z r a
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0006 dv_cache_0022 dv_cache_0023
  have p0017 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a)
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      r a R A V W (synCtrans) dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 p0012 p0015 p0016
  have p0018 :=
    @gSyl2anc ph (.classMem R V) (.classMem A W)
      (synWb (synWbr R (synCtrans) A) (synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z)))))))
      hyp_trrd_1 hyp_trrd_2 p0017
  have p0019 :=
    @gMpbird ph (synWbr R (synCtrans) A)
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      p0005 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_refrd`. -/
@[expose]
noncomputable def gRefrd (ph : Wff) (x : Var) (A : Class) (R : Class) (V : Class)
    (W : Class) (dv_A_x : x ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_refrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_refrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_refrd_3 :
      Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWbr (.cv x) R (.cv x)))) :
    Nominal.NPrf (.imp ph (synWbr R (synCref) A)) :=
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
  have dv_cache_0012 : r ∉ ((synWral x A (synWbr (.cv x) R (.cv x)))).fv :=
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
  have dv_cache_0013 : a ∉ ((synWral x A (synWbr (.cv x) R (.cv x)))).fv :=
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
  have p0000 := @gRalrimiva ph (synWbr (.cv x) R (.cv x)) x A dv_cache_0001 hyp_refrd_3
  have p0001 := @gBreq (.cv x) (.cv x) (.cv r) R
  have p0002 :=
    @gRalbidv (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv x))
      (synWbr (.cv x) R (.cv x)) x (.cv a) dv_cache_0002 p0001
  have p0003 :=
    @gRaleq (synWbr (.cv x) R (.cv x)) x (.cv a) A dv_cache_0003 dv_cache_0004
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRef x r a
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @gBrabg (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x)))
      (synWral x (.cv a) (synWbr (.cv x) R (.cv x)))
      (synWral x A (synWbr (.cv x) R (.cv x))) r a R A V W (synCref) dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      p0002 p0003 p0004
  have p0006 :=
    @gSyl2anc ph (.classMem R V) (.classMem A W)
      (synWb (synWbr R (synCref) A) (synWral x A (synWbr (.cv x) R (.cv x))))
      hyp_refrd_1 hyp_refrd_2 p0005
  have p0007 :=
    @gMpbird ph (synWbr R (synCref) A) (synWral x A (synWbr (.cv x) R (.cv x))) p0000
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_refd`. -/
@[expose]
noncomputable def gRefd (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_refd_1 : Nominal.NPrf (.imp ph (synWbr R (synCref) A)))
    (hyp_refd_2 : Nominal.NPrf (.imp ph (.classMem X A))) :
    Nominal.NPrf (.imp ph (synWbr X R X)) :=
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
  have dv_cache_0011 : r ∉ ((synWral x A (synWbr (.cv x) R (.cv x)))).fv :=
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
  have dv_cache_0012 : a ∉ ((synWral x A (synWbr (.cv x) R (.cv x)))).fv :=
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
  have dv_cache_0015 : x ∉ ((synWbr X R X)).fv :=
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
  have p0000 := @gBrex R A (synCref)
  have p0001 := @gBreq (.cv x) (.cv x) (.cv r) R
  have p0002 :=
    @gRalbidv (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv x))
      (synWbr (.cv x) R (.cv x)) x (.cv a) dv_cache_0001 p0001
  have p0003 :=
    @gRaleq (synWbr (.cv x) R (.cv x)) x (.cv a) A dv_cache_0002 dv_cache_0003
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRef x r a
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0005 :=
    @gBrabg (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x)))
      (synWral x (.cv a) (synWbr (.cv x) R (.cv x)))
      (synWral x A (synWbr (.cv x) R (.cv x))) r a R A (synCvv) (synCvv) (synCref)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0002 p0003 p0004
  have p0006 :=
    @gSyl (synWbr R (synCref) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCref) A) (synWral x A (synWbr (.cv x) R (.cv x)))) p0000
      p0005
  have p0007 :=
    @gIbi (synWbr R (synCref) A) (synWral x A (synWbr (.cv x) R (.cv x))) p0006
  have p0008 :=
    @gSyl ph (synWbr R (synCref) A) (synWral x A (synWbr (.cv x) R (.cv x)))
      hyp_refd_1 p0007
  have p0009 := @gId (.classEq (.cv x) X)
  have p0010 := @gBreq12d (.classEq (.cv x) X) (.cv x) X (.cv x) X R p0009 p0009
  have p0011 :=
    @gRspccv (synWbr (.cv x) R (.cv x)) (synWbr X R X) x X A dv_cache_0014
      dv_cache_0003 dv_cache_0015 p0010
  have p0012 :=
    @gSylc ph (synWral x A (synWbr (.cv x) R (.cv x))) (.classMem X A) (synWbr X R X)
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

/-- Checked nominal proof certificate identified upstream as `g_antird`. -/
@[expose]
noncomputable def gAntird (ph : Wff) (x : Var) (y : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_antird_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_antird_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_antird_3 : Nominal.NPrf (.imp
          (synW3a ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) (.objEq x y))) :
    Nominal.NPrf (.imp ph (synWbr R (synCantisym) A)) :=
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
      ((synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
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
      ((synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
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
    @gN3expia ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y)
      hyp_antird_3
  have p0001 :=
    @gRalrimivva ph
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      x y A A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0003 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @gAnbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @gImbi1d (.classEq (.cv r) R)
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y) p0004
  have p0006 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
        (.objEq x y))
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      x y (.cv a) (.cv a) dv_cache_0005 dv_cache_0006 p0005
  have p0007 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      y (.cv a) A dv_cache_0007 dv_cache_0001
  have p0008 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
          (.objEq x y)))
      (synWral y A (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
          (.objEq x y)))
      x (.cv a) A dv_cache_0008 dv_cache_0009 p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0010 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      r a R A V W (synCantisym) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0006 p0008 p0009
  have p0011 :=
    @gSyl2anc ph (.classMem R V) (.classMem A W)
      (synWb (synWbr R (synCantisym) A) (synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
              (.objEq x y)))))
      hyp_antird_1 hyp_antird_2 p0010
  have p0012 :=
    @gMpbird ph (synWbr R (synCantisym) A)
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      p0001 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_antid`. -/
@[expose]
noncomputable def gAntid (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_antid_1 : Nominal.NPrf (.imp ph (synWbr R (synCantisym) A)))
    (hyp_antid_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_antid_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_antid_4 : Nominal.NPrf (.imp ph (synWbr X R Y)))
    (hyp_antid_5 : Nominal.NPrf (.imp ph (synWbr Y R X))) :
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
      ((synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
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
      ((synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
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
      ((Wff.imp (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R X))
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
    y ∉ ((Wff.imp (synWa (synWbr X R Y) (synWbr Y R X)) (.classEq X Y))).fv :=
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
  have p0000 := @gBrex R A (synCantisym)
  have p0001 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0002 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0003 :=
    @gAnbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0001 p0002
  have p0004 :=
    @gImbi1d (.classEq (.cv r) R)
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y) p0003
  have p0005 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
        (.objEq x y))
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      x y (.cv a) (.cv a) dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      y (.cv a) A dv_cache_0003 dv_cache_0004
  have p0007 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
          (.objEq x y)))
      (synWral y A (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
          (.objEq x y)))
      x (.cv a) A dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0009 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      r a R A (synCvv) (synCvv) (synCantisym) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0005 p0007 p0008
  have p0010 :=
    @gSyl (synWbr R (synCantisym) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCantisym) A) (synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
              (.objEq x y)))))
      p0000 p0009
  have p0011 :=
    @gIbi (synWbr R (synCantisym) A)
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      p0010
  have p0012 :=
    @gSyl ph (synWbr R (synCantisym) A)
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      hyp_antid_1 p0011
  have p0013 := @gBreq1 (.cv x) X (.cv y) R
  have p0014 := @gBreq2 (.cv x) X (.cv y) R
  have p0015 :=
    @gAnbi12d (.classEq (.cv x) X) (synWbr (.cv x) R (.cv y)) (synWbr X R (.cv y))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R X) p0013 p0014
  have p0016 := @gEqeq1 (.cv x) X (.cv y)
  have p0017_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) X) (synWb (.objEq x y) (.classEq X (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gImbi12d (.classEq (.cv x) X)
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R X)) (.objEq x y)
      (.classEq X (.cv y)) p0015 p0017_e01_recanon
  have p0018 := @gBreq2 (.cv y) Y X R
  have p0019 := @gBreq1 (.cv y) Y X R
  have p0020 :=
    @gAnbi12d (.classEq (.cv y) Y) (synWbr X R (.cv y)) (synWbr X R Y)
      (synWbr (.cv y) R X) (synWbr Y R X) p0018 p0019
  have p0021 := @gEqeq2 (.cv y) Y X
  have p0022 :=
    @gImbi12d (.classEq (.cv y) Y) (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R X))
      (synWa (synWbr X R Y) (synWbr Y R X)) (.classEq X (.cv y)) (.classEq X Y) p0020
      p0021
  have p0023 :=
    @gRspc2v
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))
      (.imp (synWa (synWbr X R Y) (synWbr Y R X)) (.classEq X Y))
      (.imp (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R X)) (.classEq X (.cv y))) x y
      X Y A A dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006
      dv_cache_0004 dv_cache_0023 dv_cache_0024 dv_cache_0012 p0017 p0022
  have p0024 :=
    @gSyl2anc ph (.classMem X A) (.classMem Y A)
      (.imp (synWral x A (synWral y A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
              (.objEq x y)))) (.imp (synWa (synWbr X R Y) (synWbr Y R X)) (.classEq X Y)))
      hyp_antid_2 hyp_antid_3 p0023
  have p0025 :=
    @gMpd ph
      (synWral x A (synWral y A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) (.objEq x y))))
      (.imp (synWa (synWbr X R Y) (synWbr Y R X)) (.classEq X Y)) p0012 p0024
  have p0026 :=
    @gMp2and ph (synWbr X R Y) (synWbr Y R X) (.classEq X Y) hyp_antid_4 hyp_antid_5
      p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_connexrd`. -/
@[expose]
noncomputable def gConnexrd (ph : Wff) (x : Var) (y : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_connexrd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_connexrd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_connexrd_3 : Nominal.NPrf
        (.imp (synW3a ph (.classMem (.cv x) A) (.classMem (.cv y) A))
          (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))) :
    Nominal.NPrf (.imp ph (synWbr R (synCconnex) A)) :=
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
      ((synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
      ((synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
    @gN3expib ph (.classMem (.cv x) A) (.classMem (.cv y) A)
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) hyp_connexrd_3
  have p0001 :=
    @gRalrimivv ph (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y A
      A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0003 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @gOrbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0005 dv_cache_0006 p0004
  have p0006 :=
    @gRaleq (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0007 dv_cache_0001
  have p0007 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0008 dv_cache_0009 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0009 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      (synWral x A
        (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      r a R A V W (synCconnex) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0007 p0008
  have p0010 :=
    @gSyl2anc ph (.classMem R V) (.classMem A W)
      (synWb (synWbr R (synCconnex) A) (synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))))
      hyp_connexrd_1 hyp_connexrd_2 p0009
  have p0011 :=
    @gMpbird ph (synWbr R (synCconnex) A)
      (synWral x A
        (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
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

/-- Checked nominal proof certificate identified upstream as `g_connexd`. -/
@[expose]
noncomputable def gConnexd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_connexd_1 : Nominal.NPrf (.imp ph (synWbr R (synCconnex) A)))
    (hyp_connexd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_connexd_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (synWo (synWbr X R Y) (synWbr Y R X))) :=
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
      ((synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
      ((synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
  have dv_cache_0023 : x ∉ ((synWo (synWbr X R (.cv y)) (synWbr (.cv y) R X))).fv :=
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
  have dv_cache_0024 : y ∉ ((synWo (synWbr X R Y) (synWbr Y R X))).fv :=
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
  have p0000 := @gBrex R A (synCconnex)
  have p0001 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0002 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0003 :=
    @gOrbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0001 p0002
  have p0004 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @gRaleq (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0005 dv_cache_0006 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex x y r a
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0008 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      (synWral x A
        (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      r a R A (synCvv) (synCvv) (synCconnex) dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0004 p0006 p0007
  have p0009 :=
    @gSyl (synWbr R (synCconnex) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCconnex) A) (synWral x A (synWral y A
            (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))))
      p0000 p0008
  have p0010 :=
    @gIbi (synWbr R (synCconnex) A)
      (synWral x A
        (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      p0009
  have p0011 := @gBreq1 (.cv x) X (.cv y) R
  have p0012 := @gBreq2 (.cv x) X (.cv y) R
  have p0013 :=
    @gOrbi12d (.classEq (.cv x) X) (synWbr (.cv x) R (.cv y)) (synWbr X R (.cv y))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R X) p0011 p0012
  have p0014 := @gBreq2 (.cv y) Y X R
  have p0015 := @gBreq1 (.cv y) Y X R
  have p0016 :=
    @gOrbi12d (.classEq (.cv y) Y) (synWbr X R (.cv y)) (synWbr X R Y)
      (synWbr (.cv y) R X) (synWbr Y R X) p0014 p0015
  have p0017 :=
    @gRspc2v (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWo (synWbr X R Y) (synWbr Y R X))
      (synWo (synWbr X R (.cv y)) (synWbr (.cv y) R X)) x y X Y A A dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006 dv_cache_0004 dv_cache_0023
      dv_cache_0024 dv_cache_0012 p0013 p0016
  have p0018 :=
    @gSyl2anc ph (.classMem X A) (.classMem Y A)
      (.imp (synWral x A
          (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
        (synWo (synWbr X R Y) (synWbr Y R X)))
      hyp_connexd_2 hyp_connexd_3 p0017
  have p0019 :=
    @gSyl5 (synWbr R (synCconnex) A)
      (synWral x A
        (synWral y A (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      ph (synWo (synWbr X R Y) (synWbr Y R X)) p0010 p0018
  have p0020 :=
    @gMpd ph (synWbr R (synCconnex) A) (synWo (synWbr X R Y) (synWbr Y R X))
      hyp_connexd_1 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_ersymtr`. -/
@[expose]
noncomputable def gErsymtr (A : Class) (R : Class) :
    Nominal.NPrf
      (synWb (synWbr R (synCer) A)
        (synWa (synWbr R (synCsym) A) (synWbr R (synCtrans) A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCer))
  have p0001 := @gBreqi R A (synCer) (synCin (synCsym) (synCtrans)) p0000
  have p0002 := @gBrin R A (synCsym) (synCtrans)
  have p0003 :=
    @gBitri (synWbr R (synCer) A) (synWbr R (synCin (synCsym) (synCtrans)) A)
      (synWa (synWbr R (synCsym) A) (synWbr R (synCtrans) A)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_porta`. -/
@[expose]
noncomputable def gPorta (A : Class) (R : Class) :
    Nominal.NPrf
      (synWb (synWbr R (synCpartial) A)
        (synW3a (synWbr R (synCref) A) (synWbr R (synCtrans) A)
          (synWbr R (synCantisym) A))) :=
  by
  have p0000 := @gBrin R A (synCin (synCref) (synCtrans)) (synCantisym)
  have p0001 := @gBrin R A (synCref) (synCtrans)
  have p0002 :=
    @gAnbi1i (synWbr R (synCin (synCref) (synCtrans)) A)
      (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
      (synWbr R (synCantisym) A) p0001
  have p0003 :=
    @gBitri (synWbr R (synCin (synCin (synCref) (synCtrans)) (synCantisym)) A)
      (synWa (synWbr R (synCin (synCref) (synCtrans)) A) (synWbr R (synCantisym) A))
      (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
        (synWbr R (synCantisym) A))
      p0000 p0002
  have p0004 := (Nominal.classEqRefl (synCpartial))
  have p0005 :=
    @gBreqi R A (synCpartial) (synCin (synCin (synCref) (synCtrans)) (synCantisym))
      p0004
  have p0006 :=
    (Nominal.biimpRefl (synW3a (synWbr R (synCref) A) (synWbr R (synCtrans) A)
        (synWbr R (synCantisym) A)))
  have p0007 :=
    @gN3bitr4i (synWbr R (synCin (synCin (synCref) (synCtrans)) (synCantisym)) A)
      (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
        (synWbr R (synCantisym) A))
      (synWbr R (synCpartial) A)
      (synW3a (synWbr R (synCref) A) (synWbr R (synCtrans) A) (synWbr R (synCantisym) A))
      p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sopc`. -/
@[expose]
noncomputable def gSopc (A : Class) (R : Class) :
    Nominal.NPrf
      (synWb (synWbr R (synCstrict) A)
        (synWa (synWbr R (synCpartial) A) (synWbr R (synCconnex) A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCstrict))
  have p0001 := @gBreqi R A (synCstrict) (synCin (synCpartial) (synCconnex)) p0000
  have p0002 := @gBrin R A (synCpartial) (synCconnex)
  have p0003 :=
    @gBitri (synWbr R (synCstrict) A)
      (synWbr R (synCin (synCpartial) (synCconnex)) A)
      (synWa (synWbr R (synCpartial) A) (synWbr R (synCconnex) A)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_frds`. -/
@[expose]
noncomputable def gFrds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_frds_1 : Nominal.NPrf (.classMem (.cab x ps) (synCvv)))
    (hyp_frds_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ps ch)))
    (hyp_frds_3 : Nominal.NPrf (.imp (.objEq x z) (synWb ps th)))
    (hyp_frds_4 : Nominal.NPrf (.imp ph (synWbr R (synCfound) A)))
    (hyp_frds_5 : Nominal.NPrf (.imp ph (synWrex x A ps))) :
    Nominal.NPrf
      (.imp ph (synWrex y A (synWa ch (synWral z A
              (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))) :=
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
  have dv_cache_0004 : y ∉ ((Class.cab x (synWa (.classMem (.cv x) A) ps))).fv :=
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
  have dv_cache_0005 : z ∉ ((Class.cab x (synWa (.classMem (.cv x) A) ps))).fv :=
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
  have dv_cache_0007 : x ∉ ((synWa (.classMem (.cv y) A) ch)).fv :=
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
  have dv_cache_0009 : x ∉ ((synWa (.classMem (.cv z) A) th)).fv :=
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
  have p0000 := @gDfrab2 ps x A dv_cache_0001
  have p0001 := (Nominal.classEqRefl (synCrab x A ps))
  have p0002 :=
    @gEqtr3i (synCrab x A ps) (synCin (.cab x ps) A)
      (.cab x (synWa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 := @gBrex R A (synCfound)
  have p0004 :=
    @gSyl ph (synWbr R (synCfound) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv))) hyp_frds_4 p0003
  have p0005 := @gSimprd ph (.classMem R (synCvv)) (.classMem A (synCvv)) p0004
  have p0006 := @gInexg (.cab x ps) A (synCvv) (synCvv)
  have p0007 :=
    @gSylancr ph (.classMem (.cab x ps) (synCvv)) (.classMem A (synCvv))
      (.classMem (synCin (.cab x ps) A) (synCvv)) hyp_frds_1 p0005 p0006
  have p0008 :=
    @gSyl5eqelr ph (.cab x (synWa (.classMem (.cv x) A) ps)) (synCin (.cab x ps) A)
      (synCvv) p0002 p0007
  have p0009 := @gSsab2 ps x A dv_cache_0001
  have p0010 := @gA1i (synWss (.cab x (synWa (.classMem (.cv x) A) ps)) A) ph p0009
  have p0011 := (Nominal.biimpRefl (synWrex x A ps))
  have p0012 :=
    @gSylib ph (synWrex x A ps) (synWex x (synWa (.classMem (.cv x) A) ps)) hyp_frds_5
      p0011
  have p0013 := @gAbn0 (synWa (.classMem (.cv x) A) ps) x
  have p0014 :=
    @gSylibr ph (synWex x (synWa (.classMem (.cv x) A) ps))
      (synWne (.cab x (synWa (.classMem (.cv x) A) ps)) (synC0)) p0012 p0013
  have p0015 :=
    @gFrd ph y z A R (synCvv) (.cab x (synWa (.classMem (.cv x) A) ps)) dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_frds_4 p0008 p0010 p0014
  have p0016 := @gEleq1 (.cv x) (.cv y) A
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gAnbi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A) ps ch
      p0017_e00_recanon hyp_frds_2
  have p0018 :=
    @gRexab (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv y) A) ch)
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))) y x
      dv_cache_0007 dv_cache_0008 p0017
  have p0019 :=
    @gAnass (.classMem (.cv y) A) ch
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))
  have p0020 :=
    @gExbii
      (synWa (synWa (.classMem (.cv y) A) ch)
        (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
      (synWa (.classMem (.cv y) A) (synWa ch
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))
      y p0019
  have p0021 :=
    @gBitri
      (synWrex y (.cab x (synWa (.classMem (.cv x) A) ps))
        (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
      (synWex y (synWa (synWa (.classMem (.cv y) A) ch)
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))
      (synWex y (synWa (.classMem (.cv y) A) (synWa ch
            (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))))
      p0018 p0020
  have p0022 :=
    @gImpexp (.classMem (.cv z) A) th (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))
  have p0023 := @gImpexp th (synWbr (.cv z) R (.cv y)) (.objEq z y)
  have p0024 :=
    @gImbi2i (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))) (.classMem (.cv z) A)
      p0023
  have p0025 :=
    @gBitr4i
      (.imp (synWa (.classMem (.cv z) A) th) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (.imp (.classMem (.cv z) A) (.imp th (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (.imp (.classMem (.cv z) A) (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))
      p0022 p0024
  have p0026 :=
    @gAlbii
      (.imp (synWa (.classMem (.cv z) A) th) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (.imp (.classMem (.cv z) A) (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))
      z p0025
  have p0027 := @gEleq1 (.cv x) (.cv z) A
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.classMem (.cv x) A) (.classMem (.cv z) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0028 :=
    @gAnbi12d (.objEq x z) (.classMem (.cv x) A) (.classMem (.cv z) A) ps th
      p0028_e00_recanon hyp_frds_3
  have p0029 :=
    @gRalab (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv z) A) th)
      (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) z x dv_cache_0009 dv_cache_0010
      p0028
  have p0030 :=
    (Nominal.biimpRefl
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
  have p0031 :=
    @gN3bitr4i
      (.all z (.imp (synWa (.classMem (.cv z) A) th)
          (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (.all z (.imp (.classMem (.cv z) A)
          (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
      (synWral z (.cab x (synWa (.classMem (.cv x) A) ps))
        (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))) p0026
      p0029 p0030
  have p0032 :=
    @gRexbii
      (synWral z (.cab x (synWa (.classMem (.cv x) A) ps))
        (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))) y
      (.cab x (synWa (.classMem (.cv x) A) ps)) p0031
  have p0033 :=
    (Nominal.biimpRefl (synWrex y A (synWa ch
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))))
  have p0034 :=
    @gN3bitr4i
      (synWrex y (.cab x (synWa (.classMem (.cv x) A) ps))
        (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
      (synWex y (synWa (.classMem (.cv y) A) (synWa ch
            (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))))
      (synWrex y (.cab x (synWa (.classMem (.cv x) A) ps))
        (synWral z (.cab x (synWa (.classMem (.cv x) A) ps))
          (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (synWrex y A (synWa ch
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))
      p0021 p0032 p0033
  have p0035 :=
    @gSylib ph
      (synWrex y (.cab x (synWa (.classMem (.cv x) A) ps))
        (synWral z (.cab x (synWa (.classMem (.cv x) A) ps))
          (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))))
      (synWrex y A (synWa ch
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))
      p0015 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_pod`. -/
@[expose]
noncomputable def gPod (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_pod_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_pod_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_pod_3 :
      Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWbr (.cv x) R (.cv x))))
    (hyp_pod_4 : Nominal.NPrf (.imp (synW3a ph
            (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
          (synWbr (.cv x) R (.cv z))))
    (hyp_pod_5 : Nominal.NPrf (.imp
          (synW3a ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) (.objEq x y))) :
    Nominal.NPrf (.imp ph (synWbr R (synCpartial) A)) :=
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
    @gRefrd ph x A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_pod_1 hyp_pod_2
      hyp_pod_3
  have p0001 :=
    @gTrrd ph x y z A R V W dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_pod_1 hyp_pod_2 hyp_pod_4
  have p0002 :=
    @gAntird ph x y A R V W dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006
      dv_cache_0003 dv_cache_0008 dv_cache_0010 hyp_pod_1 hyp_pod_2 hyp_pod_5
  have p0003 := @gPorta A R
  have p0004 :=
    @gSyl3anbrc ph (synWbr R (synCref) A) (synWbr R (synCtrans) A)
      (synWbr R (synCantisym) A) (synWbr R (synCpartial) A) p0000 p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sod`. -/
@[expose]
noncomputable def gSod (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_sod_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_sod_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_sod_3 :
      Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWbr (.cv x) R (.cv x))))
    (hyp_sod_4 : Nominal.NPrf (.imp (synW3a ph
            (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
          (synWbr (.cv x) R (.cv z))))
    (hyp_sod_5 : Nominal.NPrf (.imp
          (synW3a ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) (.objEq x y)))
    (hyp_sod_6 : Nominal.NPrf (.imp (synW3a ph (.classMem (.cv x) A) (.classMem (.cv y) A))
          (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))) :
    Nominal.NPrf (.imp ph (synWbr R (synCstrict) A)) :=
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
    @gPod ph x y z A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_sod_1 hyp_sod_2 hyp_sod_3 hyp_sod_4 hyp_sod_5
  have p0001 :=
    @gConnexrd ph x y A R V W dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0005
      dv_cache_0007 dv_cache_0008 dv_cache_0010 hyp_sod_1 hyp_sod_2 hyp_sod_6
  have p0002 := @gSopc A R
  have p0003 :=
    @gSylanbrc ph (synWbr R (synCpartial) A) (synWbr R (synCconnex) A)
      (synWbr R (synCstrict) A) p0000 p0001 p0002
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

/-- Checked nominal proof certificate identified upstream as `g_weds`. -/
@[expose]
noncomputable def gWeds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_weds_1 : Nominal.NPrf (.classMem (.cab x ps) (synCvv)))
    (hyp_weds_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ps ch)))
    (hyp_weds_3 : Nominal.NPrf (.imp (.objEq x z) (synWb ps th)))
    (hyp_weds_4 : Nominal.NPrf (.imp ph (synWbr R (synCwe) A)))
    (hyp_weds_5 : Nominal.NPrf (.imp ph (synWrex x A ps))) :
    Nominal.NPrf
      (.imp ph (synWrex y A
          (synWa ch (synWral z A (.imp th (synWbr (.cv y) R (.cv z))))))) :=
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
  have dv_cache_0013 : z ∉ ((synWa ph (.classMem (.cv y) A))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0000
  have p0002 := @gBrin R A (synCstrict) (synCfound)
  have p0003 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0001 p0002
  have p0004 :=
    @gSimprbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0005 :=
    @gSyl ph (synWbr R (synCwe) A) (synWbr R (synCfound) A) hyp_weds_4 p0004
  have p0006 :=
    @gFrds ph ps ch th x y z A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 hyp_weds_1 hyp_weds_2 hyp_weds_3 p0005 hyp_weds_5
  have p0007 := @gImpexp th (synWbr (.cv z) R (.cv y)) (.objEq z y)
  have p0008 :=
    @gSimplbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0009 :=
    @gSyl ph (synWbr R (synCwe) A) (synWbr R (synCstrict) A) hyp_weds_4 p0008
  have p0010 := @gSopc A R
  have p0011 :=
    @gSimprbi (synWbr R (synCstrict) A) (synWbr R (synCpartial) A)
      (synWbr R (synCconnex) A) p0010
  have p0012 :=
    @gSyl ph (synWbr R (synCstrict) A) (synWbr R (synCconnex) A) p0009 p0011
  have p0013 :=
    @gAdantr ph (synWbr R (synCconnex) A)
      (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)) p0012
  have p0014 := @gSimprl ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0015 := @gSimprr ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0016 :=
    @gConnexd (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A))) A R
      (.cv y) (.cv z) p0013 p0014 p0015
  have p0017 :=
    @gAx1 (synWbr (.cv y) R (.cv z)) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))
  have p0018 :=
    @gA1i
      (.imp (synWbr (.cv y) R (.cv z)) (.imp (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))
          (synWbr (.cv y) R (.cv z))))
      (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A))) p0017
  have p0019 := @gPm227 (synWbr (.cv z) R (.cv y)) (.objEq z y)
  have p0020 := @gPorta A R
  have p0021 :=
    @gSimp1bi (synWbr R (synCpartial) A) (synWbr R (synCref) A)
      (synWbr R (synCtrans) A) (synWbr R (synCantisym) A) p0020
  have p0022 :=
    @gAdantr (synWbr R (synCpartial) A) (synWbr R (synCref) A)
      (synWbr R (synCconnex) A) p0021
  have p0023 :=
    @gSylbi (synWbr R (synCstrict) A)
      (synWa (synWbr R (synCpartial) A) (synWbr R (synCconnex) A))
      (synWbr R (synCref) A) p0010 p0022
  have p0024 := @gSyl ph (synWbr R (synCstrict) A) (synWbr R (synCref) A) p0009 p0023
  have p0025 := @gAdantr ph (synWbr R (synCref) A) (.classMem (.cv z) A) p0024
  have p0026 := @gSimpr ph (.classMem (.cv z) A)
  have p0027 := @gRefd (synWa ph (.classMem (.cv z) A)) A R (.cv z) p0025 p0026
  have p0028 :=
    @gAdantrl ph (.classMem (.cv z) A) (synWbr (.cv z) R (.cv z)) (.classMem (.cv y) A)
      p0027
  have p0029 := @gBreq1 (.cv z) (.cv y) (.cv z) R
  have p0030_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (synWb (synWbr (.cv z) R (.cv z)) (synWbr (.cv y) R (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @gSyl5ibcom (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (synWbr (.cv z) R (.cv z)) (.objEq z y) (synWbr (.cv y) R (.cv z)) p0028
      p0030_e01_recanon
  have p0031 :=
    @gSyl9r (synWbr (.cv z) R (.cv y)) (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y))
      (.objEq z y) (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (synWbr (.cv y) R (.cv z)) p0019 p0030
  have p0032 :=
    @gJaod (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (synWbr (.cv y) R (.cv z))
      (.imp (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv z) R (.cv y)) p0018 p0031
  have p0033 :=
    @gMpd (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (synWo (synWbr (.cv y) R (.cv z)) (synWbr (.cv z) R (.cv y)))
      (.imp (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) (synWbr (.cv y) R (.cv z)))
      p0016 p0032
  have p0034 :=
    @gImim2d (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)) (synWbr (.cv y) R (.cv z)) th p0033
  have p0035 :=
    @gSyl5bi (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (.imp (synWbr (.cv z) R (.cv y)) (.objEq z y)))
      (synWa ph (synWa (.classMem (.cv y) A) (.classMem (.cv z) A)))
      (.imp th (synWbr (.cv y) R (.cv z))) p0007 p0034
  have p0036 :=
    @gAnassrs ph (.classMem (.cv y) A) (.classMem (.cv z) A)
      (.imp (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))
        (.imp th (synWbr (.cv y) R (.cv z))))
      p0035
  have p0037 :=
    @gRalimdva (synWa ph (.classMem (.cv y) A))
      (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))
      (.imp th (synWbr (.cv y) R (.cv z))) z A dv_cache_0013 p0036
  have p0038 :=
    @gAnim2d (synWa ph (.classMem (.cv y) A))
      (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))
      (synWral z A (.imp th (synWbr (.cv y) R (.cv z)))) ch p0037
  have p0039 :=
    @gReximdva ph
      (synWa ch (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y))))
      (synWa ch (synWral z A (.imp th (synWbr (.cv y) R (.cv z))))) y A dv_cache_0014
      p0038
  have p0040 :=
    @gMpd ph
      (synWrex y A (synWa ch
          (synWral z A (.imp (synWa th (synWbr (.cv z) R (.cv y))) (.objEq z y)))))
      (synWrex y A (synWa ch (synWral z A (.imp th (synWbr (.cv y) R (.cv z))))))
      p0006 p0039
  exact p0040

/-- Checked nominal proof certificate identified upstream as `g_iserd`. -/
@[expose]
noncomputable def gIserd (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_iserd_1 : Nominal.NPrf (.imp ph (.classMem R V)))
    (hyp_iserd_2 : Nominal.NPrf (.imp ph (.classMem A W)))
    (hyp_iserd_3 : Nominal.NPrf (.imp
          (synW3a ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (synWbr (.cv x) R (.cv y))) (synWbr (.cv y) R (.cv x))))
    (hyp_iserd_4 : Nominal.NPrf (.imp (synW3a ph
            (synW3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A))
            (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
          (synWbr (.cv x) R (.cv z)))) :
    Nominal.NPrf (.imp ph (synWbr R (synCer) A)) :=
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
      ((synWral x A (synWral y A
            (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
      ((synWral x A (synWral y A
            (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))).fv :=
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
    @gN3expia ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)) hyp_iserd_3
  have p0001 :=
    @gRalrimivva ph (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y A
      A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0003 := @gBreq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @gImbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (.imp (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) x y (.cv a) (.cv a)
      dv_cache_0005 dv_cache_0006 p0004
  have p0006 :=
    @gRaleq (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) y (.cv a) A
      dv_cache_0007 dv_cache_0001
  have p0007 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) x
      (.cv a) A dv_cache_0008 dv_cache_0009 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSym x y r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0009 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (synWral x (.cv a) (synWral y (.cv a)
          (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      r a R A V W (synCsym) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0007 p0008
  have p0010 :=
    @gSyl2anc ph (.classMem R V) (.classMem A W)
      (synWb (synWbr R (synCsym) A) (synWral x A
          (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))))
      hyp_iserd_1 hyp_iserd_2 p0009
  have p0011 :=
    @gMpbird ph (synWbr R (synCsym) A)
      (synWral x A
        (synWral y A (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))))
      p0001 p0010
  have p0012 :=
    @gTrrd ph x y z A R V W dv_cache_0009 dv_cache_0001 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0002 dv_cache_0003 dv_cache_0026 dv_cache_0004
      dv_cache_0027 dv_cache_0028 hyp_iserd_1 hyp_iserd_2 hyp_iserd_4
  have p0013 := @gErsymtr A R
  have p0014 :=
    @gSylanbrc ph (synWbr R (synCsym) A) (synWbr R (synCtrans) A)
      (synWbr R (synCer) A) p0011 p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_dfec2`. -/
@[expose]
noncomputable def gDfec2 (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv)
    (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (synCec A R) (.cab y (synWbr A R (.cv y)))) :=
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
  have p0000 := (Nominal.classEqRefl (synCec A R))
  have p0001 := @gImasn y A R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gEqtri (synCec A R) (synCima R (synCsn A)) (.cab y (synWbr A R (.cv y))) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ecexg`. -/
@[expose]
noncomputable def gEcexg (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem R B) (.classMem (synCec A R) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCec A R))
  have p0001 := @gSnex A
  have p0002 := @gImaexg R (synCsn A) B (synCvv)
  have p0003 :=
    @gMpan2 (.classMem R B) (.classMem (synCsn A) (synCvv))
      (.classMem (synCima R (synCsn A)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem R B) (synCec A R) (synCima R (synCsn A)) (synCvv) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ecexr`. -/
@[expose]
noncomputable def gEcexr (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem A (synCec B R)) (.classMem B (synCvv))) :=
  by
  have p0000 := @gN0i (synCima R (synCsn B)) A
  have p0001 := @gSnprc B
  have p0002 := @gImaeq2 (synCsn B) (synC0) R
  have p0003 :=
    @gSylbi (.neg (.classMem B (synCvv))) (.classEq (synCsn B) (synC0))
      (.classEq (synCima R (synCsn B)) (synCima R (synC0))) p0001 p0002
  have p0004 := @gIma0 R
  have p0005 :=
    @gSyl6eq (.neg (.classMem B (synCvv))) (synCima R (synCsn B))
      (synCima R (synC0)) (synC0) p0003 p0004
  have p0006 :=
    @gNsyl2 (.classMem A (synCima R (synCsn B)))
      (.classEq (synCima R (synCsn B)) (synC0)) (.classMem B (synCvv)) p0000 p0005
  have p0007 := (Nominal.classEqRefl (synCec B R))
  have p0008 :=
    @gEleq2s (.classMem B (synCvv)) A (synCima R (synCsn B)) (synCec B R) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ersym`. -/
@[expose]
noncomputable def gErsym (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_ersym_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ersym_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ersym_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ersym_4 : Nominal.NPrf (.imp ph (synWbr X R Y))) :
    Nominal.NPrf (.imp ph (synWbr Y R X)) :=
  by
  have p0000 := @gErsymtr A R
  have p0001 :=
    @gSimplbi (synWbr R (synCer) A) (synWbr R (synCsym) A) (synWbr R (synCtrans) A)
      p0000
  have p0002 :=
    @gSyl ph (synWbr R (synCer) A) (synWbr R (synCsym) A) hyp_ersym_1 p0001
  have p0003 := @gSymd ph A R X Y p0002 hyp_ersym_2 hyp_ersym_3 hyp_ersym_4
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ersymb`. -/
@[expose]
noncomputable def gErsymb (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (hyp_ersymb_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ersymb_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ersymb_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (synWb (synWbr X R Y) (synWbr Y R X))) :=
  by
  have p0000 := @gAdantr ph (synWbr R (synCer) A) (synWbr X R Y) hyp_ersymb_1
  have p0001 := @gAdantr ph (.classMem X A) (synWbr X R Y) hyp_ersymb_2
  have p0002 := @gAdantr ph (.classMem Y A) (synWbr X R Y) hyp_ersymb_3
  have p0003 := @gSimpr ph (synWbr X R Y)
  have p0004 := @gErsym (synWa ph (synWbr X R Y)) A R X Y p0000 p0001 p0002 p0003
  have p0005 := @gAdantr ph (synWbr R (synCer) A) (synWbr Y R X) hyp_ersymb_1
  have p0006 := @gAdantr ph (.classMem Y A) (synWbr Y R X) hyp_ersymb_3
  have p0007 := @gAdantr ph (.classMem X A) (synWbr Y R X) hyp_ersymb_2
  have p0008 := @gSimpr ph (synWbr Y R X)
  have p0009 := @gErsym (synWa ph (synWbr Y R X)) A R Y X p0005 p0006 p0007 p0008
  have p0010 := @gImpbida ph (synWbr X R Y) (synWbr Y R X) p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ertr`. -/
@[expose]
noncomputable def gErtr (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) :
    Nominal.NPrf
      (.imp ph (.imp (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z))) :=
  by
  have p0000 := @gErsymtr A R
  have p0001 :=
    @gSimprbi (synWbr R (synCer) A) (synWbr R (synCsym) A) (synWbr R (synCtrans) A)
      p0000
  have p0002 :=
    @gSyl ph (synWbr R (synCer) A) (synWbr R (synCtrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @gAdantr ph (synWbr R (synCtrans) A) (synWa (synWbr X R Y) (synWbr Y R Z)) p0002
  have p0004 :=
    @gAdantr ph (.classMem X A) (synWa (synWbr X R Y) (synWbr Y R Z)) hyp_ertr_2
  have p0005 :=
    @gAdantr ph (.classMem Y A) (synWa (synWbr X R Y) (synWbr Y R Z)) hyp_ertr_3
  have p0006 :=
    @gAdantr ph (.classMem Z A) (synWa (synWbr X R Y) (synWbr Y R Z)) hyp_ertr_4
  have p0007 := @gSimprl ph (synWbr X R Y) (synWbr Y R Z)
  have p0008 := @gSimprr ph (synWbr X R Y) (synWbr Y R Z)
  have p0009 :=
    @gTrd (synWa ph (synWa (synWbr X R Y) (synWbr Y R Z))) A R X Y Z p0003 p0004
      p0005 p0006 p0007 p0008
  have p0010 := @gEx ph (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ertrd`. -/
@[expose]
noncomputable def gErtrd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertrd_5 : Nominal.NPrf (.imp ph (synWbr X R Y)))
    (hyp_ertrd_6 : Nominal.NPrf (.imp ph (synWbr Y R Z))) :
    Nominal.NPrf (.imp ph (synWbr X R Z)) :=
  by
  have p0000 := @gErsymtr A R
  have p0001 :=
    @gSimprbi (synWbr R (synCer) A) (synWbr R (synCsym) A) (synWbr R (synCtrans) A)
      p0000
  have p0002 :=
    @gSyl ph (synWbr R (synCer) A) (synWbr R (synCtrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @gTrd ph A R X Y Z p0002 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertrd_5 hyp_ertrd_6
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ertr3d`. -/
@[expose]
noncomputable def gErtr3d (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertr3d_5 : Nominal.NPrf (.imp ph (synWbr Y R X)))
    (hyp_ertr3d_6 : Nominal.NPrf (.imp ph (synWbr Y R Z))) :
    Nominal.NPrf (.imp ph (synWbr X R Z)) :=
  by
  have p0000 := @gErsym ph A R Y X hyp_ertr_1 hyp_ertr_3 hyp_ertr_2 hyp_ertr3d_5
  have p0001 :=
    @gErtrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 p0000 hyp_ertr3d_6
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ertr4d`. -/
@[expose]
noncomputable def gErtr4d (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) A)))
    (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_ertr4d_5 : Nominal.NPrf (.imp ph (synWbr X R Y)))
    (hyp_ertr4d_6 : Nominal.NPrf (.imp ph (synWbr Z R Y))) :
    Nominal.NPrf (.imp ph (synWbr X R Z)) :=
  by
  have p0000 := @gErsym ph A R Z Y hyp_ertr_1 hyp_ertr_4 hyp_ertr_3 hyp_ertr4d_6
  have p0001 :=
    @gErtrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertr4d_5 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_erref`. -/
@[expose]
noncomputable def gErref (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_erref_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) (synCvv))))
    (hyp_erref_2 : Nominal.NPrf (.imp ph (.classEq (synCdm R) A)))
    (hyp_erref_3 : Nominal.NPrf (.imp ph (.classMem X A))) :
    Nominal.NPrf (.imp ph (synWbr X R X)) :=
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
  have dv_cache_0003 : y ∉ ((synWbr X R X)).fv :=
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
  have p0000 := @gEleq2d ph (synCdm R) A X hyp_erref_2
  have p0001 := @gEldm y X R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gAdantr ph (synWbr R (synCer) (synCvv)) (synWbr X R (.cv y)) hyp_erref_1
  have p0003 := @gElex X A
  have p0004 := @gSyl ph (.classMem X A) (.classMem X (synCvv)) hyp_erref_3 p0003
  have p0005 := @gAdantr ph (.classMem X (synCvv)) (synWbr X R (.cv y)) p0004
  have p0006 := @gVex y
  have p0007 :=
    @gA1i (.classMem (.cv y) (synCvv)) (synWa ph (synWbr X R (.cv y))) p0006
  have p0008 := @gSimpr ph (synWbr X R (.cv y))
  have p0009 :=
    @gErtr4d (synWa ph (synWbr X R (.cv y))) (synCvv) R X (.cv y) X p0002 p0005 p0007
      p0005 p0008 p0008
  have p0010 := @gEx ph (synWbr X R (.cv y)) (synWbr X R X) p0009
  have p0011 :=
    @gExlimdv ph (synWbr X R (.cv y)) (synWbr X R X) y dv_cache_0003 dv_cache_0004
      p0010
  have p0012 :=
    @gSyl5bi (.classMem X (synCdm R)) (synWex y (synWbr X R (.cv y))) ph
      (synWbr X R X) p0001 p0011
  have p0013 :=
    @gSylbird ph (.classMem X A) (.classMem X (synCdm R)) (synWbr X R X) p0000 p0012
  have p0014 := @gMpd ph (.classMem X A) (synWbr X R X) hyp_erref_3 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_eceq1`. -/
@[expose]
noncomputable def gEceq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCec A C) (synCec B C))) :=
  by
  have p0000 := @gSneq A B
  have p0001 := @gImaeq2d (.classEq A B) (synCsn A) (synCsn B) C p0000
  have p0002 := (Nominal.classEqRefl (synCec A C))
  have p0003 := (Nominal.classEqRefl (synCec B C))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCima C (synCsn A)) (synCima C (synCsn B))
      (synCec A C) (synCec B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eceq2`. -/
@[expose]
noncomputable def gEceq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCec C A) (synCec C B))) :=
  by
  have p0000 := @gImaeq1 A B (synCsn C)
  have p0001 := (Nominal.classEqRefl (synCec C A))
  have p0002 := (Nominal.classEqRefl (synCec C B))
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCima A (synCsn C)) (synCima B (synCsn C))
      (synCec C A) (synCec C B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elec`. -/
@[expose]
noncomputable def gElec (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (synWb (.classMem A (synCec B R)) (synWbr B R A)) :=
  by
  have p0000 := @gElimasn R B A
  have p0001 := (Nominal.classEqRefl (synCec B R))
  have p0002 := @gEleq2i (synCec B R) (synCima R (synCsn B)) A p0001
  have p0003 := (Nominal.biimpRefl (synWbr B R A))
  have p0004 :=
    @gN3bitr4i (.classMem A (synCima R (synCsn B))) (.classMem (synCop B A) R)
      (.classMem A (synCec B R)) (synWbr B R A) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_erdmrn`. -/
@[expose]
noncomputable def gErdmrn (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCer) (synCvv)) (.classEq (synCdm R) (synCrn R))) :=
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
  have dv_cache_0001 : y ∉ ((synWbr R (synCer) (synCvv))).fv := by
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
  have dv_cache_0004 : x ∉ ((synCdm R)).fv :=
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
  have dv_cache_0005 : x ∉ ((synCrn R)).fv :=
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
  have dv_cache_0006 : x ∉ ((synWbr R (synCer) (synCvv))).fv :=
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
  have p0000 := @gId (synWbr R (synCer) (synCvv))
  have p0001 := @gVex x
  have p0002 := @gA1i (.classMem (.cv x) (synCvv)) (synWbr R (synCer) (synCvv)) p0001
  have p0003 := @gVex y
  have p0004 := @gA1i (.classMem (.cv y) (synCvv)) (synWbr R (synCer) (synCvv)) p0003
  have p0005 :=
    @gErsymb (synWbr R (synCer) (synCvv)) (synCvv) R (.cv x) (.cv y) p0000 p0002
      p0004
  have p0006 :=
    @gExbidv (synWbr R (synCer) (synCvv)) (synWbr (.cv x) R (.cv y))
      (synWbr (.cv y) R (.cv x)) y dv_cache_0001 p0005
  have p0007 := @gEldm y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0008 := @gElrn y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gN3bitr4g (synWbr R (synCer) (synCvv)) (synWex y (synWbr (.cv x) R (.cv y)))
      (synWex y (synWbr (.cv y) R (.cv x))) (.classMem (.cv x) (synCdm R))
      (.classMem (.cv x) (synCrn R)) p0006 p0007 p0008
  have p0010 :=
    @gEqrdv (synWbr R (synCer) (synCvv)) x (synCdm R) (synCrn R) dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ecss`. -/
@[expose]
noncomputable def gEcss (ph : Wff) (A : Class) (R : Class) (X : Class)
    (hyp_ecss_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) (synCvv))))
    (hyp_ecss_2 : Nominal.NPrf (.imp ph (.classEq (synCdm R) X))) :
    Nominal.NPrf (.imp ph (synWss (synCec A R) X)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCec A R))
  have p0001 := @gImassrn R (synCsn A)
  have p0002 := @gEqsstri (synCec A R) (synCima R (synCsn A)) (synCrn R) p0000 p0001
  have p0003 := @gErdmrn R
  have p0004 :=
    @gSyl ph (synWbr R (synCer) (synCvv)) (.classEq (synCdm R) (synCrn R))
      hyp_ecss_1 p0003
  have p0005 := @gEqtr3d ph (synCdm R) (synCrn R) X p0004 hyp_ecss_2
  have p0006 := @gSyl5sseq ph (synCrn R) (synCec A R) X p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ecdmn0`. -/
@[expose]
noncomputable def gEcdmn0 (A : Class) (R : Class) :
    Nominal.NPrf (synWb (.classMem A (synCdm R)) (synWne (synCec A R) (synC0))) :=
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
  have dv_cache_0001 : x ∉ ((synCec A R)).fv := by
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
  have p0000 := @gElec (.cv x) A R
  have p0001 := @gExbii (.classMem (.cv x) (synCec A R)) (synWbr A R (.cv x)) x p0000
  have p0002 := @gN0 x (synCec A R) dv_cache_0001
  have p0003 := @gEldm x A R dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gN3bitr4ri (synWex x (.classMem (.cv x) (synCec A R)))
      (synWex x (synWbr A R (.cv x))) (synWne (synCec A R) (synC0))
      (.classMem A (synCdm R)) p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
