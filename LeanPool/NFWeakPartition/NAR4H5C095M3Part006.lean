/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part005

/-! NF weak partition development: NAR4H5C095M3Part006. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_support_mem_0007 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_021 f) from (by
          unfold nb095_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_022 f) from (by
            unfold nb095_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0008 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_019 D R S_cls E) from (by
          unfold nb095_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_020 D R S_cls E) from (by
            unfold nb095_alpha_dummy_020;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0009 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_021 f) from (by
          unfold nb095_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_022 f) from (by
            unfold nb095_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0010 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_020 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0011 (f : Var) :
    (nb095_alpha_dummy_022 f) ∈ (((Class.cv (nb095_alpha_dummy_022 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0012 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_027 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0013 (f : Var) :
    (nb095_alpha_dummy_029 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_029 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_029 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_029 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0014 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_027 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0015 (f : Var) :
    (nb095_alpha_dummy_029 f) ∈
      (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0016 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0017 (f : Var) :
    (nb095_alpha_dummy_037 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0018 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0019 (f : Var) :
    (nb095_alpha_dummy_037 f) ∈
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0020 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_035 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0021 (f : Var) :
    (nb095_alpha_dummy_038 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0022 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_035 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0023 (f : Var) :
    (nb095_alpha_dummy_038 f) ∈
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0024 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_034 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0025 (f : Var) :
    (nb095_alpha_dummy_037 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_037 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0026 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0027 (f : Var) :
    (nb095_alpha_dummy_037 f) ∈
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_037 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_035 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_034 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0029 (f : Var) :
    (nb095_alpha_dummy_038 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_037 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0030 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_035 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0031 (f : Var) :
    (nb095_alpha_dummy_038 f) ∈
      (((Class.cv (nb095_alpha_dummy_038 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0033 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_019 D R S_cls E) from (by
          unfold nb095_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0032 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_020 D R S_cls E) from (by
            unfold nb095_alpha_dummy_020;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0032 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0034 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0035 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_021 f) from (by
          unfold nb095_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_022 f) from (by
            unfold nb095_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0036 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_019 D R S_cls E) from (by
          unfold nb095_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0032 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_020 D R S_cls E) from (by
            unfold nb095_alpha_dummy_020;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0032 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0037 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_021 f) from (by
          unfold nb095_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_022 f) from (by
            unfold nb095_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0038 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_020 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0039 (f : Var) :
    (nb095_alpha_dummy_022 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0040 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_020 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0041 (f : Var) :
    (nb095_alpha_dummy_022 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0042 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0043 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
            unfold nb095_alpha_dummy_056;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0044 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0045 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_058 f) from (by
            unfold nb095_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0046 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
            unfold nb095_alpha_dummy_056;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0047 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_058 f) from (by
            unfold nb095_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0048 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_056 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0049 (f : Var) :
    (nb095_alpha_dummy_058 f) ∈ (((Class.cv (nb095_alpha_dummy_058 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0050 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_063 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0051 (f : Var) :
    (nb095_alpha_dummy_065 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_065 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_065 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_065 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_063 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0053 (f : Var) :
    (nb095_alpha_dummy_065 f) ∈
      (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0054 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0055 (f : Var) :
    (nb095_alpha_dummy_073 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0057 (f : Var) :
    (nb095_alpha_dummy_073 f) ∈
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0058 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_071 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0059 (f : Var) :
    (nb095_alpha_dummy_074 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_071 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0061 (f : Var) :
    (nb095_alpha_dummy_074 f) ∈
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0062 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_070 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0063 (f : Var) :
    (nb095_alpha_dummy_073 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_073 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0065 (f : Var) :
    (nb095_alpha_dummy_073 f) ∈
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_073 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0066 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_071 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_070 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0067 (f : Var) :
    (nb095_alpha_dummy_074 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_073 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0068 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_071 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0069 (f : Var) :
    (nb095_alpha_dummy_074 f) ∈
      (((Class.cv (nb095_alpha_dummy_074 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0070 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0071 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0070 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
            unfold nb095_alpha_dummy_056;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0070 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0072 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0073 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
            unfold nb095_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0074 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0070 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
            unfold nb095_alpha_dummy_056;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0070 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0075 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
            unfold nb095_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0076 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_056 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0077 (f : Var) :
    (nb095_alpha_dummy_058 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0078 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_056 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0079 (f : Var) :
    (nb095_alpha_dummy_058 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0080 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0081 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_093 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0082 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0083 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_093 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0084 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0085 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
            unfold nb095_alpha_dummy_098;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0086 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0087 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
            unfold nb095_alpha_dummy_100;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0088 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
            unfold nb095_alpha_dummy_098;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0089 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
            unfold nb095_alpha_dummy_100;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0090 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_098 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0091 (f : Var) :
    (nb095_alpha_dummy_100 f) ∈ (((Class.cv (nb095_alpha_dummy_100 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0092 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_105 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0093 (f : Var) :
    (nb095_alpha_dummy_107 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_107 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_107 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0094 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_105 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0095 (f : Var) :
    (nb095_alpha_dummy_107 f) ∈
      (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0096 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0097 (f : Var) :
    (nb095_alpha_dummy_115 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0098 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0099 (f : Var) :
    (nb095_alpha_dummy_115 f) ∈
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0100 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_113 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0101 (f : Var) :
    (nb095_alpha_dummy_116 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0102 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_113 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0103 (f : Var) :
    (nb095_alpha_dummy_116 f) ∈
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0104 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_112 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0105 (f : Var) :
    (nb095_alpha_dummy_115 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_115 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0106 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0107 (f : Var) :
    (nb095_alpha_dummy_115 f) ∈
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_115 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0108 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_113 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_112 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0109 (f : Var) :
    (nb095_alpha_dummy_116 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_115 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0110 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_113 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0111 (f : Var) :
    (nb095_alpha_dummy_116 f) ∈
      (((Class.cv (nb095_alpha_dummy_116 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0112 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0113 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0112 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
            unfold nb095_alpha_dummy_098;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0112 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0114 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0115 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
            unfold nb095_alpha_dummy_100;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0116 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0112 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
            unfold nb095_alpha_dummy_098;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0112 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0117 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
            unfold nb095_alpha_dummy_100;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0118 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_098 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0119 (f : Var) :
    (nb095_alpha_dummy_100 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0120 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_098 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0121 (f : Var) :
    (nb095_alpha_dummy_100 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0122 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0123 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
            unfold nb095_alpha_dummy_134;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0124 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0125 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_136 f) from (by
            unfold nb095_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0126 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
            unfold nb095_alpha_dummy_134;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0127 (f : Var) :
    (nb095_alpha_dummy_094 f) ∈
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_136 f) from (by
            unfold nb095_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_support_mem_0128 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_134 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0129 (f : Var) :
    (nb095_alpha_dummy_136 f) ∈ (((Class.cv (nb095_alpha_dummy_136 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0130 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_141 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0131 (f : Var) :
    (nb095_alpha_dummy_143 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_143 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_143 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_143 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0132 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_141 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0133 (f : Var) :
    (nb095_alpha_dummy_143 f) ∈
      (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0134 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0135 (f : Var) :
    (nb095_alpha_dummy_151 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0136 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0137 (f : Var) :
    (nb095_alpha_dummy_151 f) ∈
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0138 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_149 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0139 (f : Var) :
    (nb095_alpha_dummy_152 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0140 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_149 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0141 (f : Var) :
    (nb095_alpha_dummy_152 f) ∈
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0142 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_148 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0143 (f : Var) :
    (nb095_alpha_dummy_151 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_151 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0144 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0145 (f : Var) :
    (nb095_alpha_dummy_151 f) ∈
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_151 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0146 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_149 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_148 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0147 (f : Var) :
    (nb095_alpha_dummy_152 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_151 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0148 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_149 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0149 (f : Var) :
    (nb095_alpha_dummy_152 f) ∈
      (((Class.cv (nb095_alpha_dummy_152 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0150 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0151 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0150 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
            unfold nb095_alpha_dummy_134;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0150 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0152 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0153 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
            unfold nb095_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0154 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0150 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
            unfold nb095_alpha_dummy_134;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0150 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0155 (f : Var) :
    (nb095_alpha_dummy_093 f) ∈
      (((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
            unfold nb095_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0156 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_134 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0157 (f : Var) :
    (nb095_alpha_dummy_136 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0158 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_134 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0159 (f : Var) :
    (nb095_alpha_dummy_136 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0160 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0161 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0162 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0163 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0164 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0165 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_013 D R S_cls E) from (by
          unfold nb095_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb095_support_mem_0166 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0167 (f : Var) :
    f ∈
      (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_016 f) from (by
          unfold nb095_alpha_dummy_016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0166 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb095_support_mem_0168 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0169 (f : Var) :
    f ∈
      (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_093 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0170 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0172 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0173 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
            unfold nb095_alpha_dummy_170;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0174 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0175 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_172 f) from (by
            unfold nb095_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0176 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
            unfold nb095_alpha_dummy_170;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0177 (f : Var) :
    (nb095_alpha_dummy_016 f) ∈
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_172 f) from (by
            unfold nb095_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0178 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_170 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0179 (f : Var) :
    (nb095_alpha_dummy_172 f) ∈ (((Class.cv (nb095_alpha_dummy_172 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0180 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_177 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0181 (f : Var) :
    (nb095_alpha_dummy_179 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_179 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0182 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_177 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0183 (f : Var) :
    (nb095_alpha_dummy_179 f) ∈
      (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0184 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0185 (f : Var) :
    (nb095_alpha_dummy_187 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0186 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0187 (f : Var) :
    (nb095_alpha_dummy_187 f) ∈
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0188 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_185 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0189 (f : Var) :
    (nb095_alpha_dummy_188 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0190 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_185 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0191 (f : Var) :
    (nb095_alpha_dummy_188 f) ∈
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0192 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_184 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0193 (f : Var) :
    (nb095_alpha_dummy_187 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0194 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0195 (f : Var) :
    (nb095_alpha_dummy_187 f) ∈
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_187 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0196 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_185 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_184 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0197 (f : Var) :
    (nb095_alpha_dummy_188 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0198 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_185 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0199 (f : Var) :
    (nb095_alpha_dummy_188 f) ∈
      (((Class.cv (nb095_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0200 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0201 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0200 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
            unfold nb095_alpha_dummy_170;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0200 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0202 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0203 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
            unfold nb095_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0204 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0200 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
            unfold nb095_alpha_dummy_170;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0200 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0205 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
            unfold nb095_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0206 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_170 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0207 (f : Var) :
    (nb095_alpha_dummy_172 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0208 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_170 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0209 (f : Var) :
    (nb095_alpha_dummy_172 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0210 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_206 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0211 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_206 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_206 D R S_cls E) ≠ (nb095_alpha_dummy_209 D R S_cls E) from (by
          unfold nb095_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_206 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) from (by
            unfold nb095_alpha_dummy_210;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0212 (f : Var) :
    (nb095_alpha_dummy_208 f) ∈
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0213 (f : Var) :
    (nb095_alpha_dummy_208 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_211 f) from (by
          unfold nb095_alpha_dummy_211;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_212 f) from (by
            unfold nb095_alpha_dummy_212;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0214 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_206 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_206 D R S_cls E) ≠ (nb095_alpha_dummy_209 D R S_cls E) from (by
          unfold nb095_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_206 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) from (by
            unfold nb095_alpha_dummy_210;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0215 (f : Var) :
    (nb095_alpha_dummy_208 f) ∈
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_211 f) from (by
          unfold nb095_alpha_dummy_211;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_212 f) from (by
            unfold nb095_alpha_dummy_212;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0216 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_210 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0217 (f : Var) :
    (nb095_alpha_dummy_212 f) ∈ (((Class.cv (nb095_alpha_dummy_212 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0218 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_217 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0219 (f : Var) :
    (nb095_alpha_dummy_219 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_219 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_219 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_219 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0220 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_217 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0221 (f : Var) :
    (nb095_alpha_dummy_219 f) ∈
      (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0222 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0223 (f : Var) :
    (nb095_alpha_dummy_227 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0224 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0225 (f : Var) :
    (nb095_alpha_dummy_227 f) ∈
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0226 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_225 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0227 (f : Var) :
    (nb095_alpha_dummy_228 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0228 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_225 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0229 (f : Var) :
    (nb095_alpha_dummy_228 f) ∈
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0230 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_224 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0231 (f : Var) :
    (nb095_alpha_dummy_227 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_227 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0232 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0233 (f : Var) :
    (nb095_alpha_dummy_227 f) ∈
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_227 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0234 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_225 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_224 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0235 (f : Var) :
    (nb095_alpha_dummy_228 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_227 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0236 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_225 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0237 (f : Var) :
    (nb095_alpha_dummy_228 f) ∈
      (((Class.cv (nb095_alpha_dummy_228 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0238 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_205 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0239 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_205 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_209 D R S_cls E) from (by
          unfold nb095_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) from (by
            unfold nb095_alpha_dummy_210;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0240 (f : Var) :
    (nb095_alpha_dummy_207 f) ∈
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0241 (f : Var) :
    (nb095_alpha_dummy_207 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_211 f) from (by
          unfold nb095_alpha_dummy_211;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_212 f) from (by
            unfold nb095_alpha_dummy_212;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0242 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_205 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_209 D R S_cls E) from (by
          unfold nb095_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) from (by
            unfold nb095_alpha_dummy_210;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0243 (f : Var) :
    (nb095_alpha_dummy_207 f) ∈
      (((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_211 f) from (by
          unfold nb095_alpha_dummy_211;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_212 f) from (by
            unfold nb095_alpha_dummy_212;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0244 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_210 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0245 (f : Var) :
    (nb095_alpha_dummy_212 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0246 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_210 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0247 (f : Var) :
    (nb095_alpha_dummy_212 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0248 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0249 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0250 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0251 (x : Var) (D : Class) (R : Class) :
    x ∈
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0252 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0253 (x : Var) (D : Class) (R : Class) :
    x ∈
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0254 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0255 (x : Var) (R : Class) :
    x ∈ (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0256 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_002 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0257 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0258 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_250 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_support_mem_0259 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_250 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_250 D R S_cls E) ≠ (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_250 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
            unfold nb095_alpha_dummy_256;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0260 (x : Var) (R : Class) :
    (nb095_alpha_dummy_252 x R) ∈
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0261 (x : Var) (R : Class) :
    (nb095_alpha_dummy_252 x R) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold nb095_alpha_dummy_257;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
            unfold nb095_alpha_dummy_258;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0260 x R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0262 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_250 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_250 D R S_cls E) ≠ (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_250 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
            unfold nb095_alpha_dummy_256;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0263 (x : Var) (R : Class) :
    (nb095_alpha_dummy_252 x R) ∈
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold nb095_alpha_dummy_257;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
            unfold nb095_alpha_dummy_258;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0260 x R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0264 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_256 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0265 (x : Var) (R : Class) :
    (nb095_alpha_dummy_258 x R) ∈ (((Class.cv (nb095_alpha_dummy_258 x R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0266 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_263 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0267 (x : Var) (R : Class) :
    (nb095_alpha_dummy_265 x R) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_265 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_265 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_265 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0268 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_263 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0269 (x : Var) (R : Class) :
    (nb095_alpha_dummy_265 x R) ∈
      (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0270 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0271 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0272 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0273 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ∈
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0274 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_271 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0275 (x : Var) (R : Class) :
    (nb095_alpha_dummy_274 x R) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0276 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_271 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0277 (x : Var) (R : Class) :
    (nb095_alpha_dummy_274 x R) ∈
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0278 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_270 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0279 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_273 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0280 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0281 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ∈
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_273 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0282 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_271 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_270 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0283 (x : Var) (R : Class) :
    (nb095_alpha_dummy_274 x R) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_273 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0284 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_271 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0285 (x : Var) (R : Class) :
    (nb095_alpha_dummy_274 x R) ∈
      (((Class.cv (nb095_alpha_dummy_274 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0286 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0287 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0286 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
            unfold nb095_alpha_dummy_256;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0286 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0288 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ∈
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0289 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold nb095_alpha_dummy_257;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0288 x R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
            unfold nb095_alpha_dummy_258;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0288 x R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0290 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0286 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
            unfold nb095_alpha_dummy_256;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0286 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0291 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ∈
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold nb095_alpha_dummy_257;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0288 x R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
            unfold nb095_alpha_dummy_258;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0288 x R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0292 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_256 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0293 (x : Var) (R : Class) :
    (nb095_alpha_dummy_258 x R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0294 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_256 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0295 (x : Var) (R : Class) :
    (nb095_alpha_dummy_258 x R) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0296 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_296 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0297 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_296 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_296 D R S_cls E) ≠ (nb095_alpha_dummy_299 D R S_cls E) from (by
          unfold nb095_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_296 D R S_cls E) ≠ (nb095_alpha_dummy_300 D R S_cls E) from (by
            unfold nb095_alpha_dummy_300;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0298 (f : Var) :
    (nb095_alpha_dummy_298 f) ∈
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0299 (f : Var) :
    (nb095_alpha_dummy_298 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_301 f) from (by
          unfold nb095_alpha_dummy_301;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_302 f) from (by
            unfold nb095_alpha_dummy_302;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0300 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_296 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_296 D R S_cls E) ≠ (nb095_alpha_dummy_299 D R S_cls E) from (by
          unfold nb095_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_296 D R S_cls E) ≠ (nb095_alpha_dummy_300 D R S_cls E) from (by
            unfold nb095_alpha_dummy_300;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0301 (f : Var) :
    (nb095_alpha_dummy_298 f) ∈
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_301 f) from (by
          unfold nb095_alpha_dummy_301;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_302 f) from (by
            unfold nb095_alpha_dummy_302;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0302 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_300 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0303 (f : Var) :
    (nb095_alpha_dummy_302 f) ∈ (((Class.cv (nb095_alpha_dummy_302 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0304 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_307 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0305 (f : Var) :
    (nb095_alpha_dummy_309 f) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_309 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_309 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_309 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0306 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_307 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0307 (f : Var) :
    (nb095_alpha_dummy_309 f) ∈
      (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0308 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0309 (f : Var) :
    (nb095_alpha_dummy_317 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0310 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0311 (f : Var) :
    (nb095_alpha_dummy_317 f) ∈
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0312 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_315 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0313 (f : Var) :
    (nb095_alpha_dummy_318 f) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0314 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_315 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0315 (f : Var) :
    (nb095_alpha_dummy_318 f) ∈
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0316 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_314 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0317 (f : Var) :
    (nb095_alpha_dummy_317 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_317 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0318 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0319 (f : Var) :
    (nb095_alpha_dummy_317 f) ∈
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_317 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0320 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_315 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_314 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0321 (f : Var) :
    (nb095_alpha_dummy_318 f) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_317 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0322 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_315 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0323 (f : Var) :
    (nb095_alpha_dummy_318 f) ∈
      (((Class.cv (nb095_alpha_dummy_318 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0324 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_295 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0325 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_295 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_295 D R S_cls E) ≠ (nb095_alpha_dummy_299 D R S_cls E) from (by
          unfold nb095_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_295 D R S_cls E) ≠ (nb095_alpha_dummy_300 D R S_cls E) from (by
            unfold nb095_alpha_dummy_300;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0326 (f : Var) :
    (nb095_alpha_dummy_297 f) ∈
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0327 (f : Var) :
    (nb095_alpha_dummy_297 f) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_297 f) ≠ (nb095_alpha_dummy_301 f) from (by
          unfold nb095_alpha_dummy_301;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_297 f) ≠ (nb095_alpha_dummy_302 f) from (by
            unfold nb095_alpha_dummy_302;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0328 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_295 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_295 D R S_cls E) ≠ (nb095_alpha_dummy_299 D R S_cls E) from (by
          unfold nb095_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_295 D R S_cls E) ≠ (nb095_alpha_dummy_300 D R S_cls E) from (by
            unfold nb095_alpha_dummy_300;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0324 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0329 (f : Var) :
    (nb095_alpha_dummy_297 f) ∈
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_297 f) ≠ (nb095_alpha_dummy_301 f) from (by
          unfold nb095_alpha_dummy_301;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_297 f) ≠ (nb095_alpha_dummy_302 f) from (by
            unfold nb095_alpha_dummy_302;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0326 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0330 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_300 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0331 (f : Var) :
    (nb095_alpha_dummy_302 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0332 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_300 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0333 (f : Var) :
    (nb095_alpha_dummy_302 f) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0334 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0335 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    f ∈
      (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0336 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0337 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    f ∈
      (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0338 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0339 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0340 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0341 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    u ∈
      (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0342 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0343 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    u ∈
      (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0344 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0345 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      (((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0346 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0347 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0348 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0349 (u : Var) (S_cls : Class) :
    u ∈ (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0350 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_001 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0351 (u : Var) : u ∈ (((Class.cv u)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0352 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0353 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_340 D R S_cls E) ≠ (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_340 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
            unfold nb095_alpha_dummy_346;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0354 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0355 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_347 u S_cls)
              (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_342 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_341 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from (by
          unfold nb095_alpha_dummy_347;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from (by
            unfold nb095_alpha_dummy_348;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0356 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_340 D R S_cls E) ≠ (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_340 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
            unfold nb095_alpha_dummy_346;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0357 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∈
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from (by
          unfold nb095_alpha_dummy_347;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from (by
            unfold nb095_alpha_dummy_348;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0358 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_346 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0359 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_348 u S_cls) ∈ (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0360 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_353 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0361 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_355 u S_cls) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0362 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_353 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0363 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_355 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0364 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0365 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0366 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0367 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0368 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_361 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0369 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_364 u S_cls) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0370 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_361 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0371 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_364 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0372 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_360 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0373 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_363 u S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0374 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0375 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0376 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_361 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_360 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0377 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_364 u S_cls) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_363 u S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0378 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_361 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0379 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_364 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0380 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0381 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
            unfold nb095_alpha_dummy_346;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0380 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0382 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∈
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0383 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_347 u S_cls)
              (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_342 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_341 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from (by
          unfold nb095_alpha_dummy_347;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from (by
            unfold nb095_alpha_dummy_348;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0382 u S_cls) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
