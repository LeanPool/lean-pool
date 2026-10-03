/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part010`. -/


section

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

theorem nb068_support_mem_0076 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0077 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_056 f) from (by
            unfold nb068_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0078 :
    (nb068_alpha_dummy_046) ∈
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_054) from (by
            unfold nb068_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0079 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_056 f) from (by
            unfold nb068_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0080 :
    (nb068_alpha_dummy_054) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0081 (f : Var) :
    (nb068_alpha_dummy_056 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0082 :
    (nb068_alpha_dummy_054) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0083 (f : Var) :
    (nb068_alpha_dummy_056 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0084 :
    (nb068_alpha_dummy_045) ∈
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0085 :
    (nb068_alpha_dummy_045) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_089) from (by
          unfold nb068_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_090) from (by
            unfold nb068_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0086 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0087 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_091 f) from (by
          unfold nb068_alpha_dummy_091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_092 f) from (by
            unfold nb068_alpha_dummy_092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0088 :
    (nb068_alpha_dummy_045) ∈
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_089) from (by
          unfold nb068_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_090) from (by
            unfold nb068_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0089 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_091 f) from (by
          unfold nb068_alpha_dummy_091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_092 f) from (by
            unfold nb068_alpha_dummy_092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0090 :
    (nb068_alpha_dummy_090) ∈ (((Class.cv (nb068_alpha_dummy_090))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0091 (f : Var) :
    (nb068_alpha_dummy_092 f) ∈ (((Class.cv (nb068_alpha_dummy_092 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0092 :
    (nb068_alpha_dummy_097) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_097))).fv) :=
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

theorem nb068_support_mem_0093 (f : Var) :
    (nb068_alpha_dummy_099 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_099 f))).fv) :=
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

theorem nb068_support_mem_0094 :
    (nb068_alpha_dummy_097) ∈
      (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0095 (f : Var) :
    (nb068_alpha_dummy_099 f) ∈
      (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0096 :
    (nb068_alpha_dummy_104) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_104))
            (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0097 (f : Var) :
    (nb068_alpha_dummy_107 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0098 :
    (nb068_alpha_dummy_104) ∈
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0099 (f : Var) :
    (nb068_alpha_dummy_107 f) ∈
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0100 :
    (nb068_alpha_dummy_105) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_104))
            (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0101 (f : Var) :
    (nb068_alpha_dummy_108 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0102 :
    (nb068_alpha_dummy_105) ∈
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0103 (f : Var) :
    (nb068_alpha_dummy_108 f) ∈
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0104 :
    (nb068_alpha_dummy_104) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0105 (f : Var) :
    (nb068_alpha_dummy_107 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0106 :
    (nb068_alpha_dummy_104) ∈
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0107 (f : Var) :
    (nb068_alpha_dummy_107 f) ∈
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0108 :
    (nb068_alpha_dummy_105) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0109 (f : Var) :
    (nb068_alpha_dummy_108 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0110 :
    (nb068_alpha_dummy_105) ∈
      (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0111 (f : Var) :
    (nb068_alpha_dummy_108 f) ∈
      (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0112 :
    (nb068_alpha_dummy_047) ∈
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0113 :
    (nb068_alpha_dummy_047) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_089) from (by
          unfold nb068_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_090) from (by
            unfold nb068_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0114 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0115 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_091 f) from (by
          unfold nb068_alpha_dummy_091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_092 f) from (by
            unfold nb068_alpha_dummy_092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0116 :
    (nb068_alpha_dummy_047) ∈
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_089) from (by
          unfold nb068_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_090) from (by
            unfold nb068_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0117 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_091 f) from (by
          unfold nb068_alpha_dummy_091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_092 f) from (by
            unfold nb068_alpha_dummy_092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0118 :
    (nb068_alpha_dummy_090) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0119 (f : Var) :
    (nb068_alpha_dummy_092 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0120 :
    (nb068_alpha_dummy_090) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0121 (f : Var) :
    (nb068_alpha_dummy_092 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0122 :
    (nb068_alpha_dummy_125) ∈
      (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0123 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0124 :
    (nb068_alpha_dummy_126) ∈
      (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0125 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0126 :
    (nb068_alpha_dummy_125) ∈
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0127 :
    (nb068_alpha_dummy_125) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from (by
            unfold nb068_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0128 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0129 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from (by
            unfold nb068_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0130 :
    (nb068_alpha_dummy_125) ∈
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from (by
            unfold nb068_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0131 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from (by
            unfold nb068_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0132 :
    (nb068_alpha_dummy_132) ∈ (((Class.cv (nb068_alpha_dummy_132))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0133 (f : Var) :
    (nb068_alpha_dummy_134 f) ∈ (((Class.cv (nb068_alpha_dummy_134 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0134 :
    (nb068_alpha_dummy_139) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_139))).fv) :=
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

theorem nb068_support_mem_0135 (f : Var) :
    (nb068_alpha_dummy_141 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_141 f))).fv) :=
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

theorem nb068_support_mem_0136 :
    (nb068_alpha_dummy_139) ∈
      (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0137 (f : Var) :
    (nb068_alpha_dummy_141 f) ∈
      (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0138 :
    (nb068_alpha_dummy_146) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_146))
            (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0139 (f : Var) :
    (nb068_alpha_dummy_149 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0140 :
    (nb068_alpha_dummy_146) ∈
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0141 (f : Var) :
    (nb068_alpha_dummy_149 f) ∈
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0142 :
    (nb068_alpha_dummy_147) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_146))
            (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0143 (f : Var) :
    (nb068_alpha_dummy_150 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0144 :
    (nb068_alpha_dummy_147) ∈
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0145 (f : Var) :
    (nb068_alpha_dummy_150 f) ∈
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0146 :
    (nb068_alpha_dummy_146) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0147 (f : Var) :
    (nb068_alpha_dummy_149 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0148 :
    (nb068_alpha_dummy_146) ∈
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0149 (f : Var) :
    (nb068_alpha_dummy_149 f) ∈
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0150 :
    (nb068_alpha_dummy_147) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0151 (f : Var) :
    (nb068_alpha_dummy_150 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0152 :
    (nb068_alpha_dummy_147) ∈
      (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0153 (f : Var) :
    (nb068_alpha_dummy_150 f) ∈
      (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0154 :
    (nb068_alpha_dummy_126) ∈
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0155 :
    (nb068_alpha_dummy_126) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from (by
            unfold nb068_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0156 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0157 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
            unfold nb068_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0158 :
    (nb068_alpha_dummy_126) ∈
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from (by
            unfold nb068_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0159 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
            unfold nb068_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0160 :
    (nb068_alpha_dummy_132) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0161 (f : Var) :
    (nb068_alpha_dummy_134 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0162 :
    (nb068_alpha_dummy_132) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0163 (f : Var) :
    (nb068_alpha_dummy_134 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0164 :
    (nb068_alpha_dummy_126) ∈
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0165 :
    (nb068_alpha_dummy_126) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from (by
          unfold nb068_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
            unfold nb068_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0166 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0167 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from (by
          unfold nb068_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
            unfold nb068_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0168 :
    (nb068_alpha_dummy_126) ∈
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from (by
          unfold nb068_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
            unfold nb068_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0169 (f : Var) :
    (nb068_alpha_dummy_128 f) ∈
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from (by
          unfold nb068_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
            unfold nb068_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0170 :
    (nb068_alpha_dummy_168) ∈ (((Class.cv (nb068_alpha_dummy_168))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0171 (f : Var) :
    (nb068_alpha_dummy_170 f) ∈ (((Class.cv (nb068_alpha_dummy_170 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0172 :
    (nb068_alpha_dummy_175) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_175))).fv) :=
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

theorem nb068_support_mem_0173 (f : Var) :
    (nb068_alpha_dummy_177 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_177 f))).fv) :=
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

theorem nb068_support_mem_0174 :
    (nb068_alpha_dummy_175) ∈
      (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0175 (f : Var) :
    (nb068_alpha_dummy_177 f) ∈
      (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0176 :
    (nb068_alpha_dummy_182) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_182))
            (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0177 (f : Var) :
    (nb068_alpha_dummy_185 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0178 :
    (nb068_alpha_dummy_182) ∈
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0179 (f : Var) :
    (nb068_alpha_dummy_185 f) ∈
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0180 :
    (nb068_alpha_dummy_183) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_182))
            (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0181 (f : Var) :
    (nb068_alpha_dummy_186 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0182 :
    (nb068_alpha_dummy_183) ∈
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0183 (f : Var) :
    (nb068_alpha_dummy_186 f) ∈
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0184 :
    (nb068_alpha_dummy_182) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0185 (f : Var) :
    (nb068_alpha_dummy_185 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0186 :
    (nb068_alpha_dummy_182) ∈
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0187 (f : Var) :
    (nb068_alpha_dummy_185 f) ∈
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0188 :
    (nb068_alpha_dummy_183) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0189 (f : Var) :
    (nb068_alpha_dummy_186 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0190 :
    (nb068_alpha_dummy_183) ∈
      (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0191 (f : Var) :
    (nb068_alpha_dummy_186 f) ∈
      (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0192 :
    (nb068_alpha_dummy_125) ∈
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0193 :
    (nb068_alpha_dummy_125) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from (by
          unfold nb068_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from (by
            unfold nb068_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0194 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0195 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
          unfold nb068_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
            unfold nb068_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0196 :
    (nb068_alpha_dummy_125) ∈
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from (by
          unfold nb068_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from (by
            unfold nb068_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0197 (f : Var) :
    (nb068_alpha_dummy_127 f) ∈
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
          unfold nb068_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
            unfold nb068_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0198 :
    (nb068_alpha_dummy_168) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0199 (f : Var) :
    (nb068_alpha_dummy_170 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0200 :
    (nb068_alpha_dummy_168) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0201 (f : Var) :
    (nb068_alpha_dummy_170 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0202 :
    (nb068_alpha_dummy_000) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) :=
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

theorem nb068_support_mem_0203 (f : Var) :
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

theorem nb068_support_mem_0204 :
    (nb068_alpha_dummy_000) ∈
      (((syn_ccom (Class.cv (nb068_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0205 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0206 :
    (nb068_alpha_dummy_000) ∈
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0207 :
    (nb068_alpha_dummy_000) ∈
      (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047))
                (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_047) from (by
          unfold nb068_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0208 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0209 (f : Var) :
    f ∈
      (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_050 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
                (Class.cv (nb068_alpha_dummy_049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb068_alpha_dummy_050 f) from (by
          unfold nb068_alpha_dummy_050;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0210 :
    (nb068_alpha_dummy_000) ∈
      (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0211 (f : Var) :
    f ∈
      (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0212 :
    (nb068_alpha_dummy_000) ∈ (((Class.cv (nb068_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0214 :
    (nb068_alpha_dummy_047) ∈
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part011`. -/


section

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

theorem nb068_support_mem_0215 :
    (nb068_alpha_dummy_047) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_203) from (by
          unfold nb068_alpha_dummy_203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_204) from (by
            unfold nb068_alpha_dummy_204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0216 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0217 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_205 f) from (by
          unfold nb068_alpha_dummy_205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_206 f) from (by
            unfold nb068_alpha_dummy_206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0218 :
    (nb068_alpha_dummy_047) ∈
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_203) from (by
          unfold nb068_alpha_dummy_203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_204) from (by
            unfold nb068_alpha_dummy_204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0219 (f : Var) :
    (nb068_alpha_dummy_050 f) ∈
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_205 f) from (by
          unfold nb068_alpha_dummy_205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_206 f) from (by
            unfold nb068_alpha_dummy_206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0220 :
    (nb068_alpha_dummy_204) ∈ (((Class.cv (nb068_alpha_dummy_204))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0221 (f : Var) :
    (nb068_alpha_dummy_206 f) ∈ (((Class.cv (nb068_alpha_dummy_206 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0222 :
    (nb068_alpha_dummy_211) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_211))).fv) :=
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

theorem nb068_support_mem_0223 (f : Var) :
    (nb068_alpha_dummy_213 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_213 f))).fv) :=
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

theorem nb068_support_mem_0224 :
    (nb068_alpha_dummy_211) ∈
      (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0225 (f : Var) :
    (nb068_alpha_dummy_213 f) ∈
      (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0226 :
    (nb068_alpha_dummy_218) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_218))
            (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0227 (f : Var) :
    (nb068_alpha_dummy_221 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0228 :
    (nb068_alpha_dummy_218) ∈
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0229 (f : Var) :
    (nb068_alpha_dummy_221 f) ∈
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0230 :
    (nb068_alpha_dummy_219) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_218))
            (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0231 (f : Var) :
    (nb068_alpha_dummy_222 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0232 :
    (nb068_alpha_dummy_219) ∈
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0233 (f : Var) :
    (nb068_alpha_dummy_222 f) ∈
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0234 :
    (nb068_alpha_dummy_218) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0235 (f : Var) :
    (nb068_alpha_dummy_221 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0236 :
    (nb068_alpha_dummy_218) ∈
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0237 (f : Var) :
    (nb068_alpha_dummy_221 f) ∈
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0238 :
    (nb068_alpha_dummy_219) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0239 (f : Var) :
    (nb068_alpha_dummy_222 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0240 :
    (nb068_alpha_dummy_219) ∈
      (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0241 (f : Var) :
    (nb068_alpha_dummy_222 f) ∈
      (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0242 :
    (nb068_alpha_dummy_046) ∈
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0243 :
    (nb068_alpha_dummy_046) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_203) from (by
          unfold nb068_alpha_dummy_203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_204) from (by
            unfold nb068_alpha_dummy_204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0244 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0245 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_205 f) from (by
          unfold nb068_alpha_dummy_205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_206 f) from (by
            unfold nb068_alpha_dummy_206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0246 :
    (nb068_alpha_dummy_046) ∈
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_203) from (by
          unfold nb068_alpha_dummy_203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_204) from (by
            unfold nb068_alpha_dummy_204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0247 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_205 f) from (by
          unfold nb068_alpha_dummy_205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_206 f) from (by
            unfold nb068_alpha_dummy_206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0248 :
    (nb068_alpha_dummy_204) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0249 (f : Var) :
    (nb068_alpha_dummy_206 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0250 :
    (nb068_alpha_dummy_204) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0251 (f : Var) :
    (nb068_alpha_dummy_206 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0252 :
    (nb068_alpha_dummy_240) ∈
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0253 :
    (nb068_alpha_dummy_240) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_244) from (by
            unfold nb068_alpha_dummy_244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0254 (f : Var) :
    (nb068_alpha_dummy_242 f) ∈
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0255 (f : Var) :
    (nb068_alpha_dummy_242 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_246 f) from (by
            unfold nb068_alpha_dummy_246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0256 :
    (nb068_alpha_dummy_240) ∈
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_244) from (by
            unfold nb068_alpha_dummy_244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0257 (f : Var) :
    (nb068_alpha_dummy_242 f) ∈
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_246 f) from (by
            unfold nb068_alpha_dummy_246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0258 :
    (nb068_alpha_dummy_244) ∈ (((Class.cv (nb068_alpha_dummy_244))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0259 (f : Var) :
    (nb068_alpha_dummy_246 f) ∈ (((Class.cv (nb068_alpha_dummy_246 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0260 :
    (nb068_alpha_dummy_251) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_251))).fv) :=
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

theorem nb068_support_mem_0261 (f : Var) :
    (nb068_alpha_dummy_253 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_253 f))).fv) :=
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

theorem nb068_support_mem_0262 :
    (nb068_alpha_dummy_251) ∈
      (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0263 (f : Var) :
    (nb068_alpha_dummy_253 f) ∈
      (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0264 :
    (nb068_alpha_dummy_258) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_258))
            (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0265 (f : Var) :
    (nb068_alpha_dummy_261 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0266 :
    (nb068_alpha_dummy_258) ∈
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0267 (f : Var) :
    (nb068_alpha_dummy_261 f) ∈
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0268 :
    (nb068_alpha_dummy_259) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_258))
            (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0269 (f : Var) :
    (nb068_alpha_dummy_262 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0270 :
    (nb068_alpha_dummy_259) ∈
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0271 (f : Var) :
    (nb068_alpha_dummy_262 f) ∈
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0272 :
    (nb068_alpha_dummy_258) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0273 (f : Var) :
    (nb068_alpha_dummy_261 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0274 :
    (nb068_alpha_dummy_258) ∈
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0275 (f : Var) :
    (nb068_alpha_dummy_261 f) ∈
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0276 :
    (nb068_alpha_dummy_259) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0277 (f : Var) :
    (nb068_alpha_dummy_262 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0278 :
    (nb068_alpha_dummy_259) ∈
      (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0279 (f : Var) :
    (nb068_alpha_dummy_262 f) ∈
      (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0280 :
    (nb068_alpha_dummy_239) ∈
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0281 :
    (nb068_alpha_dummy_239) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_244) from (by
            unfold nb068_alpha_dummy_244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0282 (f : Var) :
    (nb068_alpha_dummy_241 f) ∈
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0283 (f : Var) :
    (nb068_alpha_dummy_241 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_246 f) from (by
            unfold nb068_alpha_dummy_246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0284 :
    (nb068_alpha_dummy_239) ∈
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_244) from (by
            unfold nb068_alpha_dummy_244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0285 (f : Var) :
    (nb068_alpha_dummy_241 f) ∈
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_246 f) from (by
            unfold nb068_alpha_dummy_246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0286 :
    (nb068_alpha_dummy_244) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0287 (f : Var) :
    (nb068_alpha_dummy_246 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0288 :
    (nb068_alpha_dummy_244) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0289 (f : Var) :
    (nb068_alpha_dummy_246 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0290 :
    (nb068_alpha_dummy_000) ∈
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0291 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0292 :
    (nb068_alpha_dummy_284) ∈
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0293 :
    (nb068_alpha_dummy_284) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287) from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
            unfold nb068_alpha_dummy_288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0294 (f : Var) :
    (nb068_alpha_dummy_286 f) ∈
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0295 (f : Var) :
    (nb068_alpha_dummy_286 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
            unfold nb068_alpha_dummy_290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0296 :
    (nb068_alpha_dummy_284) ∈
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287) from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
            unfold nb068_alpha_dummy_288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0297 (f : Var) :
    (nb068_alpha_dummy_286 f) ∈
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
            unfold nb068_alpha_dummy_290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0298 :
    (nb068_alpha_dummy_288) ∈ (((Class.cv (nb068_alpha_dummy_288))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0299 (f : Var) :
    (nb068_alpha_dummy_290 f) ∈ (((Class.cv (nb068_alpha_dummy_290 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0300 :
    (nb068_alpha_dummy_295) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_295))).fv) :=
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

theorem nb068_support_mem_0301 (f : Var) :
    (nb068_alpha_dummy_297 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_297 f))).fv) :=
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

theorem nb068_support_mem_0302 :
    (nb068_alpha_dummy_295) ∈
      (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0303 (f : Var) :
    (nb068_alpha_dummy_297 f) ∈
      (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0304 :
    (nb068_alpha_dummy_302) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_302))
            (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0305 (f : Var) :
    (nb068_alpha_dummy_305 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0306 :
    (nb068_alpha_dummy_302) ∈
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0307 (f : Var) :
    (nb068_alpha_dummy_305 f) ∈
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0308 :
    (nb068_alpha_dummy_303) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_302))
            (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0309 (f : Var) :
    (nb068_alpha_dummy_306 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0310 :
    (nb068_alpha_dummy_303) ∈
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0311 (f : Var) :
    (nb068_alpha_dummy_306 f) ∈
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0312 :
    (nb068_alpha_dummy_302) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0313 (f : Var) :
    (nb068_alpha_dummy_305 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0314 :
    (nb068_alpha_dummy_302) ∈
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0315 (f : Var) :
    (nb068_alpha_dummy_305 f) ∈
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0316 :
    (nb068_alpha_dummy_303) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0317 (f : Var) :
    (nb068_alpha_dummy_306 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0318 :
    (nb068_alpha_dummy_303) ∈
      (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0319 (f : Var) :
    (nb068_alpha_dummy_306 f) ∈
      (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0320 :
    (nb068_alpha_dummy_283) ∈
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0321 :
    (nb068_alpha_dummy_283) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from (by
            unfold nb068_alpha_dummy_288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0322 (f : Var) :
    (nb068_alpha_dummy_285 f) ∈
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0323 (f : Var) :
    (nb068_alpha_dummy_285 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
            unfold nb068_alpha_dummy_290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0324 :
    (nb068_alpha_dummy_283) ∈
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from (by
            unfold nb068_alpha_dummy_288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0325 (f : Var) :
    (nb068_alpha_dummy_285 f) ∈
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
            unfold nb068_alpha_dummy_290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0326 :
    (nb068_alpha_dummy_288) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0327 (f : Var) :
    (nb068_alpha_dummy_290 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0328 :
    (nb068_alpha_dummy_288) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0329 (f : Var) :
    (nb068_alpha_dummy_290 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0330 :
    (nb068_alpha_dummy_000) ∈
      (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0331 (y : Var) (f : Var) :
    f ∈
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0332 :
    (nb068_alpha_dummy_000) ∈
      (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0333 (y : Var) (f : Var) :
    f ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0334 :
    (nb068_alpha_dummy_000) ∈
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0335 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0336 :
    (nb068_alpha_dummy_002) ∈
      (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0337 (y : Var) (f : Var) :
    y ∈
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0338 :
    (nb068_alpha_dummy_002) ∈
      (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0339 (y : Var) (f : Var) :
    y ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0340 :
    (nb068_alpha_dummy_327) ∈
      (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
                (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
                (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0341 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0342 :
    (nb068_alpha_dummy_328) ∈
      (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
                (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
                (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0343 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0344 :
    (nb068_alpha_dummy_327) ∈
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0345 :
    (nb068_alpha_dummy_327) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_335) from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_336) from (by
            unfold nb068_alpha_dummy_336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0346 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0347 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_338 f) from (by
            unfold nb068_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0348 :
    (nb068_alpha_dummy_327) ∈
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_335) from (by
          unfold nb068_alpha_dummy_335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_336) from (by
            unfold nb068_alpha_dummy_336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0349 (f : Var) :
    (nb068_alpha_dummy_330 f) ∈
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_337 f) from (by
          unfold nb068_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_338 f) from (by
            unfold nb068_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0350 :
    (nb068_alpha_dummy_336) ∈ (((Class.cv (nb068_alpha_dummy_336))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0351 (f : Var) :
    (nb068_alpha_dummy_338 f) ∈ (((Class.cv (nb068_alpha_dummy_338 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0352 :
    (nb068_alpha_dummy_343) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_343))).fv) :=
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

theorem nb068_support_mem_0353 (f : Var) :
    (nb068_alpha_dummy_345 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_345 f))).fv) :=
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

theorem nb068_support_mem_0354 :
    (nb068_alpha_dummy_343) ∈
      (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0355 (f : Var) :
    (nb068_alpha_dummy_345 f) ∈
      (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
