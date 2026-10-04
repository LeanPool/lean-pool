/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part022`. -/


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

theorem nb078_support_mem_0033 :
    (nb078AlphaDummy010) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCphi (Class.cv (nb078AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy017) from (by
          unfold nb078AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy018) from (by
            unfold nb078AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0034 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0035 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCphi (Class.cv (nb078AlphaDummy020 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy019 f) from (by
          unfold nb078AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy020 f) from (by
            unfold nb078AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0036 :
    (nb078AlphaDummy010) ∈
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy017) from (by
          unfold nb078AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy018) from (by
            unfold nb078AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0037 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy019 f) from (by
          unfold nb078AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy020 f) from (by
            unfold nb078AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0038 :
    (nb078AlphaDummy018) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0039 (f : Var) :
    (nb078AlphaDummy020 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy020 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0040 :
    (nb078AlphaDummy018) ∈
      (((synCphi (Class.cv (nb078AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy018)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0041 (f : Var) :
    (nb078AlphaDummy020 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0042 :
    (nb078AlphaDummy009) ∈
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0043 :
    (nb078AlphaDummy009) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCphi (Class.cv (nb078AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy054) from (by
            unfold nb078AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0044 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0045 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCphi (Class.cv (nb078AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy056 f) from (by
            unfold nb078AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0046 :
    (nb078AlphaDummy009) ∈
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv ∪
        ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy054) from (by
            unfold nb078AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0047 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy056 f) from (by
            unfold nb078AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0048 :
    (nb078AlphaDummy054) ∈ (((Class.cv (nb078AlphaDummy054))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0049 (f : Var) :
    (nb078AlphaDummy056 f) ∈ (((Class.cv (nb078AlphaDummy056 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0050 :
    (nb078AlphaDummy061) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy061))).fv) :=
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

theorem nb078_support_mem_0051 (f : Var) :
    (nb078AlphaDummy063 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy063 f))).fv) :=
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

theorem nb078_support_mem_0052 :
    (nb078AlphaDummy061) ∈
      (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0053 (f : Var) :
    (nb078AlphaDummy063 f) ∈
      (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0054 :
    (nb078AlphaDummy068) ∈
      (((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy068))
            (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0055 (f : Var) :
    (nb078AlphaDummy071 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0056 :
    (nb078AlphaDummy068) ∈
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0057 (f : Var) :
    (nb078AlphaDummy071 f) ∈
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0058 :
    (nb078AlphaDummy069) ∈
      (((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy068))
            (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0059 (f : Var) :
    (nb078AlphaDummy072 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0060 :
    (nb078AlphaDummy069) ∈
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0061 (f : Var) :
    (nb078AlphaDummy072 f) ∈
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0062 :
    (nb078AlphaDummy068) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0063 (f : Var) :
    (nb078AlphaDummy071 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0064 :
    (nb078AlphaDummy068) ∈
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0065 (f : Var) :
    (nb078AlphaDummy071 f) ∈
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0066 :
    (nb078AlphaDummy069) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0067 (f : Var) :
    (nb078AlphaDummy072 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0068 :
    (nb078AlphaDummy069) ∈
      (((Class.cv (nb078AlphaDummy069))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0069 (f : Var) :
    (nb078AlphaDummy072 f) ∈
      (((Class.cv (nb078AlphaDummy072 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0070 :
    (nb078AlphaDummy011) ∈
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0071 :
    (nb078AlphaDummy011) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCphi (Class.cv (nb078AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy054) from (by
            unfold nb078AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0072 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0073 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCphi (Class.cv (nb078AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy056 f) from (by
            unfold nb078AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0074 :
    (nb078AlphaDummy011) ∈
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy054) from (by
            unfold nb078AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0075 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy056 f) from (by
            unfold nb078AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0076 :
    (nb078AlphaDummy054) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0077 (f : Var) :
    (nb078AlphaDummy056 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0078 :
    (nb078AlphaDummy054) ∈
      (((synCphi (Class.cv (nb078AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy054)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0079 (f : Var) :
    (nb078AlphaDummy056 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0080 :
    (nb078AlphaDummy089) ∈
      (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
            (Class.cv (nb078AlphaDummy089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0081 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (({(nb078AlphaDummy091 f)} : Finset Var) ∪ ({(nb078AlphaDummy092 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
            (Class.cv (nb078AlphaDummy091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0082 :
    (nb078AlphaDummy090) ∈
      (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
            (Class.cv (nb078AlphaDummy089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0083 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (({(nb078AlphaDummy091 f)} : Finset Var) ∪ ({(nb078AlphaDummy092 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
            (Class.cv (nb078AlphaDummy091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0084 :
    (nb078AlphaDummy089) ∈
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0085 :
    (nb078AlphaDummy089) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from (by
            unfold nb078AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0086 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0087 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
            unfold nb078AlphaDummy098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0088 :
    (nb078AlphaDummy089) ∈
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv ∪
        ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from (by
            unfold nb078AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0089 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
            unfold nb078AlphaDummy098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0090 :
    (nb078AlphaDummy096) ∈ (((Class.cv (nb078AlphaDummy096))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0091 (f : Var) :
    (nb078AlphaDummy098 f) ∈ (((Class.cv (nb078AlphaDummy098 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0092 :
    (nb078AlphaDummy103) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy103)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy103)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy103))).fv) :=
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

theorem nb078_support_mem_0093 (f : Var) :
    (nb078AlphaDummy105 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy105 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy105 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy105 f))).fv) :=
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

theorem nb078_support_mem_0094 :
    (nb078AlphaDummy103) ∈
      (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0095 (f : Var) :
    (nb078AlphaDummy105 f) ∈
      (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0096 :
    (nb078AlphaDummy110) ∈
      (((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy110))
            (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0097 (f : Var) :
    (nb078AlphaDummy113 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0098 :
    (nb078AlphaDummy110) ∈
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0099 (f : Var) :
    (nb078AlphaDummy113 f) ∈
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0100 :
    (nb078AlphaDummy111) ∈
      (((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy110))
            (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0101 (f : Var) :
    (nb078AlphaDummy114 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0102 :
    (nb078AlphaDummy111) ∈
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0103 (f : Var) :
    (nb078AlphaDummy114 f) ∈
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0104 :
    (nb078AlphaDummy110) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy110)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0105 (f : Var) :
    (nb078AlphaDummy113 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy113 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0106 :
    (nb078AlphaDummy110) ∈
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy110))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0107 (f : Var) :
    (nb078AlphaDummy113 f) ∈
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy113 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0108 :
    (nb078AlphaDummy111) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy110)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0109 (f : Var) :
    (nb078AlphaDummy114 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy113 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0110 :
    (nb078AlphaDummy111) ∈
      (((Class.cv (nb078AlphaDummy111))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0111 (f : Var) :
    (nb078AlphaDummy114 f) ∈
      (((Class.cv (nb078AlphaDummy114 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0112 :
    (nb078AlphaDummy090) ∈
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0113 :
    (nb078AlphaDummy090) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095) from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
            unfold nb078AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0114 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0115 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
            unfold nb078AlphaDummy098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0116 :
    (nb078AlphaDummy090) ∈
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095) from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
            unfold nb078AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0117 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
            unfold nb078AlphaDummy098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0118 :
    (nb078AlphaDummy096) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy096))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0119 (f : Var) :
    (nb078AlphaDummy098 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy098 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0120 :
    (nb078AlphaDummy096) ∈
      (((synCphi (Class.cv (nb078AlphaDummy096)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0121 (f : Var) :
    (nb078AlphaDummy098 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0122 :
    (nb078AlphaDummy090) ∈
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0123 :
    (nb078AlphaDummy090) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCphi (Class.cv (nb078AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy131) from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy132) from (by
            unfold nb078AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0124 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0125 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCphi (Class.cv (nb078AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy134 f) from (by
            unfold nb078AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0126 :
    (nb078AlphaDummy090) ∈
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv ∪
        ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy131) from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy132) from (by
            unfold nb078AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0127 (f : Var) :
    (nb078AlphaDummy092 f) ∈
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy134 f) from (by
            unfold nb078AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0128 :
    (nb078AlphaDummy132) ∈ (((Class.cv (nb078AlphaDummy132))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0129 (f : Var) :
    (nb078AlphaDummy134 f) ∈ (((Class.cv (nb078AlphaDummy134 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0130 :
    (nb078AlphaDummy139) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy139))).fv) :=
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

theorem nb078_support_mem_0131 (f : Var) :
    (nb078AlphaDummy141 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy141 f))).fv) :=
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

theorem nb078_support_mem_0132 :
    (nb078AlphaDummy139) ∈
      (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0133 (f : Var) :
    (nb078AlphaDummy141 f) ∈
      (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0134 :
    (nb078AlphaDummy146) ∈
      (((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy146))
            (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0135 (f : Var) :
    (nb078AlphaDummy149 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0136 :
    (nb078AlphaDummy146) ∈
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0137 (f : Var) :
    (nb078AlphaDummy149 f) ∈
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0138 :
    (nb078AlphaDummy147) ∈
      (((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy146))
            (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0139 (f : Var) :
    (nb078AlphaDummy150 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0140 :
    (nb078AlphaDummy147) ∈
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0141 (f : Var) :
    (nb078AlphaDummy150 f) ∈
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0142 :
    (nb078AlphaDummy146) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0143 (f : Var) :
    (nb078AlphaDummy149 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0144 :
    (nb078AlphaDummy146) ∈
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0145 (f : Var) :
    (nb078AlphaDummy149 f) ∈
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0146 :
    (nb078AlphaDummy147) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0147 (f : Var) :
    (nb078AlphaDummy150 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0148 :
    (nb078AlphaDummy147) ∈
      (((Class.cv (nb078AlphaDummy147))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0149 (f : Var) :
    (nb078AlphaDummy150 f) ∈
      (((Class.cv (nb078AlphaDummy150 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0150 :
    (nb078AlphaDummy089) ∈
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0151 :
    (nb078AlphaDummy089) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCphi (Class.cv (nb078AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131) from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
            unfold nb078AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0152 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0153 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCphi (Class.cv (nb078AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
            unfold nb078AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0154 :
    (nb078AlphaDummy089) ∈
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131) from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
            unfold nb078AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0155 (f : Var) :
    (nb078AlphaDummy091 f) ∈
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
            unfold nb078AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0156 :
    (nb078AlphaDummy132) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0157 (f : Var) :
    (nb078AlphaDummy134 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0158 :
    (nb078AlphaDummy132) ∈
      (((synCphi (Class.cv (nb078AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy132)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0159 (f : Var) :
    (nb078AlphaDummy134 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0160 :
    (nb078AlphaDummy000) ∈
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv) :=
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

theorem nb078_support_mem_0161 (f : Var) :
    f ∈
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
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

theorem nb078_support_mem_0162 :
    (nb078AlphaDummy000) ∈
      (((synCcom (Class.cv (nb078AlphaDummy000))
            (synCcnv (Class.cv (nb078AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0163 (f : Var) :
    f ∈ (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0164 :
    (nb078AlphaDummy000) ∈
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0165 :
    (nb078AlphaDummy000) ∈
      (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy011) from (by
          unfold nb078AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0166 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0167 (f : Var) :
    f ∈
      (({(nb078AlphaDummy012 f)} : Finset Var) ∪ ({(nb078AlphaDummy013 f)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb078AlphaDummy014 f) from (by
          unfold nb078AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0168 :
    (nb078AlphaDummy000) ∈
      (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
            (Class.cv (nb078AlphaDummy089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0169 (f : Var) :
    f ∈
      (({(nb078AlphaDummy091 f)} : Finset Var) ∪ ({(nb078AlphaDummy092 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
            (Class.cv (nb078AlphaDummy091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0170 :
    (nb078AlphaDummy000) ∈ (((Class.cv (nb078AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part023`. -/


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

theorem nb078_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0172 :
    (nb078AlphaDummy011) ∈
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0173 :
    (nb078AlphaDummy011) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCphi (Class.cv (nb078AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy168) from (by
            unfold nb078AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0174 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0175 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCphi (Class.cv (nb078AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy170 f) from (by
            unfold nb078AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0176 :
    (nb078AlphaDummy011) ∈
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv ∪
        ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy168) from (by
            unfold nb078AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0177 (f : Var) :
    (nb078AlphaDummy014 f) ∈
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy170 f) from (by
            unfold nb078AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0178 :
    (nb078AlphaDummy168) ∈ (((Class.cv (nb078AlphaDummy168))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0179 (f : Var) :
    (nb078AlphaDummy170 f) ∈ (((Class.cv (nb078AlphaDummy170 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0180 :
    (nb078AlphaDummy175) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy175))).fv) :=
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

theorem nb078_support_mem_0181 (f : Var) :
    (nb078AlphaDummy177 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy177 f))).fv) :=
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

theorem nb078_support_mem_0182 :
    (nb078AlphaDummy175) ∈
      (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0183 (f : Var) :
    (nb078AlphaDummy177 f) ∈
      (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0184 :
    (nb078AlphaDummy182) ∈
      (((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy182))
            (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0185 (f : Var) :
    (nb078AlphaDummy185 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0186 :
    (nb078AlphaDummy182) ∈
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0187 (f : Var) :
    (nb078AlphaDummy185 f) ∈
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0188 :
    (nb078AlphaDummy183) ∈
      (((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy182))
            (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0189 (f : Var) :
    (nb078AlphaDummy186 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0190 :
    (nb078AlphaDummy183) ∈
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0191 (f : Var) :
    (nb078AlphaDummy186 f) ∈
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0192 :
    (nb078AlphaDummy182) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0193 (f : Var) :
    (nb078AlphaDummy185 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0194 :
    (nb078AlphaDummy182) ∈
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0195 (f : Var) :
    (nb078AlphaDummy185 f) ∈
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0196 :
    (nb078AlphaDummy183) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0197 (f : Var) :
    (nb078AlphaDummy186 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0198 :
    (nb078AlphaDummy183) ∈
      (((Class.cv (nb078AlphaDummy183))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0199 (f : Var) :
    (nb078AlphaDummy186 f) ∈
      (((Class.cv (nb078AlphaDummy186 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0200 :
    (nb078AlphaDummy010) ∈
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0201 :
    (nb078AlphaDummy010) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCphi (Class.cv (nb078AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy168) from (by
            unfold nb078AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0202 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0203 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCphi (Class.cv (nb078AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy170 f) from (by
            unfold nb078AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0204 :
    (nb078AlphaDummy010) ∈
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy168) from (by
            unfold nb078AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0205 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy170 f) from (by
            unfold nb078AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0206 :
    (nb078AlphaDummy168) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0207 (f : Var) :
    (nb078AlphaDummy170 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0208 :
    (nb078AlphaDummy168) ∈
      (((synCphi (Class.cv (nb078AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy168)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0209 (f : Var) :
    (nb078AlphaDummy170 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0210 :
    (nb078AlphaDummy204) ∈
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0211 :
    (nb078AlphaDummy204) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCphi (Class.cv (nb078AlphaDummy208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy207) from (by
          unfold nb078AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy208) from (by
            unfold nb078AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0212 (f : Var) :
    (nb078AlphaDummy206 f) ∈
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0213 (f : Var) :
    (nb078AlphaDummy206 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCphi (Class.cv (nb078AlphaDummy210 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy209 f) from (by
          unfold nb078AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy210 f) from (by
            unfold nb078AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0214 :
    (nb078AlphaDummy204) ∈
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy207) from (by
          unfold nb078AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy208) from (by
            unfold nb078AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0215 (f : Var) :
    (nb078AlphaDummy206 f) ∈
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy209 f) from (by
          unfold nb078AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy210 f) from (by
            unfold nb078AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0216 :
    (nb078AlphaDummy208) ∈ (((Class.cv (nb078AlphaDummy208))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0217 (f : Var) :
    (nb078AlphaDummy210 f) ∈ (((Class.cv (nb078AlphaDummy210 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0218 :
    (nb078AlphaDummy215) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy215))).fv) :=
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

theorem nb078_support_mem_0219 (f : Var) :
    (nb078AlphaDummy217 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy217 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy217 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy217 f))).fv) :=
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

theorem nb078_support_mem_0220 :
    (nb078AlphaDummy215) ∈
      (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0221 (f : Var) :
    (nb078AlphaDummy217 f) ∈
      (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0222 :
    (nb078AlphaDummy222) ∈
      (((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy222))
            (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0223 (f : Var) :
    (nb078AlphaDummy225 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0224 :
    (nb078AlphaDummy222) ∈
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0225 (f : Var) :
    (nb078AlphaDummy225 f) ∈
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0226 :
    (nb078AlphaDummy223) ∈
      (((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy222))
            (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0227 (f : Var) :
    (nb078AlphaDummy226 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0228 :
    (nb078AlphaDummy223) ∈
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0229 (f : Var) :
    (nb078AlphaDummy226 f) ∈
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0230 :
    (nb078AlphaDummy222) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0231 (f : Var) :
    (nb078AlphaDummy225 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy225 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0232 :
    (nb078AlphaDummy222) ∈
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy222))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0233 (f : Var) :
    (nb078AlphaDummy225 f) ∈
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy225 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0234 :
    (nb078AlphaDummy223) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0235 (f : Var) :
    (nb078AlphaDummy226 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy225 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0236 :
    (nb078AlphaDummy223) ∈
      (((Class.cv (nb078AlphaDummy223))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0237 (f : Var) :
    (nb078AlphaDummy226 f) ∈
      (((Class.cv (nb078AlphaDummy226 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0238 :
    (nb078AlphaDummy203) ∈
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0239 :
    (nb078AlphaDummy203) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCphi (Class.cv (nb078AlphaDummy208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy207) from (by
          unfold nb078AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy208) from (by
            unfold nb078AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0240 (f : Var) :
    (nb078AlphaDummy205 f) ∈
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0241 (f : Var) :
    (nb078AlphaDummy205 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCphi (Class.cv (nb078AlphaDummy210 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy209 f) from (by
          unfold nb078AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy210 f) from (by
            unfold nb078AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0242 :
    (nb078AlphaDummy203) ∈
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy207) from (by
          unfold nb078AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy208) from (by
            unfold nb078AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0243 (f : Var) :
    (nb078AlphaDummy205 f) ∈
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy209 f) from (by
          unfold nb078AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy210 f) from (by
            unfold nb078AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0244 :
    (nb078AlphaDummy208) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0245 (f : Var) :
    (nb078AlphaDummy210 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy210 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0246 :
    (nb078AlphaDummy208) ∈
      (((synCphi (Class.cv (nb078AlphaDummy208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy208)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0247 (f : Var) :
    (nb078AlphaDummy210 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0248 :
    (nb078AlphaDummy000) ∈
      (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0249 (f : Var) :
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0250 :
    (nb078AlphaDummy244) ∈
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0251 :
    (nb078AlphaDummy244) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCphi (Class.cv (nb078AlphaDummy248)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy247) from (by
          unfold nb078AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy248) from (by
            unfold nb078AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0252 (f : Var) :
    (nb078AlphaDummy246 f) ∈
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0253 (f : Var) :
    (nb078AlphaDummy246 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCphi (Class.cv (nb078AlphaDummy250 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy249 f) from (by
          unfold nb078AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy250 f) from (by
            unfold nb078AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0254 :
    (nb078AlphaDummy244) ∈
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv ∪
        ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy247) from (by
          unfold nb078AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy248) from (by
            unfold nb078AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0255 (f : Var) :
    (nb078AlphaDummy246 f) ∈
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy249 f) from (by
          unfold nb078AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy250 f) from (by
            unfold nb078AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0256 :
    (nb078AlphaDummy248) ∈ (((Class.cv (nb078AlphaDummy248))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0257 (f : Var) :
    (nb078AlphaDummy250 f) ∈ (((Class.cv (nb078AlphaDummy250 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0258 :
    (nb078AlphaDummy255) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy255)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy255)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy255))).fv) :=
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

theorem nb078_support_mem_0259 (f : Var) :
    (nb078AlphaDummy257 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy257 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy257 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy257 f))).fv) :=
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

theorem nb078_support_mem_0260 :
    (nb078AlphaDummy255) ∈
      (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0261 (f : Var) :
    (nb078AlphaDummy257 f) ∈
      (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0262 :
    (nb078AlphaDummy262) ∈
      (((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy262))
            (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0263 (f : Var) :
    (nb078AlphaDummy265 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0264 :
    (nb078AlphaDummy262) ∈
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0265 (f : Var) :
    (nb078AlphaDummy265 f) ∈
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0266 :
    (nb078AlphaDummy263) ∈
      (((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy262))
            (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0267 (f : Var) :
    (nb078AlphaDummy266 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0268 :
    (nb078AlphaDummy263) ∈
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0269 (f : Var) :
    (nb078AlphaDummy266 f) ∈
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0270 :
    (nb078AlphaDummy262) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy262)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0271 (f : Var) :
    (nb078AlphaDummy265 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy265 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0272 :
    (nb078AlphaDummy262) ∈
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy262))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0273 (f : Var) :
    (nb078AlphaDummy265 f) ∈
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy265 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0274 :
    (nb078AlphaDummy263) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy262)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0275 (f : Var) :
    (nb078AlphaDummy266 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy265 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0276 :
    (nb078AlphaDummy263) ∈
      (((Class.cv (nb078AlphaDummy263))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0277 (f : Var) :
    (nb078AlphaDummy266 f) ∈
      (((Class.cv (nb078AlphaDummy266 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0278 :
    (nb078AlphaDummy243) ∈
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0279 :
    (nb078AlphaDummy243) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCphi (Class.cv (nb078AlphaDummy248)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy247) from (by
          unfold nb078AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy248) from (by
            unfold nb078AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0280 (f : Var) :
    (nb078AlphaDummy245 f) ∈
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0281 (f : Var) :
    (nb078AlphaDummy245 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCphi (Class.cv (nb078AlphaDummy250 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy249 f) from (by
          unfold nb078AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy250 f) from (by
            unfold nb078AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0282 :
    (nb078AlphaDummy243) ∈
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy247) from (by
          unfold nb078AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy248) from (by
            unfold nb078AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0283 (f : Var) :
    (nb078AlphaDummy245 f) ∈
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy249 f) from (by
          unfold nb078AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy250 f) from (by
            unfold nb078AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0284 :
    (nb078AlphaDummy248) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy248))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0285 (f : Var) :
    (nb078AlphaDummy250 f) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy250 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0286 :
    (nb078AlphaDummy248) ∈
      (((synCphi (Class.cv (nb078AlphaDummy248)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy248)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0287 (f : Var) :
    (nb078AlphaDummy250 f) ∈
      (((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0288 :
    (nb078AlphaDummy000) ∈
      (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0289 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0290 :
    (nb078AlphaDummy287) ∈
      (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0291 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (({(nb078AlphaDummy290 g)} : Finset Var) ∪ ({(nb078AlphaDummy291 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0292 :
    (nb078AlphaDummy288) ∈
      (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0293 (g : Var) :
    (nb078AlphaDummy291 g) ∈
      (({(nb078AlphaDummy290 g)} : Finset Var) ∪ ({(nb078AlphaDummy291 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0294 :
    (nb078AlphaDummy287) ∈
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0295 :
    (nb078AlphaDummy287) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCphi (Class.cv (nb078AlphaDummy296)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy295) from (by
          unfold nb078AlphaDummy295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy296) from (by
            unfold nb078AlphaDummy296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0296 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0297 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCphi (Class.cv (nb078AlphaDummy298 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy297 g) from (by
          unfold nb078AlphaDummy297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy298 g) from (by
            unfold nb078AlphaDummy298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0298 :
    (nb078AlphaDummy287) ∈
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv ∪
        ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy295) from (by
          unfold nb078AlphaDummy295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy296) from (by
            unfold nb078AlphaDummy296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0299 (g : Var) :
    (nb078AlphaDummy290 g) ∈
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy297 g) from (by
          unfold nb078AlphaDummy297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy298 g) from (by
            unfold nb078AlphaDummy298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0300 :
    (nb078AlphaDummy296) ∈ (((Class.cv (nb078AlphaDummy296))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0301 (g : Var) :
    (nb078AlphaDummy298 g) ∈ (((Class.cv (nb078AlphaDummy298 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0302 :
    (nb078AlphaDummy303) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy303)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy303)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy303))).fv) :=
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

theorem nb078_support_mem_0303 (g : Var) :
    (nb078AlphaDummy305 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy305 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy305 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy305 g))).fv) :=
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

theorem nb078_support_mem_0304 :
    (nb078AlphaDummy303) ∈
      (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0305 (g : Var) :
    (nb078AlphaDummy305 g) ∈
      (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0306 :
    (nb078AlphaDummy310) ∈
      (((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy310))
            (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0307 (g : Var) :
    (nb078AlphaDummy313 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0308 :
    (nb078AlphaDummy310) ∈
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0309 (g : Var) :
    (nb078AlphaDummy313 g) ∈
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0310 :
    (nb078AlphaDummy311) ∈
      (((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy310))
            (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0311 (g : Var) :
    (nb078AlphaDummy314 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0312 :
    (nb078AlphaDummy311) ∈
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
