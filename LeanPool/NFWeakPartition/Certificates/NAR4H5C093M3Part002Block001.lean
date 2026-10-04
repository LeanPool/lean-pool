/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4H5C093M3Part002Stage1`. -/


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

theorem nb093_support_mem_0051 (r : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((synCcompl (synCcnv (Class.cv r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0052 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (({(nb093AlphaDummy058 A)} : Finset Var) ∪ ({(nb093AlphaDummy059 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
            (Class.cv (nb093AlphaDummy058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0053 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (({(nb093AlphaDummy060 r)} : Finset Var) ∪ ({(nb093AlphaDummy061 r)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
            (Class.cv (nb093AlphaDummy060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0054 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (({(nb093AlphaDummy058 A)} : Finset Var) ∪ ({(nb093AlphaDummy059 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
            (Class.cv (nb093AlphaDummy058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0055 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (({(nb093AlphaDummy060 r)} : Finset Var) ∪ ({(nb093AlphaDummy061 r)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
            (Class.cv (nb093AlphaDummy060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0056 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0057 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCphi (Class.cv (nb093AlphaDummy065 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy065 A) from (by
            unfold nb093AlphaDummy065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0058 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0059 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCphi (Class.cv (nb093AlphaDummy067 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy067 r) from (by
            unfold nb093AlphaDummy067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0060 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy065 A) from (by
            unfold nb093AlphaDummy065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0061 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy067 r) from (by
            unfold nb093AlphaDummy067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0062 (A : Class) :
    (nb093AlphaDummy065 A) ∈ (((Class.cv (nb093AlphaDummy065 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0063 (r : Var) :
    (nb093AlphaDummy067 r) ∈ (((Class.cv (nb093AlphaDummy067 r))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0064 (A : Class) :
    (nb093AlphaDummy072 A) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy072 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy072 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy072 A))).fv) :=
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

theorem nb093_support_mem_0065 (r : Var) :
    (nb093AlphaDummy074 r) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy074 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy074 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy074 r))).fv) :=
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

theorem nb093_support_mem_0066 (A : Class) :
    (nb093AlphaDummy072 A) ∈
      (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0067 (r : Var) :
    (nb093AlphaDummy074 r) ∈
      (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0068 (A : Class) :
    (nb093AlphaDummy079 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0069 (r : Var) :
    (nb093AlphaDummy082 r) ∈
      (((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0070 (A : Class) :
    (nb093AlphaDummy079 A) ∈
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0071 (r : Var) :
    (nb093AlphaDummy082 r) ∈
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0072 (A : Class) :
    (nb093AlphaDummy080 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy079 A))
            (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0073 (r : Var) :
    (nb093AlphaDummy083 r) ∈
      (((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy082 r))
            (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0074 (A : Class) :
    (nb093AlphaDummy080 A) ∈
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0075 (r : Var) :
    (nb093AlphaDummy083 r) ∈
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0076 (A : Class) :
    (nb093AlphaDummy079 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy079 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0077 (r : Var) :
    (nb093AlphaDummy082 r) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy082 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0078 (A : Class) :
    (nb093AlphaDummy079 A) ∈
      (((Class.cv (nb093AlphaDummy079 A))).fv ∪ ((Class.cv (nb093AlphaDummy079 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0079 (r : Var) :
    (nb093AlphaDummy082 r) ∈
      (((Class.cv (nb093AlphaDummy082 r))).fv ∪ ((Class.cv (nb093AlphaDummy082 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0080 (A : Class) :
    (nb093AlphaDummy080 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy079 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0081 (r : Var) :
    (nb093AlphaDummy083 r) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy082 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0082 (A : Class) :
    (nb093AlphaDummy080 A) ∈
      (((Class.cv (nb093AlphaDummy080 A))).fv ∪ ((Class.cv (nb093AlphaDummy080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0083 (r : Var) :
    (nb093AlphaDummy083 r) ∈
      (((Class.cv (nb093AlphaDummy083 r))).fv ∪ ((Class.cv (nb093AlphaDummy083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0084 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((Class.cv (nb093AlphaDummy058 A))).fv ∪ ((Class.cv (nb093AlphaDummy059 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0085 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCphi (Class.cv (nb093AlphaDummy065 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
            unfold nb093AlphaDummy065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0086 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0087 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCphi (Class.cv (nb093AlphaDummy067 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy067 r) from (by
            unfold nb093AlphaDummy067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0088 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy065 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
            unfold nb093AlphaDummy065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0089 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy067 r)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy067 r) from (by
            unfold nb093AlphaDummy067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0090 (A : Class) :
    (nb093AlphaDummy065 A) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy065 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0091 (r : Var) :
    (nb093AlphaDummy067 r) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy067 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0092 (A : Class) :
    (nb093AlphaDummy065 A) ∈
      (((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy065 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0093 (r : Var) :
    (nb093AlphaDummy067 r) ∈
      (((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy067 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0094 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0095 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCphi (Class.cv (nb093AlphaDummy101 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy101 A) from (by
            unfold nb093AlphaDummy101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0096 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0097 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCphi (Class.cv (nb093AlphaDummy103 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy103 r) from (by
            unfold nb093AlphaDummy103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0098 (A : Class) :
    (nb093AlphaDummy059 A) ∈
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv ∪
        ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy101 A) from (by
            unfold nb093AlphaDummy101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0099 (r : Var) :
    (nb093AlphaDummy061 r) ∈
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv ∪
        ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy103 r) from (by
            unfold nb093AlphaDummy103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0100 (A : Class) :
    (nb093AlphaDummy101 A) ∈ (((Class.cv (nb093AlphaDummy101 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0101 (r : Var) :
    (nb093AlphaDummy103 r) ∈ (((Class.cv (nb093AlphaDummy103 r))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0102 (A : Class) :
    (nb093AlphaDummy108 A) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy108 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy108 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy108 A))).fv) :=
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

theorem nb093_support_mem_0103 (r : Var) :
    (nb093AlphaDummy110 r) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy110 r)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy110 r)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy110 r))).fv) :=
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

theorem nb093_support_mem_0104 (A : Class) :
    (nb093AlphaDummy108 A) ∈
      (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0105 (r : Var) :
    (nb093AlphaDummy110 r) ∈
      (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0106 (A : Class) :
    (nb093AlphaDummy115 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0107 (r : Var) :
    (nb093AlphaDummy118 r) ∈
      (((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0108 (A : Class) :
    (nb093AlphaDummy115 A) ∈
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0109 (r : Var) :
    (nb093AlphaDummy118 r) ∈
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0110 (A : Class) :
    (nb093AlphaDummy116 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy115 A))
            (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0111 (r : Var) :
    (nb093AlphaDummy119 r) ∈
      (((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy118 r))
            (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0112 (A : Class) :
    (nb093AlphaDummy116 A) ∈
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0113 (r : Var) :
    (nb093AlphaDummy119 r) ∈
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0114 (A : Class) :
    (nb093AlphaDummy115 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy115 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0115 (r : Var) :
    (nb093AlphaDummy118 r) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy118 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0116 (A : Class) :
    (nb093AlphaDummy115 A) ∈
      (((Class.cv (nb093AlphaDummy115 A))).fv ∪ ((Class.cv (nb093AlphaDummy115 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0117 (r : Var) :
    (nb093AlphaDummy118 r) ∈
      (((Class.cv (nb093AlphaDummy118 r))).fv ∪ ((Class.cv (nb093AlphaDummy118 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0118 (A : Class) :
    (nb093AlphaDummy116 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy115 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0119 (r : Var) :
    (nb093AlphaDummy119 r) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy118 r)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0120 (A : Class) :
    (nb093AlphaDummy116 A) ∈
      (((Class.cv (nb093AlphaDummy116 A))).fv ∪ ((Class.cv (nb093AlphaDummy116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0121 (r : Var) :
    (nb093AlphaDummy119 r) ∈
      (((Class.cv (nb093AlphaDummy119 r))).fv ∪ ((Class.cv (nb093AlphaDummy119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0122 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0123 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCphi (Class.cv (nb093AlphaDummy101 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
            unfold nb093AlphaDummy101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0124 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((Class.cv (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0125 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCphi (Class.cv (nb093AlphaDummy103 r)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy103 r) from (by
            unfold nb093AlphaDummy103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0126 (A : Class) :
    (nb093AlphaDummy058 A) ∈
      (((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy101 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
            unfold nb093AlphaDummy101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0127 (r : Var) :
    (nb093AlphaDummy060 r) ∈
      (((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCun (synCphi (Class.cv (nb093AlphaDummy103 r)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy103 r) from (by
            unfold nb093AlphaDummy103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0128 (A : Class) :
    (nb093AlphaDummy101 A) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy101 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0129 (r : Var) :
    (nb093AlphaDummy103 r) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy103 r))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0130 (A : Class) :
    (nb093AlphaDummy101 A) ∈
      (((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy101 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0131 (r : Var) :
    (nb093AlphaDummy103 r) ∈
      (((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy103 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0132 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv ∪
        ((synCcnv (Class.cv (nb093AlphaDummy001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0133 (r : Var) :
    r ∈ (((synCcnv (Class.cv r))).fv ∪ ((synCcnv (Class.cv r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0134 (A : Class) :
    (nb093AlphaDummy001 A) ∈
      (({(nb093AlphaDummy058 A)} : Finset Var) ∪ ({(nb093AlphaDummy059 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy059 A)) (Class.cv (nb093AlphaDummy001 A))
            (Class.cv (nb093AlphaDummy058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0135 (r : Var) :
    r ∈
      (({(nb093AlphaDummy060 r)} : Finset Var) ∪ ({(nb093AlphaDummy061 r)} : Finset Var) ∪
        ((synWbr (Class.cv (nb093AlphaDummy061 r)) (Class.cv r)
            (Class.cv (nb093AlphaDummy060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0136 (A : Class) :
    (nb093AlphaDummy001 A) ∈ (((Class.cv (nb093AlphaDummy001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0137 (r : Var) : r ∈ (((Class.cv r)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0138 (A : Class) :
    (nb093AlphaDummy045 A) ∈ (((Class.cv (nb093AlphaDummy045 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0139 (r : Var) (d : Var) :
    (nb093AlphaDummy047 r d) ∈ (((Class.cv (nb093AlphaDummy047 r d))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0140 (A : Class) :
    (nb093AlphaDummy136 A) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy136 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy136 A)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy136 A))).fv) :=
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

theorem nb093_support_mem_0141 (r : Var) (d : Var) :
    (nb093AlphaDummy138 r d) ∈
      (((Wff.classMem (Class.cv (nb093AlphaDummy138 r d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb093AlphaDummy138 r d)) (synC1c))).fv ∪
        ((Class.cv (nb093AlphaDummy138 r d))).fv) :=
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

theorem nb093_support_mem_0142 (A : Class) :
    (nb093AlphaDummy136 A) ∈
      (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0143 (r : Var) (d : Var) :
    (nb093AlphaDummy138 r d) ∈
      (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0144 (A : Class) :
    (nb093AlphaDummy143 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0145 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ∈
      (((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0146 (A : Class) :
    (nb093AlphaDummy143 A) ∈
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0147 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ∈
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0148 (A : Class) :
    (nb093AlphaDummy144 A) ∈
      (((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy143 A))
            (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0149 (r : Var) (d : Var) :
    (nb093AlphaDummy147 r d) ∈
      (((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv ∪
        ((synCnin (Class.cv (nb093AlphaDummy146 r d))
            (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0150 (A : Class) :
    (nb093AlphaDummy144 A) ∈
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0151 (r : Var) (d : Var) :
    (nb093AlphaDummy147 r d) ∈
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0152 (A : Class) :
    (nb093AlphaDummy143 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy143 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0153 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy146 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0154 (A : Class) :
    (nb093AlphaDummy143 A) ∈
      (((Class.cv (nb093AlphaDummy143 A))).fv ∪ ((Class.cv (nb093AlphaDummy143 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0155 (r : Var) (d : Var) :
    (nb093AlphaDummy146 r d) ∈
      (((Class.cv (nb093AlphaDummy146 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy146 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0156 (A : Class) :
    (nb093AlphaDummy144 A) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy143 A)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0157 (r : Var) (d : Var) :
    (nb093AlphaDummy147 r d) ∈
      (((synCcompl (Class.cv (nb093AlphaDummy146 r d)))).fv ∪
        ((synCcompl (Class.cv (nb093AlphaDummy147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0158 (A : Class) :
    (nb093AlphaDummy144 A) ∈
      (((Class.cv (nb093AlphaDummy144 A))).fv ∪ ((Class.cv (nb093AlphaDummy144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0159 (r : Var) (d : Var) :
    (nb093AlphaDummy147 r d) ∈
      (((Class.cv (nb093AlphaDummy147 r d))).fv ∪
        ((Class.cv (nb093AlphaDummy147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0160 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
        ((Class.cv (nb093AlphaDummy000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0161 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((synCcompl (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
                (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCphi (Class.cv (nb093AlphaDummy045 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy044 A)
              (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy045 A) from (by
            unfold nb093AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0162 (r : Var) (d : Var) :
    d ∈ (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0163 (r : Var) (d : Var) :
    d ∈
      (((synCcompl (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
                (synCdif (Class.cv r) (synCcnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCphi (Class.cv (nb093AlphaDummy047 r d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb093AlphaDummy046 r d)
              (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093AlphaDummy046 r d) from (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093AlphaDummy047 r d) from (by
            unfold nb093AlphaDummy047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0164 (A : Class) :
    (nb093AlphaDummy000 A) ∈
      (((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy044 A)
            (synWrex (nb093AlphaDummy045 A) (Class.cv (nb093AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCun (synCphi (Class.cv (nb093AlphaDummy045 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy045 A) from (by
            unfold nb093AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0165 (r : Var) (d : Var) :
    d ∈
      (((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb093AlphaDummy046 r d)
            (synWrex (nb093AlphaDummy047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093AlphaDummy046 r d) from (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093AlphaDummy047 r d) from (by
            unfold nb093AlphaDummy047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0166 (A : Class) :
    (nb093AlphaDummy045 A) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy045 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0167 (r : Var) (d : Var) :
    (nb093AlphaDummy047 r d) ∈
      (((synCcompl (synCphi (Class.cv (nb093AlphaDummy047 r d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0168 (A : Class) :
    (nb093AlphaDummy045 A) ∈
      (((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy045 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0169 (r : Var) (d : Var) :
    (nb093AlphaDummy047 r d) ∈
      (((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv ∪
        ((synCphi (Class.cv (nb093AlphaDummy047 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_focused_notmem_0000 (A : Class) : (nb093AlphaDummy004 A) ∉ A.fv :=
  by
  change
    freshVar
        (((synClntpc A)).fv ∪ ((synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A)
              (synWbr (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (synCfound) (Class.cv (nb093AlphaDummy000 A))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0000 (A : Class) :
    (nb093AlphaDummy004 A) ∉ ((synClntpc A)).fv := by
  simpa only [nb093AlphaDummy004, fv_syn_clntpc] using (nb093_focused_notmem_0000 A)

theorem nb093_focused_notmem_0001 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy005 A r d) ∉ A.fv :=
  by
  change
    freshVar
        (((synClntpc A)).fv ∪ ((synCopab r d
              (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                (Class.cv d)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0001 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy005 A r d) ∉ ((synClntpc A)).fv := by
  simpa only [nb093AlphaDummy005, fv_syn_clntpc] using
    (nb093_focused_notmem_0001 A r d)

theorem nb093_focused_notmem_0002 (A : Class) : (nb093AlphaDummy002 A) ∉ A.fv :=
  by
  change
    freshVar
        (((synCnin (synClntpc A)
              (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A) (synWbr
                  (synCdif (Class.cv (nb093AlphaDummy001 A))
                    (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                  (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv ∪
          ((synCnin (synClntpc A)
              (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A) (synWbr
                  (synCdif (Class.cv (nb093AlphaDummy001 A))
                    (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                  (synCfound) (Class.cv (nb093AlphaDummy000 A)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synClntpc A)
      (synCopab (nb093AlphaDummy001 A) (nb093AlphaDummy000 A) (synWbr
          (synCdif (Class.cv (nb093AlphaDummy001 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))
          (synCfound) (Class.cv (nb093AlphaDummy000 A))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0002 (A : Class) :
    (nb093AlphaDummy002 A) ∉ ((synClntpc A)).fv := by
  simpa only [nb093AlphaDummy002, fv_syn_clntpc] using (nb093_focused_notmem_0002 A)

theorem nb093_focused_notmem_0003 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy003 A r d) ∉ A.fv :=
  by
  change
    freshVar
        (((synCnin (synClntpc A) (synCopab r d
                (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                  (Class.cv d))))).fv ∪ ((synCnin (synClntpc A) (synCopab r d
                (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
                  (Class.cv d))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synClntpc A)
      (synCopab r d (synWbr (synCdif (Class.cv r) (synCcnv (Class.cv r))) (synCfound)
          (Class.cv d)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0003 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy003 A r d) ∉ ((synClntpc A)).fv := by
  simpa only [nb093AlphaDummy003, fv_syn_clntpc] using
    (nb093_focused_notmem_0003 A r d)

theorem nb093_compact_envfresh_0000 (A : Class) (r : Var) (d : Var) :
    TEnvFresh
      [((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      ((synClntpc A)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb093AlphaDummy004 A) (nb093AlphaDummy005 A r d)
      (nb093_wpp_notmem_0000 A) (nb093_wpp_notmem_0001 A r d)
      (TEnvFresh.consFresh (nb093AlphaDummy002 A) (nb093AlphaDummy003 A r d)
        (nb093_wpp_notmem_0002 A) (nb093_wpp_notmem_0003 A r d)
        (TEnvFresh.nil ((synClntpc A)).fv)))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C093M3Part002Stage2`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_wpp_refl_0000`. -/
@[expose]
noncomputable def nb093WppRefl0000 (A : Class) (r : Var) (d : Var) :
    TReflOn
      [((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      ((synClntpc A)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0000 A r d)

theorem nb093_compact_fv_empty_0020 (A : Class) :
    (nb093AlphaDummy000 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0021 (d : Var) : d ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0022 (A : Class) :
    (nb093AlphaDummy001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0024 (A : Class) :
    (nb093AlphaDummy006 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0025 (r : Var) (d : Var) :
    (nb093AlphaDummy007 r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0026 (A : Class) :
    (nb093AlphaDummy004 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0027 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy005 A r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0028 (A : Class) :
    (nb093AlphaDummy002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0029 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy003 A r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
