/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C070C001Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4C070C001Part002Stage1`. -/


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

theorem nb070_support_mem_0011 (x : Var) :
    x ∈ (((synCpw (Class.cv x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0012 (A : Class) :
    (nb070AlphaDummy001 A) ∈ (((Class.cv (nb070AlphaDummy001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0013 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0014 (A : Class) :
    (nb070AlphaDummy001 A) ∈
      (((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy018 A))
            (Class.cv (nb070AlphaDummy001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0015 (x : Var) :
    x ∈
      (((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy019 x)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0016 (A : Class) :
    (nb070AlphaDummy001 A) ∈
      (((Class.cv (nb070AlphaDummy018 A))).fv ∪ ((Class.cv (nb070AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0017 (x : Var) :
    x ∈ (((Class.cv (nb070AlphaDummy019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0018 (A : Class) :
    (nb070AlphaDummy009 A) ∈
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0019 (A : Class) :
    (nb070AlphaDummy009 A) ∈
      (((synCcompl (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCphi (Class.cv (nb070AlphaDummy025 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0020 (x : Var) :
    (nb070AlphaDummy011 x) ∈
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0021 (x : Var) :
    (nb070AlphaDummy011 x) ∈
      (((synCcompl (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCphi (Class.cv (nb070AlphaDummy027 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0022 (A : Class) :
    (nb070AlphaDummy009 A) ∈
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv ∪
        ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCphi (Class.cv (nb070AlphaDummy025 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0023 (x : Var) :
    (nb070AlphaDummy011 x) ∈
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv ∪
        ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCphi (Class.cv (nb070AlphaDummy027 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0024 (A : Class) :
    (nb070AlphaDummy025 A) ∈ (((Class.cv (nb070AlphaDummy025 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0025 (x : Var) :
    (nb070AlphaDummy027 x) ∈ (((Class.cv (nb070AlphaDummy027 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0026 (A : Class) :
    (nb070AlphaDummy032 A) ∈
      (((Wff.classMem (Class.cv (nb070AlphaDummy032 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy032 A)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy032 A))).fv) :=
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

theorem nb070_support_mem_0027 (x : Var) :
    (nb070AlphaDummy034 x) ∈
      (((Wff.classMem (Class.cv (nb070AlphaDummy034 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb070AlphaDummy034 x)) (synC1c))).fv ∪
        ((Class.cv (nb070AlphaDummy034 x))).fv) :=
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

theorem nb070_support_mem_0028 (A : Class) :
    (nb070AlphaDummy032 A) ∈
      (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0029 (x : Var) :
    (nb070AlphaDummy034 x) ∈
      (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0030 (A : Class) :
    (nb070AlphaDummy039 A) ∈
      (((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0031 (x : Var) :
    (nb070AlphaDummy042 x) ∈
      (((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0032 (A : Class) :
    (nb070AlphaDummy039 A) ∈
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0033 (x : Var) :
    (nb070AlphaDummy042 x) ∈
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0034 (A : Class) :
    (nb070AlphaDummy040 A) ∈
      (((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0035 (x : Var) :
    (nb070AlphaDummy043 x) ∈
      (((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv ∪
        ((synCnin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0036 (A : Class) :
    (nb070AlphaDummy040 A) ∈
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0037 (x : Var) :
    (nb070AlphaDummy043 x) ∈
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0038 (A : Class) :
    (nb070AlphaDummy039 A) ∈
      (((synCcompl (Class.cv (nb070AlphaDummy039 A)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0039 (x : Var) :
    (nb070AlphaDummy042 x) ∈
      (((synCcompl (Class.cv (nb070AlphaDummy042 x)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0040 (A : Class) :
    (nb070AlphaDummy039 A) ∈
      (((Class.cv (nb070AlphaDummy039 A))).fv ∪ ((Class.cv (nb070AlphaDummy039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0041 (x : Var) :
    (nb070AlphaDummy042 x) ∈
      (((Class.cv (nb070AlphaDummy042 x))).fv ∪ ((Class.cv (nb070AlphaDummy042 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0042 (A : Class) :
    (nb070AlphaDummy040 A) ∈
      (((synCcompl (Class.cv (nb070AlphaDummy039 A)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0043 (x : Var) :
    (nb070AlphaDummy043 x) ∈
      (((synCcompl (Class.cv (nb070AlphaDummy042 x)))).fv ∪
        ((synCcompl (Class.cv (nb070AlphaDummy043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0044 (A : Class) :
    (nb070AlphaDummy040 A) ∈
      (((Class.cv (nb070AlphaDummy040 A))).fv ∪ ((Class.cv (nb070AlphaDummy040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0045 (x : Var) :
    (nb070AlphaDummy043 x) ∈
      (((Class.cv (nb070AlphaDummy043 x))).fv ∪ ((Class.cv (nb070AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0046 (A : Class) :
    (nb070AlphaDummy008 A) ∈
      (((Class.cv (nb070AlphaDummy009 A))).fv ∪ ((Class.cv (nb070AlphaDummy008 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0047 (A : Class) :
    (nb070AlphaDummy008 A) ∈
      (((synCcompl (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy009 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCphi (Class.cv (nb070AlphaDummy025 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0048 (x : Var) :
    (nb070AlphaDummy010 x) ∈
      (((Class.cv (nb070AlphaDummy011 x))).fv ∪ ((Class.cv (nb070AlphaDummy010 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0049 (x : Var) :
    (nb070AlphaDummy010 x) ∈
      (((synCcompl (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy011 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCphi (Class.cv (nb070AlphaDummy027 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0050 (A : Class) :
    (nb070AlphaDummy008 A) ∈
      (((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0051 (x : Var) :
    (nb070AlphaDummy010 x) ∈
      (((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0052 (A : Class) :
    (nb070AlphaDummy025 A) ∈
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy025 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0053 (x : Var) :
    (nb070AlphaDummy027 x) ∈
      (((synCcompl (synCphi (Class.cv (nb070AlphaDummy027 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0054 (A : Class) :
    (nb070AlphaDummy025 A) ∈
      (((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy025 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0055 (x : Var) :
    (nb070AlphaDummy027 x) ∈
      (((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv ∪
        ((synCphi (Class.cv (nb070AlphaDummy027 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0056 (A : Class) :
    (nb070AlphaDummy002 A) ∈ (((Class.cv (nb070AlphaDummy002 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0057 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy003 x A b) ∈ (((Class.cv (nb070AlphaDummy003 x A b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_compact_fv_empty_0000 (A : Class) :
    (nb070AlphaDummy000 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0000 (A : Class) : (nb070AlphaDummy000 A) ∉ ((synCncs)).fv :=
  by simpa only [nb070AlphaDummy000, fv_syn_cncs] using (nb070_compact_fv_empty_0000 A)

theorem nb070_compact_fv_empty_0001 (b : Var) : b ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0001 (b : Var) : b ∉ ((synCncs)).fv := by
  simpa only [fv_syn_cncs] using (nb070_compact_fv_empty_0001 b)

theorem nb070_compact_fv_empty_0002 (A : Class) :
    (nb070AlphaDummy002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0002 (A : Class) : (nb070AlphaDummy002 A) ∉ ((synCncs)).fv :=
  by simpa only [nb070AlphaDummy002, fv_syn_cncs] using (nb070_compact_fv_empty_0002 A)

theorem nb070_compact_fv_empty_0003 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy003 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0003 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy003 x A b) ∉ ((synCncs)).fv := by
  simpa only [nb070AlphaDummy003, fv_syn_cncs] using
    (nb070_compact_fv_empty_0003 x A b)

theorem nb070_compact_fv_empty_0004 (A : Class) :
    (nb070AlphaDummy005 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0004 (A : Class) : (nb070AlphaDummy005 A) ∉ ((synCncs)).fv :=
  by simpa only [nb070AlphaDummy005, fv_syn_cncs] using (nb070_compact_fv_empty_0004 A)

theorem nb070_compact_fv_empty_0005 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy007 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0005 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy007 x A b) ∉ ((synCncs)).fv := by
  simpa only [nb070AlphaDummy007, fv_syn_cncs] using
    (nb070_compact_fv_empty_0005 x A b)

theorem nb070_compact_fv_empty_0006 (A : Class) :
    (nb070AlphaDummy004 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0006 (A : Class) : (nb070AlphaDummy004 A) ∉ ((synCncs)).fv :=
  by simpa only [nb070AlphaDummy004, fv_syn_cncs] using (nb070_compact_fv_empty_0006 A)

theorem nb070_compact_fv_empty_0007 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy006 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0007 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy006 x A b) ∉ ((synCncs)).fv := by
  simpa only [nb070AlphaDummy006, fv_syn_cncs] using
    (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0000 (x : Var) (A : Class) (b : Var) :
    TEnvFresh
      [((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      ((synCncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070AlphaDummy000 A) b (nb070_wpp_notmem_0000 A)
      (nb070_wpp_notmem_0001 b)
      (TEnvFresh.consFresh (nb070AlphaDummy002 A) (nb070AlphaDummy003 x A b)
        (nb070_wpp_notmem_0002 A) (nb070_wpp_notmem_0003 x A b)
        (TEnvFresh.consFresh (nb070AlphaDummy005 A) (nb070AlphaDummy007 x A b)
          (nb070_wpp_notmem_0004 A) (nb070_wpp_notmem_0005 x A b)
          (TEnvFresh.consFresh (nb070AlphaDummy004 A) (nb070AlphaDummy006 x A b)
            (nb070_wpp_notmem_0006 A) (nb070_wpp_notmem_0007 x A b)
            (TEnvFresh.nil ((synCncs)).fv)))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4C070C001Part002Stage2`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_wpp_refl_0000`. -/
@[expose]
noncomputable def nb070WppRefl0000 (x : Var) (A : Class) (b : Var) :
    TReflOn
      [((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      ((synCncs)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0000 x A b)

theorem nb070_focused_notmem_0000 (A : Class) : (nb070AlphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem nb070_wpp_notmem_0008 (A : Class) : (nb070AlphaDummy001 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0000 A)

theorem nb070_wpp_notmem_0009 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem nb070_focused_notmem_0001 (A : Class) : (nb070AlphaDummy000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem nb070_wpp_notmem_0010 (A : Class) : (nb070AlphaDummy000 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0001 A)

theorem nb070_wpp_notmem_0011 (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) : b ∉ (A).fv := by
  exact dv_A_b


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4C070C001Part002Stage3`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_predicate`. -/
@[expose]
def nb070Predicate (x : Var) (A : Class) (b : Var) : Wff :=
  synWa (Wff.classMem (Class.cv b) synCncs)
    (synWrex x A (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))

theorem nb070_predicate_support (x : Var) (A : Class) (b : Var) (hx : x ∉ A.fv) :
    ∀ u, u ∈ A.fv → u ∈ (nb070Predicate x A b).fv :=
  by
  intro u hu
  rw [nb070Predicate, fv_syn_wa, Finset.mem_union]
  right
  rw [fv_syn_wrex, Finset.mem_union]
  left
  rw [Finset.mem_erase]
  exact ⟨fun equality => hx (equality ▸ hu), hu⟩

theorem nb070_support_cab (support : Finset Var) (b : Var) (predicate : Wff)
    (hb : b ∉ support) (hsub : ∀ u, u ∈ support → u ∈ predicate.fv) :
    ∀ u, u ∈ support → u ∈ (Class.cab b predicate).fv :=
  by
  intro u hu
  rw [fv_class_cab, Finset.mem_erase]
  exact ⟨fun equality => hb (equality ▸ hu), hsub u hu⟩

theorem nb070_inner_support (x : Var) (A : Class) (b : Var) (hx : x ∉ A.fv)
    (hb : b ∉ A.fv) : ∀ u, u ∈ A.fv → u ∈ (Class.cab b (nb070Predicate x A b)).fv := by
  with_reducible
    exact
      (nb070_support_cab A.fv b (nb070Predicate x A b) hb (nb070_predicate_support x A b hx))

theorem nb070_outer_support (x : Var) (A : Class) (b v : Var) (hx : x ∉ A.fv)
    (hb : b ∉ A.fv) (hv : v ∉ A.fv) :
    ∀ u,
      u ∈ A.fv →
        u ∈
          (Class.cab v (Wff.classEq (Class.cab b (nb070Predicate x A b))
                (synCsn (Class.cv v)))).fv :=
  by
  intro u hu
  rw [fv_class_cab, Finset.mem_erase]
  constructor
  · exact fun equality => hv (equality ▸ hu)
  · rw [fv_wff_classEq, Finset.mem_union]
    left
    with_reducible exact (nb070_inner_support x A b hx hb u hu)

theorem nb070_predicate_fresh (x : Var) (A : Class) (b : Var) (hx : x ∉ A.fv) :
    freshVar ({ b } ∪ (nb070Predicate x A b).fv) 0 ∉ A.fv :=
  by
  have subset : A.fv ⊆ { b } ∪ (nb070Predicate x A b).fv :=
    by
    intro u hu
    rw [Finset.mem_union]
    right
    with_reducible exact (nb070_predicate_support x A b hx u hu)
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 subset

theorem nb070_outer_fresh (x : Var) (A : Class) (b v : Var) (offset : Nat) (hx : x ∉ A.fv)
    (hb : b ∉ A.fv) (hv : v ∉ A.fv) :
    freshVar
        (Class.cab v
            (Wff.classEq (Class.cab b (nb070Predicate x A b)) (synCsn (Class.cv v)))).fv
        offset ∉
      A.fv :=
  by
  have subset :
    A.fv ⊆
      (Class.cab v (Wff.classEq (Class.cab b (nb070Predicate x A b))
            (synCsn (Class.cv v)))).fv :=
    by
    intro u hu
    with_reducible exact (nb070_outer_support x A b v hx hb hv u hu)
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset offset subset


theorem nb070_focused_notmem_0002 (A : Class) : (nb070AlphaDummy002 A) ∉ A.fv :=
  by
  unfold nb070AlphaDummy002
  simpa only [nb070Predicate] using
    (nb070_predicate_fresh (nb070AlphaDummy001 A) A (nb070AlphaDummy000 A)
      (nb070_focused_notmem_0000 A))

theorem nb070_wpp_notmem_0012 (A : Class) : (nb070AlphaDummy002 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0002 A)

theorem nb070_focused_notmem_0003 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) :
    (nb070AlphaDummy003 x A b) ∉ A.fv :=
  by
  unfold nb070AlphaDummy003
  simpa only [nb070Predicate] using (nb070_predicate_fresh x A b dv_A_x)

theorem nb070_wpp_notmem_0013 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) :
    (nb070AlphaDummy003 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0003 x A b dv_A_x)

theorem nb070_focused_notmem_0004 (A : Class) : (nb070AlphaDummy005 A) ∉ A.fv :=
  by
  unfold nb070AlphaDummy005
  simpa only [nb070Predicate] using
    (nb070_outer_fresh (nb070AlphaDummy001 A) A (nb070AlphaDummy000 A)
      (nb070AlphaDummy002 A) 1 (nb070_focused_notmem_0000 A)
      (nb070_focused_notmem_0001 A) (nb070_focused_notmem_0002 A))

theorem nb070_wpp_notmem_0014 (A : Class) : (nb070AlphaDummy005 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0004 A)

theorem nb070_focused_notmem_0005 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070AlphaDummy007 x A b) ∉ A.fv :=
  by
  unfold nb070AlphaDummy007
  simpa only [nb070Predicate] using
    (nb070_outer_fresh x A b (nb070AlphaDummy003 x A b) 1 dv_A_x dv_A_b
      (nb070_focused_notmem_0003 x A b dv_A_x))

theorem nb070_wpp_notmem_0015 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070AlphaDummy007 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0005 x A b dv_A_b dv_A_x)

theorem nb070_focused_notmem_0006 (A : Class) : (nb070AlphaDummy004 A) ∉ A.fv :=
  by
  unfold nb070AlphaDummy004
  simpa only [nb070Predicate] using
    (nb070_outer_fresh (nb070AlphaDummy001 A) A (nb070AlphaDummy000 A)
      (nb070AlphaDummy002 A) 0 (nb070_focused_notmem_0000 A)
      (nb070_focused_notmem_0001 A) (nb070_focused_notmem_0002 A))

theorem nb070_wpp_notmem_0016 (A : Class) : (nb070AlphaDummy004 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0006 A)

theorem nb070_focused_notmem_0007 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070AlphaDummy006 x A b) ∉ A.fv :=
  by
  unfold nb070AlphaDummy006
  simpa only [nb070Predicate] using
    (nb070_outer_fresh x A b (nb070AlphaDummy003 x A b) 0 dv_A_x dv_A_b
      (nb070_focused_notmem_0003 x A b dv_A_x))

theorem nb070_wpp_notmem_0017 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070AlphaDummy006 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0007 x A b dv_A_b dv_A_x)

theorem nb070_compact_envfresh_0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) :
    TEnvFresh
      [((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (A).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070AlphaDummy001 A) x (nb070_wpp_notmem_0008 A)
      (nb070_wpp_notmem_0009 x A dv_A_x)
      (TEnvFresh.consFresh (nb070AlphaDummy000 A) b (nb070_wpp_notmem_0010 A)
        (nb070_wpp_notmem_0011 A b dv_A_b)
        (TEnvFresh.consFresh (nb070AlphaDummy002 A) (nb070AlphaDummy003 x A b)
          (nb070_wpp_notmem_0012 A) (nb070_wpp_notmem_0013 x A b dv_A_x)
          (TEnvFresh.consFresh (nb070AlphaDummy005 A) (nb070AlphaDummy007 x A b)
            (nb070_wpp_notmem_0014 A) (nb070_wpp_notmem_0015 x A b dv_A_b dv_A_x)
            (TEnvFresh.consFresh (nb070AlphaDummy004 A) (nb070AlphaDummy006 x A b)
              (nb070_wpp_notmem_0016 A) (nb070_wpp_notmem_0017 x A b dv_A_b dv_A_x)
              (TEnvFresh.nil (A).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4C070C001Part002Stage4`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_wpp_refl_0001`. -/
@[expose]
noncomputable def nb070WppRefl0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) :
    TReflOn
      [((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (A).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0001 x A b dv_A_b dv_A_x)

theorem nb070_compact_fv_empty_0014 (A : Class) :
    (nb070AlphaDummy009 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0015 (x : Var) :
    (nb070AlphaDummy011 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0016 (A : Class) :
    (nb070AlphaDummy008 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0017 (x : Var) :
    (nb070AlphaDummy010 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0018 (A : Class) :
    (nb070AlphaDummy001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0019 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
