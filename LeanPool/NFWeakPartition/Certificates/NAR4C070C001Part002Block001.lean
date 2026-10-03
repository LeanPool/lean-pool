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
    x ∈ (((syn_cpw (Class.cv x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0012 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈ (((Class.cv (nb070_alpha_dummy_001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0013 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0014 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv) :=
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
      (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0016 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈
      (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0017 (x : Var) :
    x ∈ (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0018 (A : Class) :
    (nb070_alpha_dummy_009 A) ∈
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0019 (A : Class) :
    (nb070_alpha_dummy_009 A) ∈
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb070_alpha_dummy_011 x) ∈
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0021 (x : Var) :
    (nb070_alpha_dummy_011 x) ∈
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb070_alpha_dummy_009 A) ∈
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv) :=
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
    (nb070_alpha_dummy_011 x) ∈
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv) :=
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
    (nb070_alpha_dummy_025 A) ∈ (((Class.cv (nb070_alpha_dummy_025 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0025 (x : Var) :
    (nb070_alpha_dummy_027 x) ∈ (((Class.cv (nb070_alpha_dummy_027 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0026 (A : Class) :
    (nb070_alpha_dummy_032 A) ∈
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_032 A))).fv) :=
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
    (nb070_alpha_dummy_034 x) ∈
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_034 x))).fv) :=
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
    (nb070_alpha_dummy_032 A) ∈
      (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0029 (x : Var) :
    (nb070_alpha_dummy_034 x) ∈
      (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0030 (A : Class) :
    (nb070_alpha_dummy_039 A) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0031 (x : Var) :
    (nb070_alpha_dummy_042 x) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0032 (A : Class) :
    (nb070_alpha_dummy_039 A) ∈
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0033 (x : Var) :
    (nb070_alpha_dummy_042 x) ∈
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0034 (A : Class) :
    (nb070_alpha_dummy_040 A) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0035 (x : Var) :
    (nb070_alpha_dummy_043 x) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0036 (A : Class) :
    (nb070_alpha_dummy_040 A) ∈
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0037 (x : Var) :
    (nb070_alpha_dummy_043 x) ∈
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0038 (A : Class) :
    (nb070_alpha_dummy_039 A) ∈
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0039 (x : Var) :
    (nb070_alpha_dummy_042 x) ∈
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0040 (A : Class) :
    (nb070_alpha_dummy_039 A) ∈
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0041 (x : Var) :
    (nb070_alpha_dummy_042 x) ∈
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_042 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0042 (A : Class) :
    (nb070_alpha_dummy_040 A) ∈
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0043 (x : Var) :
    (nb070_alpha_dummy_043 x) ∈
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0044 (A : Class) :
    (nb070_alpha_dummy_040 A) ∈
      (((Class.cv (nb070_alpha_dummy_040 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0045 (x : Var) :
    (nb070_alpha_dummy_043 x) ∈
      (((Class.cv (nb070_alpha_dummy_043 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0046 (A : Class) :
    (nb070_alpha_dummy_008 A) ∈
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0047 (A : Class) :
    (nb070_alpha_dummy_008 A) ∈
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb070_alpha_dummy_010 x) ∈
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0049 (x : Var) :
    (nb070_alpha_dummy_010 x) ∈
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb070_alpha_dummy_008 A) ∈
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb070_alpha_dummy_010 x) ∈
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb070_alpha_dummy_025 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0053 (x : Var) :
    (nb070_alpha_dummy_027 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0054 (A : Class) :
    (nb070_alpha_dummy_025 A) ∈
      (((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0055 (x : Var) :
    (nb070_alpha_dummy_027 x) ∈
      (((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0056 (A : Class) :
    (nb070_alpha_dummy_002 A) ∈ (((Class.cv (nb070_alpha_dummy_002 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0057 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_003 x A b) ∈ (((Class.cv (nb070_alpha_dummy_003 x A b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_compact_fv_empty_0000 (A : Class) :
    (nb070_alpha_dummy_000 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0000 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_cncs)).fv :=
  by simpa only [nb070_alpha_dummy_000, fv_syn_cncs] using (nb070_compact_fv_empty_0000 A)

theorem nb070_compact_fv_empty_0001 (b : Var) : b ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0001 (b : Var) : b ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb070_compact_fv_empty_0001 b)

theorem nb070_compact_fv_empty_0002 (A : Class) :
    (nb070_alpha_dummy_002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0002 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_cncs)).fv :=
  by simpa only [nb070_alpha_dummy_002, fv_syn_cncs] using (nb070_compact_fv_empty_0002 A)

theorem nb070_compact_fv_empty_0003 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_003 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0003 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_003 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_cncs] using
    (nb070_compact_fv_empty_0003 x A b)

theorem nb070_compact_fv_empty_0004 (A : Class) :
    (nb070_alpha_dummy_005 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0004 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_cncs)).fv :=
  by simpa only [nb070_alpha_dummy_005, fv_syn_cncs] using (nb070_compact_fv_empty_0004 A)

theorem nb070_compact_fv_empty_0005 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_007 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0005 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_007 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_cncs] using
    (nb070_compact_fv_empty_0005 x A b)

theorem nb070_compact_fv_empty_0006 (A : Class) :
    (nb070_alpha_dummy_004 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0006 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_cncs)).fv :=
  by simpa only [nb070_alpha_dummy_004, fv_syn_cncs] using (nb070_compact_fv_empty_0006 A)

theorem nb070_compact_fv_empty_0007 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_006 x A b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0007 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_006 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_cncs] using
    (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0000 (x : Var) (A : Class) (b : Var) :
    TEnvFresh
      [((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      ((syn_cncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0000 A)
      (nb070_wpp_notmem_0001 b)
      (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b)
        (nb070_wpp_notmem_0002 A) (nb070_wpp_notmem_0003 x A b)
        (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b)
          (nb070_wpp_notmem_0004 A) (nb070_wpp_notmem_0005 x A b)
          (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b)
            (nb070_wpp_notmem_0006 A) (nb070_wpp_notmem_0007 x A b)
            (TEnvFresh.nil ((syn_cncs)).fv)))))


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

@[expose]
noncomputable def nb070_wpp_refl_0000 (x : Var) (A : Class) (b : Var) :
    TReflOn
      [((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0000 x A b)

theorem nb070_focused_notmem_0000 (A : Class) : (nb070_alpha_dummy_001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem nb070_wpp_notmem_0008 (A : Class) : (nb070_alpha_dummy_001 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0000 A)

theorem nb070_wpp_notmem_0009 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem nb070_focused_notmem_0001 (A : Class) : (nb070_alpha_dummy_000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem nb070_wpp_notmem_0010 (A : Class) : (nb070_alpha_dummy_000 A) ∉ (A).fv := by
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

@[expose]
def nb070_predicate (x : Var) (A : Class) (b : Var) : Wff :=
  syn_wa (Wff.classMem (Class.cv b) syn_cncs)
    (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))

theorem nb070_predicate_support (x : Var) (A : Class) (b : Var) (hx : x ∉ A.fv) :
    ∀ u, u ∈ A.fv → u ∈ (nb070_predicate x A b).fv :=
  by
  intro u hu
  rw [nb070_predicate, fv_syn_wa, Finset.mem_union]
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
    (hb : b ∉ A.fv) : ∀ u, u ∈ A.fv → u ∈ (Class.cab b (nb070_predicate x A b)).fv := by
  with_reducible
    exact
      (nb070_support_cab A.fv b (nb070_predicate x A b) hb (nb070_predicate_support x A b hx))

theorem nb070_outer_support (x : Var) (A : Class) (b v : Var) (hx : x ∉ A.fv)
    (hb : b ∉ A.fv) (hv : v ∉ A.fv) :
    ∀ u,
      u ∈ A.fv →
        u ∈
          (Class.cab v (Wff.classEq (Class.cab b (nb070_predicate x A b))
                (syn_csn (Class.cv v)))).fv :=
  by
  intro u hu
  rw [fv_class_cab, Finset.mem_erase]
  constructor
  · exact fun equality => hv (equality ▸ hu)
  · rw [fv_wff_classEq, Finset.mem_union]
    left
    with_reducible exact (nb070_inner_support x A b hx hb u hu)

theorem nb070_predicate_fresh (x : Var) (A : Class) (b : Var) (hx : x ∉ A.fv) :
    freshVar ({ b } ∪ (nb070_predicate x A b).fv) 0 ∉ A.fv :=
  by
  have subset : A.fv ⊆ { b } ∪ (nb070_predicate x A b).fv :=
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
            (Wff.classEq (Class.cab b (nb070_predicate x A b)) (syn_csn (Class.cv v)))).fv
        offset ∉
      A.fv :=
  by
  have subset :
    A.fv ⊆
      (Class.cab v (Wff.classEq (Class.cab b (nb070_predicate x A b))
            (syn_csn (Class.cv v)))).fv :=
    by
    intro u hu
    with_reducible exact (nb070_outer_support x A b v hx hb hv u hu)
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset offset subset


theorem nb070_focused_notmem_0002 (A : Class) : (nb070_alpha_dummy_002 A) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_002
  simpa only [nb070_predicate] using
    (nb070_predicate_fresh (nb070_alpha_dummy_001 A) A (nb070_alpha_dummy_000 A)
      (nb070_focused_notmem_0000 A))

theorem nb070_wpp_notmem_0012 (A : Class) : (nb070_alpha_dummy_002 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0002 A)

theorem nb070_focused_notmem_0003 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) :
    (nb070_alpha_dummy_003 x A b) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_003
  simpa only [nb070_predicate] using (nb070_predicate_fresh x A b dv_A_x)

theorem nb070_wpp_notmem_0013 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) :
    (nb070_alpha_dummy_003 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0003 x A b dv_A_x)

theorem nb070_focused_notmem_0004 (A : Class) : (nb070_alpha_dummy_005 A) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_005
  simpa only [nb070_predicate] using
    (nb070_outer_fresh (nb070_alpha_dummy_001 A) A (nb070_alpha_dummy_000 A)
      (nb070_alpha_dummy_002 A) 1 (nb070_focused_notmem_0000 A)
      (nb070_focused_notmem_0001 A) (nb070_focused_notmem_0002 A))

theorem nb070_wpp_notmem_0014 (A : Class) : (nb070_alpha_dummy_005 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0004 A)

theorem nb070_focused_notmem_0005 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_007 x A b) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_007
  simpa only [nb070_predicate] using
    (nb070_outer_fresh x A b (nb070_alpha_dummy_003 x A b) 1 dv_A_x dv_A_b
      (nb070_focused_notmem_0003 x A b dv_A_x))

theorem nb070_wpp_notmem_0015 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_007 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0005 x A b dv_A_b dv_A_x)

theorem nb070_focused_notmem_0006 (A : Class) : (nb070_alpha_dummy_004 A) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_004
  simpa only [nb070_predicate] using
    (nb070_outer_fresh (nb070_alpha_dummy_001 A) A (nb070_alpha_dummy_000 A)
      (nb070_alpha_dummy_002 A) 0 (nb070_focused_notmem_0000 A)
      (nb070_focused_notmem_0001 A) (nb070_focused_notmem_0002 A))

theorem nb070_wpp_notmem_0016 (A : Class) : (nb070_alpha_dummy_004 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0006 A)

theorem nb070_focused_notmem_0007 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_006 x A b) ∉ A.fv :=
  by
  unfold nb070_alpha_dummy_006
  simpa only [nb070_predicate] using
    (nb070_outer_fresh x A b (nb070_alpha_dummy_003 x A b) 0 dv_A_x dv_A_b
      (nb070_focused_notmem_0003 x A b dv_A_x))

theorem nb070_wpp_notmem_0017 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_006 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0007 x A b dv_A_b dv_A_x)

theorem nb070_compact_envfresh_0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) :
    TEnvFresh
      [((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (A).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0008 A)
      (nb070_wpp_notmem_0009 x A dv_A_x)
      (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0010 A)
        (nb070_wpp_notmem_0011 A b dv_A_b)
        (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b)
          (nb070_wpp_notmem_0012 A) (nb070_wpp_notmem_0013 x A b dv_A_x)
          (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b)
            (nb070_wpp_notmem_0014 A) (nb070_wpp_notmem_0015 x A b dv_A_b dv_A_x)
            (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b)
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

@[expose]
noncomputable def nb070_wpp_refl_0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) :
    TReflOn
      [((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (A).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0001 x A b dv_A_b dv_A_x)

theorem nb070_compact_fv_empty_0014 (A : Class) :
    (nb070_alpha_dummy_009 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0015 (x : Var) :
    (nb070_alpha_dummy_011 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0016 (A : Class) :
    (nb070_alpha_dummy_008 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0017 (x : Var) :
    (nb070_alpha_dummy_010 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0018 (A : Class) :
    (nb070_alpha_dummy_001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb070_compact_fv_empty_0019 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
