/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C059C001Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4C059C001Part002Stage1`. -/


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

theorem nb059_support_mem_0030 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ∈
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0031 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ∈
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0032 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0033 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ∈
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_035 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0034 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_033 R S_cls) ∈
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0035 (R : Class) (a : Var) :
    (nb059_alpha_dummy_036 R a) ∈
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0036 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_033 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0037 (R : Class) (a : Var) :
    (nb059_alpha_dummy_036 R a) ∈
      (((Class.cv (nb059_alpha_dummy_036 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0038 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_013 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0039 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_013 R S_cls) ∈
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls)
              (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_014 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_013 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0040 (R : Class) (a : Var) :
    (nb059_alpha_dummy_015 R a) ∈
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0041 (R : Class) (a : Var) :
    (nb059_alpha_dummy_015 R a) ∈
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0042 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_013 R S_cls) ∈
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_017 R S_cls)
            (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0043 (R : Class) (a : Var) :
    (nb059_alpha_dummy_015 R a) ∈
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0044 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_018 R S_cls) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0045 (R : Class) (a : Var) :
    (nb059_alpha_dummy_020 R a) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0046 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_018 R S_cls) ∈
      (((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0047 (R : Class) (a : Var) :
    (nb059_alpha_dummy_020 R a) ∈
      (((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_focused_notmem_0000 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_007 R S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0000 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_007 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0000 R S_cls)

theorem nb059_focused_notmem_0001 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_008 S_cls a) ∉ S_cls.fv :=
  by
  change freshVar ((S_cls).fv ∪ ((Class.cv a)).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0001 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_008 S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0001 S_cls a)

theorem nb059_focused_notmem_0002 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_005 R S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
          ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb059_wpp_notmem_0002 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_005 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0002 R S_cls)

theorem nb059_focused_notmem_0003 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_006 S_cls a) ∉ S_cls.fv :=
  by
  change
    freshVar (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) 0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls (Class.cv a)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb059_wpp_notmem_0003 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_006 S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0003 S_cls a)

theorem nb059_focused_notmem_0004 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∉ S_cls.fv :=
  by
  change freshVar ((S_cls).fv ∪ (R).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0004 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0004 R S_cls)

theorem nb059_wpp_notmem_0005 (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) :
    a ∉ (S_cls).fv := by exact dv_S_a

theorem nb059_focused_notmem_0005 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_002 R S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cab (nb059_alpha_dummy_000 R S_cls)
            (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
                (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb059_alpha_dummy_000 R S_cls)
      (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
        (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb059_focused_notmem_0004 R S_cls)) (h_eq ▸ hu)
  · rw [fv_syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
        (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))]
    rw [Finset.mem_union]
    left
    exact hu

theorem nb059_wpp_notmem_0006 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_002 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0005 R S_cls)

theorem nb059_focused_notmem_0006 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_004 R S_cls a) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
              (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab a
      (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a)))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => (dv_S_a) (h_eq ▸ hu)
  · rw [fv_syn_wa (syn_wss S_cls (Class.cv a))
        (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss S_cls (Class.cv a)]
    rw [Finset.mem_union]
    left
    exact hu

theorem nb059_wpp_notmem_0007 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_004 R S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0006 R S_cls a dv_S_a)

theorem nb059_focused_notmem_0007 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_001 R S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cab (nb059_alpha_dummy_000 R S_cls)
            (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
                (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb059_alpha_dummy_000 R S_cls)
      (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
        (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb059_focused_notmem_0004 R S_cls)) (h_eq ▸ hu)
  · rw [fv_syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
        (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))]
    rw [Finset.mem_union]
    left
    exact hu

theorem nb059_wpp_notmem_0008 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_001 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0007 R S_cls)

theorem nb059_focused_notmem_0008 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_003 R S_cls a) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
              (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab a
      (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a)))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => (dv_S_a) (h_eq ▸ hu)
  · rw [fv_syn_wa (syn_wss S_cls (Class.cv a))
        (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss S_cls (Class.cv a)]
    rw [Finset.mem_union]
    left
    exact hu

theorem nb059_wpp_notmem_0009 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_003 R S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0008 R S_cls a dv_S_a)

theorem nb059_compact_envfresh_0000 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) :
    TEnvFresh
      [((nb059_alpha_dummy_007 R S_cls), (nb059_alpha_dummy_008 S_cls a)),
        ((nb059_alpha_dummy_005 R S_cls), (nb059_alpha_dummy_006 S_cls a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (S_cls).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb059_alpha_dummy_007 R S_cls) (nb059_alpha_dummy_008 S_cls a)
      (nb059_wpp_notmem_0000 R S_cls) (nb059_wpp_notmem_0001 S_cls a)
      (TEnvFresh.consFresh (nb059_alpha_dummy_005 R S_cls) (nb059_alpha_dummy_006 S_cls a)
        (nb059_wpp_notmem_0002 R S_cls) (nb059_wpp_notmem_0003 S_cls a)
        (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a
          (nb059_wpp_notmem_0004 R S_cls) (nb059_wpp_notmem_0005 S_cls a dv_S_a)
          (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls)
            (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0006 R S_cls)
            (nb059_wpp_notmem_0007 R S_cls a dv_S_a)
            (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls)
              (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0008 R S_cls)
              (nb059_wpp_notmem_0009 R S_cls a dv_S_a) (TEnvFresh.nil (S_cls).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4C059C001Part002Stage2`. -/


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
noncomputable def nb059_wpp_refl_0000 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) :
    TReflOn
      [((nb059_alpha_dummy_007 R S_cls), (nb059_alpha_dummy_008 S_cls a)),
        ((nb059_alpha_dummy_005 R S_cls), (nb059_alpha_dummy_006 S_cls a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (S_cls).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0000 R S_cls a dv_S_a)

theorem nb059_compact_envfresh_0001 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) :
    TEnvFresh
      [((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (S_cls).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a (nb059_wpp_notmem_0004 R S_cls)
      (nb059_wpp_notmem_0005 S_cls a dv_S_a)
      (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls)
        (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0006 R S_cls)
        (nb059_wpp_notmem_0007 R S_cls a dv_S_a)
        (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls)
          (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0008 R S_cls)
          (nb059_wpp_notmem_0009 R S_cls a dv_S_a) (TEnvFresh.nil (S_cls).fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
