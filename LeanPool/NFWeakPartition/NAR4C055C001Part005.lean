/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C055C001Block001

/-! NF weak partition development: NAR4C055C001Part005. -/


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

theorem nb055_support_mem_0138 :
    (nb055AlphaDummy014) ∈
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv ∪
        ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0139 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0140 :
    (nb055AlphaDummy119) ∈ (((Class.cv (nb055AlphaDummy119))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0141 (x : Var) (y : Var) :
    (nb055AlphaDummy121 x y) ∈ (((Class.cv (nb055AlphaDummy121 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0142 :
    (nb055AlphaDummy126) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy126)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy126)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy126))).fv) :=
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

theorem nb055_support_mem_0143 (x : Var) (y : Var) :
    (nb055AlphaDummy128 x y) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy128 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy128 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy128 x y))).fv) :=
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

theorem nb055_support_mem_0144 :
    (nb055AlphaDummy126) ∈
      (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0145 (x : Var) (y : Var) :
    (nb055AlphaDummy128 x y) ∈
      (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0146 :
    (nb055AlphaDummy133) ∈
      (((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy133))
            (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0147 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0148 :
    (nb055AlphaDummy133) ∈
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0149 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ∈
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0150 :
    (nb055AlphaDummy134) ∈
      (((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy133))
            (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0151 (x : Var) (y : Var) :
    (nb055AlphaDummy137 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0152 :
    (nb055AlphaDummy134) ∈
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0153 (x : Var) (y : Var) :
    (nb055AlphaDummy137 x y) ∈
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0154 :
    (nb055AlphaDummy133) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy133)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0155 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy136 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0156 :
    (nb055AlphaDummy133) ∈
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy133))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0157 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ∈
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy136 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0158 :
    (nb055AlphaDummy134) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy133)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0159 (x : Var) (y : Var) :
    (nb055AlphaDummy137 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy136 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0160 :
    (nb055AlphaDummy134) ∈
      (((Class.cv (nb055AlphaDummy134))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0161 (x : Var) (y : Var) :
    (nb055AlphaDummy137 x y) ∈
      (((Class.cv (nb055AlphaDummy137 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0162 :
    (nb055AlphaDummy078) ∈
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0163 :
    (nb055AlphaDummy078) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCphi (Class.cv (nb055AlphaDummy119)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0164 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0165 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCphi (Class.cv (nb055AlphaDummy121 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0166 :
    (nb055AlphaDummy078) ∈
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0167 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0168 :
    (nb055AlphaDummy119) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy119))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0169 (x : Var) (y : Var) :
    (nb055AlphaDummy121 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy121 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0170 :
    (nb055AlphaDummy119) ∈
      (((synCphi (Class.cv (nb055AlphaDummy119)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy119)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0171 (x : Var) (y : Var) :
    (nb055AlphaDummy121 x y) ∈
      (((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0172 :
    (nb055AlphaDummy001) ∈
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0173 (x : Var) (y : Var) :
    y ∈
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0174 :
    (nb055AlphaDummy078) ∈
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0175 :
    (nb055AlphaDummy078) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCphi (Class.cv (nb055AlphaDummy155)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0176 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0177 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCphi (Class.cv (nb055AlphaDummy157 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0178 :
    (nb055AlphaDummy078) ∈
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv ∪
        ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0179 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∈
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0180 :
    (nb055AlphaDummy155) ∈ (((Class.cv (nb055AlphaDummy155))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0181 (x : Var) (y : Var) :
    (nb055AlphaDummy157 x y) ∈ (((Class.cv (nb055AlphaDummy157 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0182 :
    (nb055AlphaDummy162) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy162)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy162)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy162))).fv) :=
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

theorem nb055_support_mem_0183 (x : Var) (y : Var) :
    (nb055AlphaDummy164 x y) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy164 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy164 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy164 x y))).fv) :=
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

theorem nb055_support_mem_0184 :
    (nb055AlphaDummy162) ∈
      (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0185 (x : Var) (y : Var) :
    (nb055AlphaDummy164 x y) ∈
      (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0186 :
    (nb055AlphaDummy169) ∈
      (((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy169))
            (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0187 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0188 :
    (nb055AlphaDummy169) ∈
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0189 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ∈
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0190 :
    (nb055AlphaDummy170) ∈
      (((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy169))
            (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0191 (x : Var) (y : Var) :
    (nb055AlphaDummy173 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0192 :
    (nb055AlphaDummy170) ∈
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0193 (x : Var) (y : Var) :
    (nb055AlphaDummy173 x y) ∈
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0194 :
    (nb055AlphaDummy169) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy169)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0195 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy172 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0196 :
    (nb055AlphaDummy169) ∈
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy169))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0197 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ∈
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy172 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0198 :
    (nb055AlphaDummy170) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy169)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0199 (x : Var) (y : Var) :
    (nb055AlphaDummy173 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy172 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0200 :
    (nb055AlphaDummy170) ∈
      (((Class.cv (nb055AlphaDummy170))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0201 (x : Var) (y : Var) :
    (nb055AlphaDummy173 x y) ∈
      (((Class.cv (nb055AlphaDummy173 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0202 :
    (nb055AlphaDummy015) ∈
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0203 :
    (nb055AlphaDummy015) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCphi (Class.cv (nb055AlphaDummy155)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0204 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0205 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCphi (Class.cv (nb055AlphaDummy157 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0206 :
    (nb055AlphaDummy015) ∈
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0207 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0208 :
    (nb055AlphaDummy155) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy155))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0209 (x : Var) (y : Var) :
    (nb055AlphaDummy157 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy157 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0210 :
    (nb055AlphaDummy155) ∈
      (((synCphi (Class.cv (nb055AlphaDummy155)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy155)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0211 (x : Var) (y : Var) :
    (nb055AlphaDummy157 x y) ∈
      (((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0212 :
    (nb055AlphaDummy000) ∈
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0213 (x : Var) (y : Var) :
    x ∈
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
