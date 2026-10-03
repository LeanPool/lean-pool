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
    (nb055_alpha_dummy_014) ∈
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) :=
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
    (nb055_alpha_dummy_016 x y) ∈
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) :=
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
    (nb055_alpha_dummy_119) ∈ (((Class.cv (nb055_alpha_dummy_119))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0141 (x : Var) (y : Var) :
    (nb055_alpha_dummy_121 x y) ∈ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0142 :
    (nb055_alpha_dummy_126) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_126))).fv) :=
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
    (nb055_alpha_dummy_128 x y) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_128 x y))).fv) :=
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
    (nb055_alpha_dummy_126) ∈
      (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0145 (x : Var) (y : Var) :
    (nb055_alpha_dummy_128 x y) ∈
      (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0146 :
    (nb055_alpha_dummy_133) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_133))
            (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0147 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0148 :
    (nb055_alpha_dummy_133) ∈
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0149 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ∈
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0150 :
    (nb055_alpha_dummy_134) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_133))
            (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0151 (x : Var) (y : Var) :
    (nb055_alpha_dummy_137 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0152 :
    (nb055_alpha_dummy_134) ∈
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0153 (x : Var) (y : Var) :
    (nb055_alpha_dummy_137 x y) ∈
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0154 :
    (nb055_alpha_dummy_133) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0155 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0156 :
    (nb055_alpha_dummy_133) ∈
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0157 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ∈
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_136 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0158 :
    (nb055_alpha_dummy_134) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0159 (x : Var) (y : Var) :
    (nb055_alpha_dummy_137 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0160 :
    (nb055_alpha_dummy_134) ∈
      (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0161 (x : Var) (y : Var) :
    (nb055_alpha_dummy_137 x y) ∈
      (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0162 :
    (nb055_alpha_dummy_078) ∈
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0163 :
    (nb055_alpha_dummy_078) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_079 x y) ∈
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0165 (x : Var) (y : Var) :
    (nb055_alpha_dummy_079 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_078) ∈
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb055_alpha_dummy_079 x y) ∈
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb055_alpha_dummy_119) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0169 (x : Var) (y : Var) :
    (nb055_alpha_dummy_121 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0170 :
    (nb055_alpha_dummy_119) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0171 (x : Var) (y : Var) :
    (nb055_alpha_dummy_121 x y) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0172 :
    (nb055_alpha_dummy_001) ∈
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv) :=
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
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) :=
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
    (nb055_alpha_dummy_078) ∈
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0175 :
    (nb055_alpha_dummy_078) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_079 x y) ∈
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0177 (x : Var) (y : Var) :
    (nb055_alpha_dummy_079 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_078) ∈
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) :=
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
    (nb055_alpha_dummy_079 x y) ∈
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) :=
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
    (nb055_alpha_dummy_155) ∈ (((Class.cv (nb055_alpha_dummy_155))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0181 (x : Var) (y : Var) :
    (nb055_alpha_dummy_157 x y) ∈ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0182 :
    (nb055_alpha_dummy_162) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_162))).fv) :=
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
    (nb055_alpha_dummy_164 x y) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_164 x y))).fv) :=
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
    (nb055_alpha_dummy_162) ∈
      (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0185 (x : Var) (y : Var) :
    (nb055_alpha_dummy_164 x y) ∈
      (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0186 :
    (nb055_alpha_dummy_169) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_169))
            (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0187 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0188 :
    (nb055_alpha_dummy_169) ∈
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0189 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ∈
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0190 :
    (nb055_alpha_dummy_170) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_169))
            (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0191 (x : Var) (y : Var) :
    (nb055_alpha_dummy_173 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0192 :
    (nb055_alpha_dummy_170) ∈
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0193 (x : Var) (y : Var) :
    (nb055_alpha_dummy_173 x y) ∈
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0194 :
    (nb055_alpha_dummy_169) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0195 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0196 :
    (nb055_alpha_dummy_169) ∈
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0197 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ∈
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_172 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0198 :
    (nb055_alpha_dummy_170) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0199 (x : Var) (y : Var) :
    (nb055_alpha_dummy_173 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0200 :
    (nb055_alpha_dummy_170) ∈
      (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0201 (x : Var) (y : Var) :
    (nb055_alpha_dummy_173 x y) ∈
      (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0202 :
    (nb055_alpha_dummy_015) ∈
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0203 :
    (nb055_alpha_dummy_015) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_017 x y) ∈
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0205 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
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
    (nb055_alpha_dummy_015) ∈
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb055_alpha_dummy_017 x y) ∈
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
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
    (nb055_alpha_dummy_155) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0209 (x : Var) (y : Var) :
    (nb055_alpha_dummy_157 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0210 :
    (nb055_alpha_dummy_155) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0211 (x : Var) (y : Var) :
    (nb055_alpha_dummy_157 x y) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0212 :
    (nb055_alpha_dummy_000) ∈
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv) :=
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
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) :=
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
