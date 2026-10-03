/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C056C001Block001

/-! NF weak partition development: NAR4C056C001Part005. -/


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

theorem nb056_support_mem_0128 :
    (nb056_alpha_dummy_128) ∈ (((Class.cv (nb056_alpha_dummy_128))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0129 (f : Var) :
    (nb056_alpha_dummy_130 f) ∈ (((Class.cv (nb056_alpha_dummy_130 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0130 :
    (nb056_alpha_dummy_135) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_135))).fv) :=
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

theorem nb056_support_mem_0131 (f : Var) :
    (nb056_alpha_dummy_137 f) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_137 f))).fv) :=
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

theorem nb056_support_mem_0132 :
    (nb056_alpha_dummy_135) ∈
      (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0133 (f : Var) :
    (nb056_alpha_dummy_137 f) ∈
      (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0134 :
    (nb056_alpha_dummy_142) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_142))
            (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0135 (f : Var) :
    (nb056_alpha_dummy_145 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0136 :
    (nb056_alpha_dummy_142) ∈
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0137 (f : Var) :
    (nb056_alpha_dummy_145 f) ∈
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0138 :
    (nb056_alpha_dummy_143) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_142))
            (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0139 (f : Var) :
    (nb056_alpha_dummy_146 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0140 :
    (nb056_alpha_dummy_143) ∈
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0141 (f : Var) :
    (nb056_alpha_dummy_146 f) ∈
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0142 :
    (nb056_alpha_dummy_142) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0143 (f : Var) :
    (nb056_alpha_dummy_145 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0144 :
    (nb056_alpha_dummy_142) ∈
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0145 (f : Var) :
    (nb056_alpha_dummy_145 f) ∈
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0146 :
    (nb056_alpha_dummy_143) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0147 (f : Var) :
    (nb056_alpha_dummy_146 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0148 :
    (nb056_alpha_dummy_143) ∈
      (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0149 (f : Var) :
    (nb056_alpha_dummy_146 f) ∈
      (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0150 :
    (nb056_alpha_dummy_085) ∈
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0151 :
    (nb056_alpha_dummy_085) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0152 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0153 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0154 :
    (nb056_alpha_dummy_085) ∈
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0155 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0156 :
    (nb056_alpha_dummy_128) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0157 (f : Var) :
    (nb056_alpha_dummy_130 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0158 :
    (nb056_alpha_dummy_128) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0159 (f : Var) :
    (nb056_alpha_dummy_130 f) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0160 :
    (nb056_alpha_dummy_000) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  have member : (nb056_alpha_dummy_000) ∈ (Class.cv (nb056_alpha_dummy_000)).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_cnin, fv_syn_ccom]
  with_reducible
    exact
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ member))

theorem nb056_support_mem_0161 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  have member : f ∈ (Class.cv f).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_cnin, fv_syn_ccom]
  with_reducible
    exact
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ member))

theorem nb056_support_mem_0162 :
    (nb056_alpha_dummy_000) ∈
      (((syn_ccom (Class.cv (nb056_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  have member : (nb056_alpha_dummy_000) ∈ (Class.cv (nb056_alpha_dummy_000)).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_ccom]
  with_reducible exact Finset.mem_union_left _ (Finset.mem_union_left _ member)

theorem nb056_support_mem_0163 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  have member : f ∈ (Class.cv f).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_ccom]
  with_reducible exact Finset.mem_union_left _ (Finset.mem_union_left _ member)

theorem nb056_support_mem_0164 :
    (nb056_alpha_dummy_000) ∈
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0165 :
    (nb056_alpha_dummy_000) ∈
      (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
                (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))
                (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007))
                (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb056_support_mem_0166 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := f) (s := ((Class.cv f)).fv) ((syn_ccnv (Class.cv f))).fv
        ?_
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0167 (f : Var) :
    f ∈
      (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv) :=
  by
  have fresh : f ≠ nb056_alpha_dummy_010 f :=
    by
    unfold nb056_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  with_reducible
    refine
      Finset.mem_union_right (a := f) (t := ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv)
        (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪
          ({(nb056_alpha_dummy_009 f)} : Finset Var))
        ?_
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · with_reducible exact fresh
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb056_support_mem_0168 :
    (nb056_alpha_dummy_000) ∈
      (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0169 (f : Var) :
    f ∈
      (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0170 :
    (nb056_alpha_dummy_000) ∈ (((Class.cv (nb056_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0172 :
    (nb056_alpha_dummy_007) ∈
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0173 :
    (nb056_alpha_dummy_007) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0174 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0175 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0176 :
    (nb056_alpha_dummy_007) ∈
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0177 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0178 :
    (nb056_alpha_dummy_164) ∈ (((Class.cv (nb056_alpha_dummy_164))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0179 (f : Var) :
    (nb056_alpha_dummy_166 f) ∈ (((Class.cv (nb056_alpha_dummy_166 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0180 :
    (nb056_alpha_dummy_171) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_171))).fv) :=
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

theorem nb056_support_mem_0181 (f : Var) :
    (nb056_alpha_dummy_173 f) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_173 f))).fv) :=
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

theorem nb056_support_mem_0182 :
    (nb056_alpha_dummy_171) ∈
      (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0183 (f : Var) :
    (nb056_alpha_dummy_173 f) ∈
      (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0184 :
    (nb056_alpha_dummy_178) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_178))
            (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0185 (f : Var) :
    (nb056_alpha_dummy_181 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0186 :
    (nb056_alpha_dummy_178) ∈
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0187 (f : Var) :
    (nb056_alpha_dummy_181 f) ∈
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0188 :
    (nb056_alpha_dummy_179) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_178))
            (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0189 (f : Var) :
    (nb056_alpha_dummy_182 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0190 :
    (nb056_alpha_dummy_179) ∈
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0191 (f : Var) :
    (nb056_alpha_dummy_182 f) ∈
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0192 :
    (nb056_alpha_dummy_178) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0193 (f : Var) :
    (nb056_alpha_dummy_181 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0194 :
    (nb056_alpha_dummy_178) ∈
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0195 (f : Var) :
    (nb056_alpha_dummy_181 f) ∈
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0196 :
    (nb056_alpha_dummy_179) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0197 (f : Var) :
    (nb056_alpha_dummy_182 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0198 :
    (nb056_alpha_dummy_179) ∈
      (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0199 (f : Var) :
    (nb056_alpha_dummy_182 f) ∈
      (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0200 :
    (nb056_alpha_dummy_006) ∈
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0201 :
    (nb056_alpha_dummy_006) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0202 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0203 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0204 :
    (nb056_alpha_dummy_006) ∈
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0205 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0206 :
    (nb056_alpha_dummy_164) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0207 (f : Var) :
    (nb056_alpha_dummy_166 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0208 :
    (nb056_alpha_dummy_164) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0209 (f : Var) :
    (nb056_alpha_dummy_166 f) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_compact_fv_empty_0026 : (nb056_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0027 (f : Var) :
    (nb056_alpha_dummy_004 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0028 : (nb056_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0029 (f : Var) :
    (nb056_alpha_dummy_002 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0030 : (nb056_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
