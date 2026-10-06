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
    (nb056AlphaDummy128) ∈ (((Class.cv (nb056AlphaDummy128))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0129 (f : Var) :
    (nb056AlphaDummy130 f) ∈ (((Class.cv (nb056AlphaDummy130 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0130 :
    (nb056AlphaDummy135) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy135))).fv) :=
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
    (nb056AlphaDummy137 f) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy137 f))).fv) :=
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
    (nb056AlphaDummy135) ∈
      (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0133 (f : Var) :
    (nb056AlphaDummy137 f) ∈
      (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0134 :
    (nb056AlphaDummy142) ∈
      (((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy142))
            (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0135 (f : Var) :
    (nb056AlphaDummy145 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0136 :
    (nb056AlphaDummy142) ∈
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0137 (f : Var) :
    (nb056AlphaDummy145 f) ∈
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0138 :
    (nb056AlphaDummy143) ∈
      (((synCnin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy142))
            (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0139 (f : Var) :
    (nb056AlphaDummy146 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0140 :
    (nb056AlphaDummy143) ∈
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0141 (f : Var) :
    (nb056AlphaDummy146 f) ∈
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0142 :
    (nb056AlphaDummy142) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0143 (f : Var) :
    (nb056AlphaDummy145 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0144 :
    (nb056AlphaDummy142) ∈
      (((Class.cv (nb056AlphaDummy142))).fv ∪ ((Class.cv (nb056AlphaDummy142))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0145 (f : Var) :
    (nb056AlphaDummy145 f) ∈
      (((Class.cv (nb056AlphaDummy145 f))).fv ∪ ((Class.cv (nb056AlphaDummy145 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0146 :
    (nb056AlphaDummy143) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0147 (f : Var) :
    (nb056AlphaDummy146 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0148 :
    (nb056AlphaDummy143) ∈
      (((Class.cv (nb056AlphaDummy143))).fv ∪ ((Class.cv (nb056AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0149 (f : Var) :
    (nb056AlphaDummy146 f) ∈
      (((Class.cv (nb056AlphaDummy146 f))).fv ∪ ((Class.cv (nb056AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0150 :
    (nb056AlphaDummy085) ∈
      (((Class.cv (nb056AlphaDummy086))).fv ∪ ((Class.cv (nb056AlphaDummy085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0151 :
    (nb056AlphaDummy085) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCphi (Class.cv (nb056AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy087 f) ∈
      (((Class.cv (nb056AlphaDummy088 f))).fv ∪ ((Class.cv (nb056AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0153 (f : Var) :
    (nb056AlphaDummy087 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCphi (Class.cv (nb056AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy085) ∈
      (((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                  (synCsn (synC0c))))))).fv) :=
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
    (nb056AlphaDummy087 f) ∈
      (((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv) :=
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
    (nb056AlphaDummy128) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0157 (f : Var) :
    (nb056AlphaDummy130 f) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0158 :
    (nb056AlphaDummy128) ∈
      (((synCphi (Class.cv (nb056AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy128)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0159 (f : Var) :
    (nb056AlphaDummy130 f) ∈
      (((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy130 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0160 :
    (nb056AlphaDummy000) ∈
      (((synCnin (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))).fv) :=
  by
  have member : (nb056AlphaDummy000) ∈ (Class.cv (nb056AlphaDummy000)).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_cnin, fv_syn_ccom]
  with_reducible
    exact
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ member))

theorem nb056_support_mem_0161 (f : Var) :
    f ∈
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
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
    (nb056AlphaDummy000) ∈
      (((synCcom (Class.cv (nb056AlphaDummy000))
            (synCcnv (Class.cv (nb056AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  have member : (nb056AlphaDummy000) ∈ (Class.cv (nb056AlphaDummy000)).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_ccom]
  with_reducible exact Finset.mem_union_left _ (Finset.mem_union_left _ member)

theorem nb056_support_mem_0163 (f : Var) :
    f ∈ (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  have member : f ∈ (Class.cv f).fv :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  rw [fv_syn_ccom]
  with_reducible exact Finset.mem_union_left _ (Finset.mem_union_left _ member)

theorem nb056_support_mem_0164 :
    (nb056AlphaDummy000) ∈
      (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0165 :
    (nb056AlphaDummy000) ∈
      (({(nb056AlphaDummy005)} : Finset Var) ∪ ({(nb056AlphaDummy006)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy007) (synWa (synWbr (Class.cv (nb056AlphaDummy005))
                (synCcnv (Class.cv (nb056AlphaDummy000)))
                (Class.cv (nb056AlphaDummy007))) (synWbr (Class.cv (nb056AlphaDummy007))
                (Class.cv (nb056AlphaDummy000)) (Class.cv (nb056AlphaDummy006)))))).fv) :=
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
    f ∈ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := f) (s := ((Class.cv f)).fv) ((synCcnv (Class.cv f))).fv
        ?_
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0167 (f : Var) :
    f ∈
      (({(nb056AlphaDummy008 f)} : Finset Var) ∪ ({(nb056AlphaDummy009 f)} : Finset Var) ∪
        ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv) :=
  by
  have fresh : f ≠ nb056AlphaDummy010 f :=
    by
    unfold nb056AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  with_reducible
    refine
      Finset.mem_union_right (a := f) (t := ((synWex (nb056AlphaDummy010 f) (synWa
              (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
                (Class.cv (nb056AlphaDummy010 f)))
              (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
                (Class.cv (nb056AlphaDummy009 f)))))).fv)
        (({(nb056AlphaDummy008 f)} : Finset Var) ∪
          ({(nb056AlphaDummy009 f)} : Finset Var))
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
    (nb056AlphaDummy000) ∈
      (({(nb056AlphaDummy085)} : Finset Var) ∪ ({(nb056AlphaDummy086)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))).fv) :=
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
      (({(nb056AlphaDummy087 f)} : Finset Var) ∪ ({(nb056AlphaDummy088 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0170 :
    (nb056AlphaDummy000) ∈ (((Class.cv (nb056AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0172 :
    (nb056AlphaDummy007) ∈
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0173 :
    (nb056AlphaDummy007) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCphi (Class.cv (nb056AlphaDummy164)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy010 f) ∈
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0175 (f : Var) :
    (nb056AlphaDummy010 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCphi (Class.cv (nb056AlphaDummy166 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy007) ∈
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv ∪
        ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCphi (Class.cv (nb056AlphaDummy164))))))).fv) :=
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
    (nb056AlphaDummy010 f) ∈
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv ∪
        ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCphi (Class.cv (nb056AlphaDummy166 f))))))).fv) :=
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
    (nb056AlphaDummy164) ∈ (((Class.cv (nb056AlphaDummy164))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0179 (f : Var) :
    (nb056AlphaDummy166 f) ∈ (((Class.cv (nb056AlphaDummy166 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0180 :
    (nb056AlphaDummy171) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy171))).fv) :=
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
    (nb056AlphaDummy173 f) ∈
      (((Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))).fv ∪
        ((Class.cv (nb056AlphaDummy173 f))).fv) :=
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
    (nb056AlphaDummy171) ∈
      (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0183 (f : Var) :
    (nb056AlphaDummy173 f) ∈
      (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0184 :
    (nb056AlphaDummy178) ∈
      (((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy178))
            (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0185 (f : Var) :
    (nb056AlphaDummy181 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0186 :
    (nb056AlphaDummy178) ∈
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0187 (f : Var) :
    (nb056AlphaDummy181 f) ∈
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0188 :
    (nb056AlphaDummy179) ∈
      (((synCnin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy178))
            (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0189 (f : Var) :
    (nb056AlphaDummy182 f) ∈
      (((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv ∪
        ((synCnin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0190 :
    (nb056AlphaDummy179) ∈
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0191 (f : Var) :
    (nb056AlphaDummy182 f) ∈
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0192 :
    (nb056AlphaDummy178) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy178)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0193 (f : Var) :
    (nb056AlphaDummy181 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy181 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0194 :
    (nb056AlphaDummy178) ∈
      (((Class.cv (nb056AlphaDummy178))).fv ∪ ((Class.cv (nb056AlphaDummy178))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0195 (f : Var) :
    (nb056AlphaDummy181 f) ∈
      (((Class.cv (nb056AlphaDummy181 f))).fv ∪ ((Class.cv (nb056AlphaDummy181 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0196 :
    (nb056AlphaDummy179) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy178)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy179)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0197 (f : Var) :
    (nb056AlphaDummy182 f) ∈
      (((synCcompl (Class.cv (nb056AlphaDummy181 f)))).fv ∪
        ((synCcompl (Class.cv (nb056AlphaDummy182 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0198 :
    (nb056AlphaDummy179) ∈
      (((Class.cv (nb056AlphaDummy179))).fv ∪ ((Class.cv (nb056AlphaDummy179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0199 (f : Var) :
    (nb056AlphaDummy182 f) ∈
      (((Class.cv (nb056AlphaDummy182 f))).fv ∪ ((Class.cv (nb056AlphaDummy182 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0200 :
    (nb056AlphaDummy006) ∈
      (((Class.cv (nb056AlphaDummy007))).fv ∪ ((Class.cv (nb056AlphaDummy006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0201 :
    (nb056AlphaDummy006) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCphi (Class.cv (nb056AlphaDummy164)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy009 f) ∈
      (((Class.cv (nb056AlphaDummy010 f))).fv ∪ ((Class.cv (nb056AlphaDummy009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0203 (f : Var) :
    (nb056AlphaDummy009 f) ∈
      (((synCcompl (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCphi (Class.cv (nb056AlphaDummy166 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (nb056AlphaDummy006) ∈
      (((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                  (synCsn (synC0c))))))).fv) :=
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
    (nb056AlphaDummy009 f) ∈
      (((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))).fv) :=
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
    (nb056AlphaDummy164) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy164))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0207 (f : Var) :
    (nb056AlphaDummy166 f) ∈
      (((synCcompl (synCphi (Class.cv (nb056AlphaDummy166 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0208 :
    (nb056AlphaDummy164) ∈
      (((synCphi (Class.cv (nb056AlphaDummy164)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy164)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0209 (f : Var) :
    (nb056AlphaDummy166 f) ∈
      (((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv ∪
        ((synCphi (Class.cv (nb056AlphaDummy166 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_compact_fv_empty_0026 : (nb056AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0027 (f : Var) :
    (nb056AlphaDummy004 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0028 : (nb056AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0029 (f : Var) :
    (nb056AlphaDummy002 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0030 : (nb056AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb056_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
