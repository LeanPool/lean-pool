/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001042ImaReflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_ima`. -/
@[expose]
noncomputable def nominalDfIma (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCima A B) (.cab x (synWrex y B (synWbr (.cv y) A (.cv x))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alphaDummy002 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy004 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)
  let alphaDummy005 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)
  let alphaDummy006 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy002
              (synWrex alphaDummy003 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCphi (Class.cv alphaDummy003))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCun (synCphi (Class.cv alphaDummy003)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy007 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy008 : Var :=
    (freshVar (((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCphi (Class.cv alphaDummy003)))))).fv ∪ ((Class.cab alphaDummy002
            (synWrex alphaDummy003 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCphi (Class.cv alphaDummy003)))))).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv ∪ ((Class.cab alphaDummy004
            (synWrex alphaDummy005 (Class.cv y) (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv) 0)
  let alphaDummy010 : Var := (freshVar (((Class.cv alphaDummy003)).fv) 0)
  let alphaDummy011 : Var := (freshVar (((Class.cv alphaDummy003)).fv) 1)
  let alphaDummy012 : Var := (freshVar (((Class.cv alphaDummy005)).fv) 0)
  let alphaDummy013 : Var := (freshVar (((Class.cv alphaDummy005)).fv) 1)
  let alphaDummy014 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy010) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy010) (synC1c))).fv ∪
        ((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy012) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy012) (synC1c))).fv ∪
        ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy018 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy021 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy022 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv ∪
        ((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv ∪
        ((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy018)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy021)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy017))).fv ∪
        ((synCcompl (Class.cv alphaDummy018))).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy020))).fv ∪
        ((synCcompl (Class.cv alphaDummy021))).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCun (synCphi (Class.cv alphaDummy003)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCun (synCphi (Class.cv alphaDummy003)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy003)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy005)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy003))).fv ∪
        ((synCphi (Class.cv alphaDummy003))).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy005))).fv ∪
        ((synCphi (Class.cv alphaDummy005))).fv) 0)
  have fresh_046 : alphaDummy000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_047 : alphaDummy001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have support_mem_0000 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 :
    alphaDummy001 ∈
      (((synCcompl (Class.cab alphaDummy002
              (synWrex alphaDummy003 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCphi (Class.cv alphaDummy003))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCun (synCphi (Class.cv alphaDummy003))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0002 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    y ∈
      (((synCcompl (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCun (synCphi (Class.cv alphaDummy005))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0004 :
    alphaDummy001 ∈
      (((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCphi (Class.cv alphaDummy003)))))).fv ∪ ((Class.cab alphaDummy002
            (synWrex alphaDummy003 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCphi (Class.cv alphaDummy003)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0005 :
    y ∈
      (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv ∪ ((Class.cab alphaDummy004
            (synWrex alphaDummy005 (Class.cv y) (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0006 : alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alphaDummy010 ∈
      (((Wff.classMem (Class.cv alphaDummy010) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy010) (synC1c))).fv ∪
        ((Class.cv alphaDummy010)).fv) :=
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
  have support_mem_0009 :
    alphaDummy012 ∈
      (((Wff.classMem (Class.cv alphaDummy012) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy012) (synC1c))).fv ∪
        ((Class.cv alphaDummy012)).fv) :=
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
  have support_mem_0010 :
    alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alphaDummy012 ∈ (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alphaDummy017 ∈
      (((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv ∪
        ((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alphaDummy020 ∈
      (((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv ∪
        ((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy018 ∈
      (((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv ∪
        ((synCnin (Class.cv alphaDummy017) (Class.cv alphaDummy018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy021 ∈
      (((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv ∪
        ((synCnin (Class.cv alphaDummy020) (Class.cv alphaDummy021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy017 ∈
      (((synCcompl (Class.cv alphaDummy017))).fv ∪
        ((synCcompl (Class.cv alphaDummy018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy020 ∈
      (((synCcompl (Class.cv alphaDummy020))).fv ∪
        ((synCcompl (Class.cv alphaDummy021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alphaDummy018 ∈
      (((synCcompl (Class.cv alphaDummy017))).fv ∪
        ((synCcompl (Class.cv alphaDummy018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    alphaDummy021 ∈
      (((synCcompl (Class.cv alphaDummy020))).fv ∪
        ((synCcompl (Class.cv alphaDummy021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0027 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy002
              (synWrex alphaDummy003 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCphi (Class.cv alphaDummy003))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCun (synCphi (Class.cv alphaDummy003))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0030 : x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    x ∈
      (((synCcompl (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCun (synCphi (Class.cv alphaDummy005))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0032 :
    alphaDummy000 ∈
      (((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCun (synCphi (Class.cv alphaDummy003)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy002 (synWrex alphaDummy003 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy002)
                (synCun (synCphi (Class.cv alphaDummy003)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0033 :
    x ∈
      (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0034 :
    alphaDummy003 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy003)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0035 :
    alphaDummy005 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy005)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0036 :
    alphaDummy003 ∈
      (((synCphi (Class.cv alphaDummy003))).fv ∪
        ((synCphi (Class.cv alphaDummy003))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0037 :
    alphaDummy005 ∈
      (((synCphi (Class.cv alphaDummy005))).fv ∪
        ((synCphi (Class.cv alphaDummy005))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alphaDummy000 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0000 : alphaDummy000 ∉ (B).fv := by exact focused_notmem_0000
  have wpp_notmem_0001 : x ∉ (B).fv := by exact dv_B_x
  have focused_notmem_0001 : alphaDummy001 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0002 : alphaDummy001 ∉ (B).fv := by exact focused_notmem_0001
  have wpp_notmem_0003 : y ∉ (B).fv := by exact dv_B_y
  have wpp_refl_0000 : TReflOn [(alphaDummy001, y), (alphaDummy000, x)] (B).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))
  have wpp_notmem_0004 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : y ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy013 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy014 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy015 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy016 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alphaDummy019 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy017 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy020 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alphaDummy018 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy021 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0008) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0009) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have wpp_notmem_0028 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : y ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alphaDummy013 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alphaDummy014 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alphaDummy015 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alphaDummy016 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alphaDummy019 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alphaDummy017 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alphaDummy020 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alphaDummy018 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : alphaDummy021 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      ((synC0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0034) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0035) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy017) (Class.cv alphaDummy018))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy016)
            (synCun (Class.cv alphaDummy017) (Class.cv alphaDummy018)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy020) (Class.cv alphaDummy021))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy019)
            (synCun (Class.cv alphaDummy020) (Class.cv alphaDummy021))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
            (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
            (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
            (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
            (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
            (alphaDummy001, y), (alphaDummy000, x)] (synC0) (by simp only [fv_syn_c0])))
      (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0052 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : y ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : alphaDummy007 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alphaDummy008 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alphaDummy009 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0062 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0063 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0064 : alphaDummy011 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0065 : alphaDummy013 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0066 : alphaDummy010 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0067 : alphaDummy012 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0068 : alphaDummy014 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0069 : alphaDummy015 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alphaDummy014, alphaDummy015), (alphaDummy010, alphaDummy012),
        (alphaDummy011, alphaDummy013), (alphaDummy003, alphaDummy005),
        (alphaDummy002, alphaDummy004), (alphaDummy008, alphaDummy009),
        (alphaDummy006, alphaDummy007), (alphaDummy001, y), (alphaDummy000, x)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy003) (Class.cv alphaDummy001)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy002) (synCphi (Class.cv alphaDummy003)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy005) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy004) (synCphi (Class.cv alphaDummy005))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective
                (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy003)).fv) (by decide))
                      (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy008, alphaDummy009), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)] (synC1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg splitAlpha0000))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy014, alphaDummy015),
                                (alphaDummy010, alphaDummy012),
                                (alphaDummy011, alphaDummy013),
                                (alphaDummy003, alphaDummy005),
                                (alphaDummy002, alphaDummy004),
                                (alphaDummy008, alphaDummy009),
                                (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                                (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy014, alphaDummy015),
                                (alphaDummy010, alphaDummy012),
                                (alphaDummy011, alphaDummy013),
                                (alphaDummy003, alphaDummy005),
                                (alphaDummy002, alphaDummy004),
                                (alphaDummy008, alphaDummy009),
                                (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                                (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0070 : alphaDummy032 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0071 : alphaDummy033 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0072 : alphaDummy034 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alphaDummy035 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alphaDummy036 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alphaDummy037 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0008) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0009) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have wpp_notmem_0076 : alphaDummy032 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0077 : alphaDummy033 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0078 : alphaDummy034 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alphaDummy035 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alphaDummy036 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alphaDummy037 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      ((synC0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy017) (Class.cv alphaDummy018))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy016)
            (synCun (Class.cv alphaDummy017) (Class.cv alphaDummy018)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy020) (Class.cv alphaDummy021))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy019)
            (synCun (Class.cv alphaDummy020) (Class.cv alphaDummy021))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
            (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
            (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
            (alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
            (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
            (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
            (alphaDummy001, y), (alphaDummy000, x)] (synC0) (by simp only [fv_syn_c0])))
      (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy010)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0082 : alphaDummy032 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alphaDummy033 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alphaDummy034 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alphaDummy035 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alphaDummy036 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alphaDummy037 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alphaDummy014, alphaDummy015), (alphaDummy010, alphaDummy012),
        (alphaDummy011, alphaDummy013), (alphaDummy036, alphaDummy037),
        (alphaDummy034, alphaDummy035), (alphaDummy003, alphaDummy005),
        (alphaDummy002, alphaDummy004), (alphaDummy032, alphaDummy033),
        (alphaDummy006, alphaDummy007), (alphaDummy001, y), (alphaDummy000, x)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                            (TAlphaVar.free (by simp) (by simp)))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy036) (synCphi (Class.cv alphaDummy003)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy036)
            (synCphi (Class.cv alphaDummy003)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy037) (synCphi (Class.cv alphaDummy005)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy037)
            (synCphi (Class.cv alphaDummy005))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy003)).fv) (by decide))
                    (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy018, alphaDummy021),
        (alphaDummy017, alphaDummy020), (alphaDummy016, alphaDummy019),
        (alphaDummy014, alphaDummy015), (alphaDummy010, alphaDummy012),
        (alphaDummy011, alphaDummy013), (alphaDummy036, alphaDummy037),
        (alphaDummy034, alphaDummy035), (alphaDummy003, alphaDummy005),
        (alphaDummy002, alphaDummy004), (alphaDummy032, alphaDummy033),
        (alphaDummy006, alphaDummy007), (alphaDummy001, y), (alphaDummy000, x)]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy014, alphaDummy015),
                              (alphaDummy010, alphaDummy012),
                              (alphaDummy011, alphaDummy013),
                              (alphaDummy036, alphaDummy037),
                              (alphaDummy034, alphaDummy035),
                              (alphaDummy003, alphaDummy005),
                              (alphaDummy002, alphaDummy004),
                              (alphaDummy032, alphaDummy033),
                              (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                              (alphaDummy000, x)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy014, alphaDummy015),
                              (alphaDummy010, alphaDummy012),
                              (alphaDummy011, alphaDummy013),
                              (alphaDummy036, alphaDummy037),
                              (alphaDummy034, alphaDummy035),
                              (alphaDummy003, alphaDummy005),
                              (alphaDummy002, alphaDummy004),
                              (alphaDummy032, alphaDummy033),
                              (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                              (alphaDummy000, x)]
                            (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy003)).fv) (by decide))
                      (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy018, alphaDummy021), (alphaDummy017, alphaDummy020),
        (alphaDummy016, alphaDummy019), (alphaDummy014, alphaDummy015),
        (alphaDummy010, alphaDummy012), (alphaDummy011, alphaDummy013),
        (alphaDummy036, alphaDummy037), (alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)] (synC1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy014, alphaDummy015),
                                (alphaDummy010, alphaDummy012),
                                (alphaDummy011, alphaDummy013),
                                (alphaDummy036, alphaDummy037),
                                (alphaDummy034, alphaDummy035),
                                (alphaDummy003, alphaDummy005),
                                (alphaDummy002, alphaDummy004),
                                (alphaDummy032, alphaDummy033),
                                (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                                (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy014, alphaDummy015),
                                (alphaDummy010, alphaDummy012),
                                (alphaDummy011, alphaDummy013),
                                (alphaDummy036, alphaDummy037),
                                (alphaDummy034, alphaDummy035),
                                (alphaDummy003, alphaDummy005),
                                (alphaDummy002, alphaDummy004),
                                (alphaDummy032, alphaDummy033),
                                (alphaDummy006, alphaDummy007), (alphaDummy001, y),
                                (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0088 : alphaDummy000 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0089 : x ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0090 : alphaDummy001 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0091 : y ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0092 : alphaDummy006 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0093 : alphaDummy007 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0094 : alphaDummy032 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0095 : alphaDummy033 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0096 : alphaDummy002 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0097 : alphaDummy004 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0098 : alphaDummy003 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0099 : alphaDummy005 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0100 : alphaDummy034 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0101 : alphaDummy035 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alphaDummy034, alphaDummy035), (alphaDummy003, alphaDummy005),
        (alphaDummy002, alphaDummy004), (alphaDummy032, alphaDummy033),
        (alphaDummy006, alphaDummy007), (alphaDummy001, y), (alphaDummy000, x)]
      ((synCcompl (synCsn (synC0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0100) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0101) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0098) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0099) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0096) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0097) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have focused_notmem_0002 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0102 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0002
  have wpp_notmem_0103 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0003 : alphaDummy001 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0104 : alphaDummy001 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0105 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0008 : TReflOn [(alphaDummy001, y), (alphaDummy000, x)] (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))
  have splitAlpha0004 :
    TAlphaWff [(alphaDummy001, y), (alphaDummy000, x)]
      (Wff.classMem (synCop (Class.cv alphaDummy001) (Class.cv alphaDummy000)) A)
      (Wff.classMem (synCop (Class.cv y) (Class.cv x)) A) :=
    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alphaDummy001)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)] (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alphaDummy001)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy034, alphaDummy035),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004),
        (alphaDummy032, alphaDummy033), (alphaDummy006, alphaDummy007),
        (alphaDummy001, y), (alphaDummy000, x)] (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))
      (TAlphaClass.reflOfReflOn [(alphaDummy001, y), (alphaDummy000, x)] A wpp_refl_0008))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [(alphaDummy001, y), (alphaDummy000, x)] B
                wpp_refl_0000)) splitAlpha0004)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
