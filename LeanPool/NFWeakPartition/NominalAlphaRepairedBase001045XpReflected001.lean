/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001045XpReflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_xp`. -/
@[expose]
noncomputable def nominalDfXp (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCxp A B)
        (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alphaDummy002 : Var :=
    (freshVar (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
            (Wff.classMem (Class.cv alphaDummy001) B))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) 1)
  let alphaDummy006 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)
  let alphaDummy007 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)
  let alphaDummy008 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy004
              (synWrex alphaDummy005 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy009 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv ∪ ((Class.cab alphaDummy004
            (synWrex alphaDummy005 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv ∪ ((Class.cab alphaDummy006
            (synWrex alphaDummy007 (Class.cv x) (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv) 0)
  let alphaDummy012 : Var := (freshVar (((Class.cv alphaDummy005)).fv) 0)
  let alphaDummy013 : Var := (freshVar (((Class.cv alphaDummy005)).fv) 1)
  let alphaDummy014 : Var := (freshVar (((Class.cv alphaDummy007)).fv) 0)
  let alphaDummy015 : Var := (freshVar (((Class.cv alphaDummy007)).fv) 1)
  let alphaDummy016 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy012) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy012) (synC1c))).fv ∪
        ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy014) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy014) (synC1c))).fv ∪
        ((Class.cv alphaDummy014)).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy021 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy024 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
        ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy019))).fv ∪
        ((synCcompl (Class.cv alphaDummy020))).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((Class.cv alphaDummy023)).fv ∪ ((Class.cv alphaDummy023)).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy005)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy007)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy005))).fv ∪
        ((synCphi (Class.cv alphaDummy005))).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy007))).fv ∪
        ((synCphi (Class.cv alphaDummy007))).fv) 0)
  have fresh_046 : alphaDummy000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_047 : alphaDummy001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have fresh_049 :
    alphaDummy002 ∉
      (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
            (Wff.classMem (Class.cv alphaDummy001) B))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
              (Wff.classMem (Class.cv alphaDummy001) B))).fv)
        0
  have fresh_050 :
    alphaDummy003 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)
        0
  have support_mem_0000 :
    alphaDummy000 ∈
      (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
            (Wff.classMem (Class.cv alphaDummy001) B))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    exact Finset.mem_singleton_self _
  have support_mem_0001 :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alphaDummy001 ∈
      (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
            (Wff.classMem (Class.cv alphaDummy001) B))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have support_mem_0004 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy004
              (synWrex alphaDummy005 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
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
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0006 : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 :
    x ∈
      (((synCcompl (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCun (synCphi (Class.cv alphaDummy007))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alphaDummy000 ∈
      (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv ∪ ((Class.cab alphaDummy004
            (synWrex alphaDummy005 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCphi (Class.cv alphaDummy005)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0009 :
    x ∈
      (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv ∪ ((Class.cab alphaDummy006
            (synWrex alphaDummy007 (Class.cv x) (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0010 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 : alphaDummy007 ∈ (((Class.cv alphaDummy007)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
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
  have support_mem_0013 :
    alphaDummy014 ∈
      (((Wff.classMem (Class.cv alphaDummy014) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy014) (synC1c))).fv ∪
        ((Class.cv alphaDummy014)).fv) :=
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
  have support_mem_0014 :
    alphaDummy012 ∈ (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
        ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy020 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
        ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy023 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alphaDummy023 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alphaDummy019 ∈
      (((synCcompl (Class.cv alphaDummy019))).fv ∪
        ((synCcompl (Class.cv alphaDummy020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    alphaDummy022 ∈
      (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0027 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alphaDummy020 ∈
      (((synCcompl (Class.cv alphaDummy019))).fv ∪
        ((synCcompl (Class.cv alphaDummy020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alphaDummy023 ∈
      (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0030 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    alphaDummy023 ∈
      (((Class.cv alphaDummy023)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0032 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0033 :
    alphaDummy001 ∈
      (((synCcompl (Class.cab alphaDummy004
              (synWrex alphaDummy005 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy004)
                  (synCphi (Class.cv alphaDummy005))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
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
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0034 : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0035 :
    y ∈
      (((synCcompl (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCun (synCphi (Class.cv alphaDummy007))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0036 :
    alphaDummy001 ∈
      (((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy004 (synWrex alphaDummy005 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy004)
                (synCun (synCphi (Class.cv alphaDummy005)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0037 :
    y ∈
      (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv y)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0038 :
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
  have support_mem_0039 :
    alphaDummy007 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy007)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0040 :
    alphaDummy005 ∈
      (((synCphi (Class.cv alphaDummy005))).fv ∪
        ((synCphi (Class.cv alphaDummy005))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0041 :
    alphaDummy007 ∈
      (((synCphi (Class.cv alphaDummy007))).fv ∪
        ((synCphi (Class.cv alphaDummy007))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have wpp_notmem_0000 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0001 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0002 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0003 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0004 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : y ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alphaDummy013 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alphaDummy015 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy014 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alphaDummy016 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alphaDummy017 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy018 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy021 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy019 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alphaDummy022 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy020 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy023 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0000 :
    TReflOn
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have wpp_notmem_0026 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0028 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : y ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alphaDummy013 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alphaDummy015 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alphaDummy014 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alphaDummy016 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alphaDummy017 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alphaDummy018 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alphaDummy021 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alphaDummy019 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alphaDummy022 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alphaDummy020 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : alphaDummy023 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
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
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy019) (Class.cv alphaDummy020))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy018)
            (synCun (Class.cv alphaDummy019) (Class.cv alphaDummy020)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy022) (Class.cv alphaDummy023))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy021)
            (synCun (Class.cv alphaDummy022) (Class.cv alphaDummy023))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
            (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
            (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
            (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
            (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
            (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0052 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : y ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alphaDummy008 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alphaDummy009 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alphaDummy010 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alphaDummy011 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0062 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0063 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0064 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0065 : alphaDummy007 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0066 : alphaDummy013 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0067 : alphaDummy015 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0068 : alphaDummy012 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0069 : alphaDummy014 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0070 : alphaDummy016 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0071 : alphaDummy017 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy016, alphaDummy017), (alphaDummy012, alphaDummy014),
        (alphaDummy013, alphaDummy015), (alphaDummy005, alphaDummy007),
        (alphaDummy004, alphaDummy006), (alphaDummy010, alphaDummy011),
        (alphaDummy008, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy002, alphaDummy003)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
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
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy005) (Class.cv alphaDummy000)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy004) (synCphi (Class.cv alphaDummy005)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy007) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy006) (synCphi (Class.cv alphaDummy007))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) (by decide))
              (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                      (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy010, alphaDummy011), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg splitAlpha0000)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy016, alphaDummy017),
                                (alphaDummy012, alphaDummy014),
                                (alphaDummy013, alphaDummy015),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy010, alphaDummy011),
                                (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy016, alphaDummy017),
                                (alphaDummy012, alphaDummy014),
                                (alphaDummy013, alphaDummy015),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy010, alphaDummy011),
                                (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0072 : alphaDummy034 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alphaDummy035 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alphaDummy036 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alphaDummy037 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0076 : alphaDummy038 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0077 : alphaDummy039 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0078 : alphaDummy034 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alphaDummy035 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alphaDummy036 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alphaDummy037 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0082 : alphaDummy038 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0083 : alphaDummy039 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy019) (Class.cv alphaDummy020))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy018)
            (synCun (Class.cv alphaDummy019) (Class.cv alphaDummy020)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy022) (Class.cv alphaDummy023))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy021)
            (synCun (Class.cv alphaDummy022) (Class.cv alphaDummy023))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
            (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
            (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
            (alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
            (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
            (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
            (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy012)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0084 : alphaDummy034 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alphaDummy035 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alphaDummy036 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alphaDummy037 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0088 : alphaDummy038 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0089 : alphaDummy039 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alphaDummy016, alphaDummy017), (alphaDummy012, alphaDummy014),
        (alphaDummy013, alphaDummy015), (alphaDummy038, alphaDummy039),
        (alphaDummy036, alphaDummy037), (alphaDummy005, alphaDummy007),
        (alphaDummy004, alphaDummy006), (alphaDummy034, alphaDummy035),
        (alphaDummy008, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy002, alphaDummy003)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy038) (synCphi (Class.cv alphaDummy005)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy038)
            (synCphi (Class.cv alphaDummy005)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy039) (synCphi (Class.cv alphaDummy007)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy039)
            (synCphi (Class.cv alphaDummy007))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                    (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy020, alphaDummy023),
        (alphaDummy019, alphaDummy022), (alphaDummy018, alphaDummy021),
        (alphaDummy016, alphaDummy017), (alphaDummy012, alphaDummy014),
        (alphaDummy013, alphaDummy015), (alphaDummy038, alphaDummy039),
        (alphaDummy036, alphaDummy037), (alphaDummy005, alphaDummy007),
        (alphaDummy004, alphaDummy006), (alphaDummy034, alphaDummy035),
        (alphaDummy008, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy002, alphaDummy003)] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy016, alphaDummy017),
                              (alphaDummy012, alphaDummy014),
                              (alphaDummy013, alphaDummy015),
                              (alphaDummy038, alphaDummy039),
                              (alphaDummy036, alphaDummy037),
                              (alphaDummy005, alphaDummy007),
                              (alphaDummy004, alphaDummy006),
                              (alphaDummy034, alphaDummy035),
                              (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                              (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy016, alphaDummy017),
                              (alphaDummy012, alphaDummy014),
                              (alphaDummy013, alphaDummy015),
                              (alphaDummy038, alphaDummy039),
                              (alphaDummy036, alphaDummy037),
                              (alphaDummy005, alphaDummy007),
                              (alphaDummy004, alphaDummy006),
                              (alphaDummy034, alphaDummy035),
                              (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                              (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                            (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy005)).fv) (by decide))
                      (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy020, alphaDummy023), (alphaDummy019, alphaDummy022),
        (alphaDummy018, alphaDummy021), (alphaDummy016, alphaDummy017),
        (alphaDummy012, alphaDummy014), (alphaDummy013, alphaDummy015),
        (alphaDummy038, alphaDummy039), (alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg splitAlpha0002)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy016, alphaDummy017),
                                (alphaDummy012, alphaDummy014),
                                (alphaDummy013, alphaDummy015),
                                (alphaDummy038, alphaDummy039),
                                (alphaDummy036, alphaDummy037),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy034, alphaDummy035),
                                (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy016, alphaDummy017),
                                (alphaDummy012, alphaDummy014),
                                (alphaDummy013, alphaDummy015),
                                (alphaDummy038, alphaDummy039),
                                (alphaDummy036, alphaDummy037),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy034, alphaDummy035),
                                (alphaDummy008, alphaDummy009), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0090 : alphaDummy002 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0091 : alphaDummy003 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0092 : alphaDummy000 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0093 : x ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0094 : alphaDummy001 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0095 : y ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0096 : alphaDummy008 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0097 : alphaDummy009 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0098 : alphaDummy034 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0099 : alphaDummy035 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0100 : alphaDummy004 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0101 : alphaDummy006 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0102 : alphaDummy005 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0103 : alphaDummy007 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0104 : alphaDummy036 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0105 : alphaDummy037 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alphaDummy036, alphaDummy037), (alphaDummy005, alphaDummy007),
        (alphaDummy004, alphaDummy006), (alphaDummy034, alphaDummy035),
        (alphaDummy008, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy002, alphaDummy003)]
      ((synCcompl (synCsn (synC0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu))
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
                      (TAlphaVar.free (by simp) (by simp))))))))))
  have splitAlpha0004 :
    TAlphaWff
      [(alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (Wff.classEq (Class.cv alphaDummy002)
        (synCop (Class.cv alphaDummy000) (Class.cv alphaDummy001)))
      (Wff.classEq (Class.cv alphaDummy003) (synCop (Class.cv x) (Class.cv y))) :=
    (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy001)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy001)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy036, alphaDummy037),
        (alphaDummy005, alphaDummy007), (alphaDummy004, alphaDummy006),
        (alphaDummy034, alphaDummy035), (alphaDummy008, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
                                        (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))))))))))
  have focused_notmem_0000 : alphaDummy002 ∉ A.fv :=
    by
    change
      freshVar
          (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
            ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
                (Wff.classMem (Class.cv alphaDummy001) B))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wa (Wff.classMem (Class.cv alphaDummy000) A)
                  (Wff.classMem (Class.cv alphaDummy001) B)).symm ▸ (Finset.mem_union_left _
                (((fv_wff_classMem (Class.cv alphaDummy000) A).symm ▸
                  (Finset.mem_union_right _ (hu))))))))
  have wpp_notmem_0106 : alphaDummy002 ∉ (A).fv := by exact focused_notmem_0000
  have focused_notmem_0001 : alphaDummy003 ∉ A.fv :=
    by
    change
      freshVar
          (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                  (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_left _
                (((fv_wff_classMem (Class.cv x) A).symm ▸ (Finset.mem_union_right _ (hu))))))))
  have wpp_notmem_0107 : alphaDummy003 ∉ (A).fv := by exact focused_notmem_0001
  have focused_notmem_0002 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0108 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0002
  have wpp_notmem_0109 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0003 : alphaDummy001 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0110 : alphaDummy001 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0111 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0007 :
    TReflOn
      [(alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))
  have focused_notmem_0004 : alphaDummy002 ∉ B.fv :=
    by
    change
      freshVar
          (({ alphaDummy000 } : Finset Var) ∪ ({ alphaDummy001 } : Finset Var) ∪
            ((synWa (Wff.classMem (Class.cv alphaDummy000) A)
                (Wff.classMem (Class.cv alphaDummy001) B))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wa (Wff.classMem (Class.cv alphaDummy000) A)
                  (Wff.classMem (Class.cv alphaDummy001) B)).symm ▸ (Finset.mem_union_right _
                (((fv_wff_classMem (Class.cv alphaDummy001) B).symm ▸
                  (Finset.mem_union_right _ (hu))))))))
  have wpp_notmem_0112 : alphaDummy002 ∉ (B).fv := by exact focused_notmem_0004
  have focused_notmem_0005 : alphaDummy003 ∉ B.fv :=
    by
    change
      freshVar
          (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                  (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_right _
                (((fv_wff_classMem (Class.cv y) B).symm ▸ (Finset.mem_union_right _ (hu))))))))
  have wpp_notmem_0113 : alphaDummy003 ∉ (B).fv := by exact focused_notmem_0005
  have focused_notmem_0006 : alphaDummy000 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0114 : alphaDummy000 ∉ (B).fv := by exact focused_notmem_0006
  have wpp_notmem_0115 : x ∉ (B).fv := by exact dv_B_x
  have focused_notmem_0007 : alphaDummy001 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0116 : alphaDummy001 ∉ (B).fv := by exact focused_notmem_0007
  have wpp_notmem_0117 : y ∉ (B).fv := by exact dv_B_y
  have wpp_refl_0008 :
    TReflOn
      [(alphaDummy001, y), (alphaDummy000, x), (alphaDummy002, alphaDummy003)]
      (B).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0112) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0113) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj splitAlpha0004
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                      dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                    [(alphaDummy001, y), (alphaDummy000, x),
                      (alphaDummy002, alphaDummy003)] A wpp_refl_0007))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfReflOn [(alphaDummy001, y), (alphaDummy000, x),
                      (alphaDummy002, alphaDummy003)] B wpp_refl_0008)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
