/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001034OpReflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_op`. -/
@[expose]
noncomputable def nominalDfOp (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCop A B)
        (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
            (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alphaDummy002 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy000 (synWrex alphaDummy001 A
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCphi (Class.cv alphaDummy001))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy000 (synWrex alphaDummy001 B
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy003 : Var :=
    (freshVar (((synCcompl (Class.cab x
              (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))).fv ∪
        ((synCcompl (Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                  (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab alphaDummy000 (synWrex alphaDummy001 A
              (Wff.classEq (Class.cv alphaDummy000)
                (synCphi (Class.cv alphaDummy001)))))).fv ∪ ((Class.cab alphaDummy000
            (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                (synCphi (Class.cv alphaDummy001)))))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cab x
            (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv ∪
        ((Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv) 0)
  let alphaDummy006 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy007 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 1)
  let alphaDummy008 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alphaDummy009 : Var := (freshVar (((Class.cv y)).fv) 1)
  let alphaDummy010 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy006) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy006) (synC1c))).fv ∪
        ((Class.cv alphaDummy006)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy008) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy008) (synC1c))).fv ∪
        ((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy014 : Var :=
    (freshVar (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy018 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv ∪
        ((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy014)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy013))).fv ∪
        ((synCcompl (Class.cv alphaDummy014))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy013)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy014)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((Class.cab alphaDummy000 (synWrex alphaDummy001 B
              (Wff.classEq (Class.cv alphaDummy000)
                (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy000 (synWrex alphaDummy001 B
              (Wff.classEq (Class.cv alphaDummy000)
                (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv ∪ ((Class.cab x
            (synWrex y B (Wff.classEq (Class.cv x)
                (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar
      (((synCcompl (synCphi (Class.cv y)))).fv ∪ ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy001))).fv ∪
        ((synCphi (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((synCphi (Class.cv y))).fv ∪ ((synCphi (Class.cv y))).fv) 0)
  have fresh_000 :
    alphaDummy004 ∉
      (((Class.cab alphaDummy000 (synWrex alphaDummy001 A
              (Wff.classEq (Class.cv alphaDummy000)
                (synCphi (Class.cv alphaDummy001)))))).fv ∪ ((Class.cab alphaDummy000
            (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                (synCphi (Class.cv alphaDummy001)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy000 (synWrex alphaDummy001 A
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCphi (Class.cv alphaDummy001)))))).fv ∪ ((Class.cab alphaDummy000
              (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                  (synCphi (Class.cv alphaDummy001)))))).fv)
        0
  have fresh_001 :
    alphaDummy028 ∉
      (((Class.cab alphaDummy000 (synWrex alphaDummy001 B
              (Wff.classEq (Class.cv alphaDummy000)
                (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy000 (synWrex alphaDummy001 B
              (Wff.classEq (Class.cv alphaDummy000)
                (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy000 (synWrex alphaDummy001 B
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv ∪
          ((Class.cab alphaDummy000 (synWrex alphaDummy001 B
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv)
        0
  have fresh_002 :
    alphaDummy005 ∉
      (((Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv ∪
        ((Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv ∪
          ((Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv)
        0
  have fresh_003 :
    alphaDummy029 ∉
      (((Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv ∪ ((Class.cab x
            (synWrex y B (Wff.classEq (Class.cv x)
                (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                  (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv ∪ ((Class.cab x
              (synWrex y B (Wff.classEq (Class.cv x)
                  (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv)
        0
  have fresh_030 :
    alphaDummy002 ∉
      (((synCcompl (Class.cab alphaDummy000 (synWrex alphaDummy001 A
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCphi (Class.cv alphaDummy001))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy000 (synWrex alphaDummy001 B
                (Wff.classEq (Class.cv alphaDummy000)
                  (synCun (synCphi (Class.cv alphaDummy001))
                    (synCsn (synC0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCcompl (Class.cab alphaDummy000 (synWrex alphaDummy001 A
                  (Wff.classEq (Class.cv alphaDummy000)
                    (synCphi (Class.cv alphaDummy001))))))).fv ∪ ((synCcompl
              (Class.cab alphaDummy000 (synWrex alphaDummy001 B
                  (Wff.classEq (Class.cv alphaDummy000)
                    (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c)))))))).fv)
        0
  have fresh_031 :
    alphaDummy003 ∉
      (((synCcompl (Class.cab x
              (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))).fv ∪
        ((synCcompl (Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                  (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCcompl (Class.cab x
                (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))).fv ∪
          ((synCcompl (Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                    (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))))).fv)
        0
  have fresh_040 : alphaDummy000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_041 : alphaDummy001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have support_mem_0000 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 : y ∈ (((Class.cv y)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alphaDummy006 ∈
      (((Wff.classMem (Class.cv alphaDummy006) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy006) (synC1c))).fv ∪
        ((Class.cv alphaDummy006)).fv) :=
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
  have support_mem_0003 :
    alphaDummy008 ∈
      (((Wff.classMem (Class.cv alphaDummy008) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy008) (synC1c))).fv ∪
        ((Class.cv alphaDummy008)).fv) :=
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
  have support_mem_0004 :
    alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
    alphaDummy013 ∈
      (((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv ∪
        ((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 :
    alphaDummy016 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alphaDummy013 ∈
      (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
    alphaDummy014 ∈
      (((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv ∪
        ((synCnin (Class.cv alphaDummy013) (Class.cv alphaDummy014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alphaDummy017 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alphaDummy014 ∈
      (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alphaDummy013 ∈
      (((synCcompl (Class.cv alphaDummy013))).fv ∪
        ((synCcompl (Class.cv alphaDummy014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy016 ∈
      (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy013 ∈
      (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy013)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy014 ∈
      (((synCcompl (Class.cv alphaDummy013))).fv ∪
        ((synCcompl (Class.cv alphaDummy014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy017 ∈
      (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy014 ∈
      (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alphaDummy001 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    y ∈
      (((synCcompl (synCphi (Class.cv y)))).fv ∪ ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alphaDummy001 ∈
      (((synCphi (Class.cv alphaDummy001))).fv ∪
        ((synCphi (Class.cv alphaDummy001))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    y ∈ (((synCphi (Class.cv y))).fv ∪ ((synCphi (Class.cv y))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alphaDummy001 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0001 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0002 : alphaDummy002 ∉ A.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab alphaDummy000 (synWrex alphaDummy001 A
                    (Wff.classEq (Class.cv alphaDummy000)
                      (synCphi (Class.cv alphaDummy001))))))).fv ∪ ((synCcompl
                (Class.cab alphaDummy000 (synWrex alphaDummy001 B
                    (Wff.classEq (Class.cv alphaDummy000)
                      (synCun (synCphi (Class.cv alphaDummy001))
                        (synCsn (synC0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alphaDummy000
                    (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                        (synCphi (Class.cv alphaDummy001)))))).symm ▸
              (((fv_class_cab alphaDummy000 (synWrex alphaDummy001 A
                      (Wff.classEq (Class.cv alphaDummy000)
                        (synCphi (Class.cv alphaDummy001))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)),
                    (((fv_syn_wrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                            (synCphi (Class.cv alphaDummy001)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0000 : alphaDummy002 ∉ (A).fv := by exact focused_notmem_0002
  have focused_notmem_0003 : alphaDummy003 ∉ A.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab x (synWrex y A
                    (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))).fv ∪ ((synCcompl
                (Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                      (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab x (synWrex y A
                      (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).symm ▸
              (((fv_class_cab x (synWrex y A
                      (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))).symm ▸
                (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (((fv_syn_wrex y A
                          (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (dv_A_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0001 : alphaDummy003 ∉ (A).fv := by exact focused_notmem_0003
  have focused_notmem_0004 : alphaDummy004 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy000 (synWrex alphaDummy001 A
                  (Wff.classEq (Class.cv alphaDummy000)
                    (synCphi (Class.cv alphaDummy001)))))).fv ∪ ((Class.cab alphaDummy000
                (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                    (synCphi (Class.cv alphaDummy001)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alphaDummy000
                  (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                      (synCphi (Class.cv alphaDummy001))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)),
                  (((fv_syn_wrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                          (synCphi (Class.cv alphaDummy001)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0002 : alphaDummy004 ∉ (A).fv := by exact focused_notmem_0004
  have focused_notmem_0005 : alphaDummy005 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab x
                (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv ∪
            ((Class.cab x
                (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab x (synWrex y A
                    (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))).symm ▸
              (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (((fv_syn_wrex y A
                        (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0003 : alphaDummy005 ∉ (A).fv := by exact focused_notmem_0005
  have wpp_notmem_0004 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0001
  have wpp_notmem_0005 : x ∉ (A).fv := by exact dv_A_x
  have wpp_notmem_0006 : alphaDummy001 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0007 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0000 :
    TReflOn
      [(alphaDummy001, y), (alphaDummy000, x), (alphaDummy004, alphaDummy005),
        (alphaDummy002, alphaDummy003)]
      (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp))))))
  have wpp_notmem_0008 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : y ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alphaDummy015 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy013 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy016 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alphaDummy014 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy017 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy004, alphaDummy005),
        (alphaDummy002, alphaDummy003)]
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
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have wpp_notmem_0028 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : y ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alphaDummy015 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alphaDummy013 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alphaDummy016 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alphaDummy014 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alphaDummy017 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy004, alphaDummy005),
        (alphaDummy002, alphaDummy003)]
      ((synC0)).fv :=
    by
    intro u hu
    exact
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
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy004, alphaDummy005),
        (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy013) (Class.cv alphaDummy014))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy012)
            (synCun (Class.cv alphaDummy013) (Class.cv alphaDummy014)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy016) (Class.cv alphaDummy017))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy015)
            (synCun (Class.cv alphaDummy016) (Class.cv alphaDummy017))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
            (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
            (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
            (alphaDummy001, y), (alphaDummy000, x),
            (alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0048 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0049 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0050 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0051 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0052 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : y ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alphaDummy007 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : alphaDummy009 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alphaDummy008 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alphaDummy010 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alphaDummy011 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alphaDummy010, alphaDummy011), (alphaDummy006, alphaDummy008),
        (alphaDummy007, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
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
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have splitAlpha0001 :
    TAlphaWff [(alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy004) (Class.cab alphaDummy000
            (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                (synCphi (Class.cv alphaDummy001)))))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy004) (Class.cab alphaDummy000
              (synWrex alphaDummy001 A (Wff.classEq (Class.cv alphaDummy000)
                  (synCphi (Class.cv alphaDummy001))))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy005)
          (Class.cab x (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy005) (Class.cab x
              (synWrex y A (Wff.classEq (Class.cv x) (synCphi (Class.cv y)))))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn [(alphaDummy001, y), (alphaDummy000, x),
                    (alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
                  A wpp_refl_0000)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective (((Class.cv alphaDummy001)).fv)
                              (by decide)) (freshVar_injective (((Class.cv y)).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [(alphaDummy014, alphaDummy017),
        (alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy010, alphaDummy011), (alphaDummy006, alphaDummy008),
        (alphaDummy007, alphaDummy009), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg splitAlpha0000)))))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [(alphaDummy010, alphaDummy011),
                                      (alphaDummy006, alphaDummy008),
                                      (alphaDummy007, alphaDummy009),
                                      (alphaDummy001, y), (alphaDummy000, x),
                                      (alphaDummy004, alphaDummy005),
                                      (alphaDummy002, alphaDummy003)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [(alphaDummy010, alphaDummy011),
                                      (alphaDummy006, alphaDummy008),
                                      (alphaDummy007, alphaDummy009),
                                      (alphaDummy001, y), (alphaDummy000, x),
                                      (alphaDummy004, alphaDummy005),
                                      (alphaDummy002, alphaDummy003)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfReflOn [(alphaDummy001, y), (alphaDummy000, x),
                      (alphaDummy004, alphaDummy005), (alphaDummy002, alphaDummy003)]
                    A wpp_refl_0000)) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                      dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                                (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there
                              (freshVar_injective (((Class.cv alphaDummy001)).fv) (by decide))
                              (freshVar_injective (((Class.cv y)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003
        0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy004, alphaDummy005),
        (alphaDummy002, alphaDummy003)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.neg splitAlpha0000))))))) (TAlphaWff.classMem (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy010, alphaDummy011),
                                        (alphaDummy006, alphaDummy008),
                                        (alphaDummy007, alphaDummy009),
                                        (alphaDummy001, y), (alphaDummy000, x),
                                        (alphaDummy004, alphaDummy005),
                                        (alphaDummy002, alphaDummy003)]
                                      (synCnnc) (by simp only [fv_syn_cnnc])))))
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                      [(alphaDummy010, alphaDummy011),
                                        (alphaDummy006, alphaDummy008),
                                        (alphaDummy007, alphaDummy009),
                                        (alphaDummy001, y), (alphaDummy000, x),
                                        (alphaDummy004, alphaDummy005),
                                        (alphaDummy002, alphaDummy003)] (synCnnc)
                                      (by simp only [fv_syn_cnnc]))))))))))))))))))
  have focused_notmem_0006 : alphaDummy001 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0007 : alphaDummy000 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0008 : alphaDummy002 ∉ B.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab alphaDummy000 (synWrex alphaDummy001 A
                    (Wff.classEq (Class.cv alphaDummy000)
                      (synCphi (Class.cv alphaDummy001))))))).fv ∪ ((synCcompl
                (Class.cab alphaDummy000 (synWrex alphaDummy001 B
                    (Wff.classEq (Class.cv alphaDummy000)
                      (synCun (synCphi (Class.cv alphaDummy001))
                        (synCsn (synC0c)))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab alphaDummy000
                    (synWrex alphaDummy001 B (Wff.classEq (Class.cv alphaDummy000)
                        (synCun (synCphi (Class.cv alphaDummy001))
                          (synCsn (synC0c))))))).symm ▸ (((fv_class_cab alphaDummy000
                    (synWrex alphaDummy001 B (Wff.classEq (Class.cv alphaDummy000)
                        (synCun (synCphi (Class.cv alphaDummy001))
                          (synCsn (synC0c)))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)),
                    (((fv_syn_wrex alphaDummy001 B (Wff.classEq (Class.cv alphaDummy000)
                            (synCun (synCphi (Class.cv alphaDummy001))
                              (synCsn (synC0c))))).symm ▸ (Finset.mem_union_left _
                        (Finset.mem_erase.mpr ⟨(fun h_eq => (focused_notmem_0006) (h_eq ▸ hu)),
                            (hu)⟩))))⟩))))))
  have wpp_notmem_0062 : alphaDummy002 ∉ (B).fv := by exact focused_notmem_0008
  have focused_notmem_0009 : alphaDummy003 ∉ B.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab x (synWrex y A
                    (Wff.classEq (Class.cv x) (synCphi (Class.cv y))))))).fv ∪ ((synCcompl
                (Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                      (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab x (synWrex y B
                      (Wff.classEq (Class.cv x)
                        (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).symm ▸
              (((fv_class_cab x (synWrex y B (Wff.classEq (Class.cv x)
                        (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))).symm ▸
                (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_B_x) (h_eq ▸ hu)), (((fv_syn_wrex y B
                          (Wff.classEq (Class.cv x)
                            (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (dv_B_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0063 : alphaDummy003 ∉ (B).fv := by exact focused_notmem_0009
  have focused_notmem_0010 : alphaDummy028 ∉ B.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy000 (synWrex alphaDummy001 B
                  (Wff.classEq (Class.cv alphaDummy000)
                    (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv ∪
            ((Class.cab alphaDummy000 (synWrex alphaDummy001 B
                  (Wff.classEq (Class.cv alphaDummy000)
                    (synCun (synCphi (Class.cv alphaDummy001)) (synCsn (synC0c))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alphaDummy000
                  (synWrex alphaDummy001 B (Wff.classEq (Class.cv alphaDummy000)
                      (synCun (synCphi (Class.cv alphaDummy001))
                        (synCsn (synC0c)))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)),
                  (((fv_syn_wrex alphaDummy001 B (Wff.classEq (Class.cv alphaDummy000)
                          (synCun (synCphi (Class.cv alphaDummy001))
                            (synCsn (synC0c))))).symm ▸ (Finset.mem_union_left _
                      (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0006) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0064 : alphaDummy028 ∉ (B).fv := by exact focused_notmem_0010
  have focused_notmem_0011 : alphaDummy029 ∉ B.fv :=
    by
    change
      freshVar
          (((Class.cab x (synWrex y B (Wff.classEq (Class.cv x)
                    (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv ∪ ((Class.cab x
                (synWrex y B (Wff.classEq (Class.cv x)
                    (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab x (synWrex y B
                    (Wff.classEq (Class.cv x)
                      (synCun (synCphi (Class.cv y)) (synCsn (synC0c)))))).symm ▸
              (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_B_x) (h_eq ▸ hu)), (((fv_syn_wrex y B
                        (Wff.classEq (Class.cv x)
                          (synCun (synCphi (Class.cv y)) (synCsn (synC0c))))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_B_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0065 : alphaDummy029 ∉ (B).fv := by exact focused_notmem_0011
  have wpp_notmem_0066 : alphaDummy000 ∉ (B).fv := by exact focused_notmem_0007
  have wpp_notmem_0067 : x ∉ (B).fv := by exact dv_B_x
  have wpp_notmem_0068 : alphaDummy001 ∉ (B).fv := by exact focused_notmem_0006
  have wpp_notmem_0069 : y ∉ (B).fv := by exact dv_B_y
  have wpp_refl_0004 :
    TReflOn
      [(alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)]
      (B).fv :=
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
              (TAlphaVar.free (by simp) (by simp))))))
  have wpp_notmem_0070 : alphaDummy028 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0071 : alphaDummy029 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0072 : alphaDummy030 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alphaDummy031 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alphaDummy032 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alphaDummy033 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)]
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
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have wpp_notmem_0076 : alphaDummy028 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0077 : alphaDummy029 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0078 : alphaDummy030 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alphaDummy031 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alphaDummy032 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alphaDummy033 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)]
      ((synC0)).fv :=
    by
    intro u hu
    exact
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0034) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0035) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy013) (Class.cv alphaDummy014))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy012)
            (synCun (Class.cv alphaDummy013) (Class.cv alphaDummy014)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy016) (Class.cv alphaDummy017))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy015)
            (synCun (Class.cv alphaDummy016) (Class.cv alphaDummy017))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
            (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
            (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
            (alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
            (alphaDummy001, y), (alphaDummy000, x),
            (alphaDummy028, alphaDummy029), (alphaDummy002, alphaDummy003)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy006)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0082 : alphaDummy028 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alphaDummy029 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alphaDummy030 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alphaDummy031 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alphaDummy032 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alphaDummy033 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alphaDummy010, alphaDummy011), (alphaDummy006, alphaDummy008),
        (alphaDummy007, alphaDummy009), (alphaDummy032, alphaDummy033),
        (alphaDummy030, alphaDummy031), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy028, alphaDummy029), (alphaDummy002, alphaDummy003)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy032) (synCphi (Class.cv alphaDummy001)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy032)
            (synCphi (Class.cv alphaDummy001)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy033) (synCphi (Class.cv y)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy033) (synCphi (Class.cv y))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy001)).fv) (by decide))
                    (freshVar_injective (((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy014, alphaDummy017),
        (alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy010, alphaDummy011), (alphaDummy006, alphaDummy008),
        (alphaDummy007, alphaDummy009), (alphaDummy032, alphaDummy033),
        (alphaDummy030, alphaDummy031), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy028, alphaDummy029), (alphaDummy002, alphaDummy003)]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy010, alphaDummy011),
                              (alphaDummy006, alphaDummy008),
                              (alphaDummy007, alphaDummy009),
                              (alphaDummy032, alphaDummy033),
                              (alphaDummy030, alphaDummy031), (alphaDummy001, y),
                              (alphaDummy000, x), (alphaDummy028, alphaDummy029),
                              (alphaDummy002, alphaDummy003)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy010, alphaDummy011),
                              (alphaDummy006, alphaDummy008),
                              (alphaDummy007, alphaDummy009),
                              (alphaDummy032, alphaDummy033),
                              (alphaDummy030, alphaDummy031), (alphaDummy001, y),
                              (alphaDummy000, x), (alphaDummy028, alphaDummy029),
                              (alphaDummy002, alphaDummy003)]
                            (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy001)).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy014, alphaDummy017), (alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy010, alphaDummy011),
        (alphaDummy006, alphaDummy008), (alphaDummy007, alphaDummy009),
        (alphaDummy032, alphaDummy033), (alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)] (synC1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy010, alphaDummy011),
                                (alphaDummy006, alphaDummy008),
                                (alphaDummy007, alphaDummy009),
                                (alphaDummy032, alphaDummy033),
                                (alphaDummy030, alphaDummy031), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy028, alphaDummy029),
                                (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy010, alphaDummy011),
                                (alphaDummy006, alphaDummy008),
                                (alphaDummy007, alphaDummy009),
                                (alphaDummy032, alphaDummy033),
                                (alphaDummy030, alphaDummy031), (alphaDummy001, y),
                                (alphaDummy000, x), (alphaDummy028, alphaDummy029),
                                (alphaDummy002, alphaDummy003)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0088 : alphaDummy002 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0089 : alphaDummy003 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0090 : alphaDummy028 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0091 : alphaDummy029 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
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
  have wpp_notmem_0096 : alphaDummy030 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0097 : alphaDummy031 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_refl_0008 :
    TReflOn
      [(alphaDummy030, alphaDummy031), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy028, alphaDummy029), (alphaDummy002, alphaDummy003)]
      ((synCcompl (synCsn (synC0c)))).fv :=
    by
    intro u hu
    exact
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
                (TAlphaVar.free (by simp) (by simp)))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg splitAlpha0001))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn
                                [(alphaDummy001, y), (alphaDummy000, x),
                                  (alphaDummy028, alphaDummy029),
                                  (alphaDummy002, alphaDummy003)] B wpp_refl_0004))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)] (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn
                                [(alphaDummy001, y), (alphaDummy000, x),
                                  (alphaDummy028, alphaDummy029),
                                  (alphaDummy002, alphaDummy003)] B wpp_refl_0004))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy030, alphaDummy031),
        (alphaDummy001, y), (alphaDummy000, x), (alphaDummy028, alphaDummy029),
        (alphaDummy002, alphaDummy003)] (synCcompl (synCsn (synC0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
