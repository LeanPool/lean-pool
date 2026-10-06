/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001047FvReflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_fv`. -/
@[expose]
noncomputable def nominalDfFv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.classEq (synCfv F A) (synCio x (synWbr A F (.cv x)))) :=
  by
  let alphaDummy000 : Var := (freshVar ((F).fv ∪ (A).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar
      (({ alphaDummy000 } : Finset Var) ∪ ((synWbr A F (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy002 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ((synWbr A F (Class.cv x))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy001 (Wff.classEq
            (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
            (synCsn (Class.cv alphaDummy001))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab alphaDummy001 (Wff.classEq
            (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
            (synCsn (Class.cv alphaDummy001))))).fv) 1)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
            (synCsn (Class.cv alphaDummy002))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
            (synCsn (Class.cv alphaDummy002))))).fv) 1)
  let alphaDummy007 : Var := (freshVar ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy008 : Var := (freshVar ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy009 : Var := (freshVar ((A).fv ∪ ((Class.cv x)).fv) 0)
  let alphaDummy010 : Var := (freshVar ((A).fv ∪ ((Class.cv x)).fv) 1)
  let alphaDummy011 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy007 (synWrex alphaDummy008 A
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy012 : Var :=
    (freshVar (((synCcompl (Class.cab alphaDummy009 (synWrex alphaDummy010 A
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c)))))))).fv)
      0)
  let alphaDummy013 : Var :=
    (freshVar (((Class.cab alphaDummy007 (synWrex alphaDummy008 A
              (Wff.classEq (Class.cv alphaDummy007)
                (synCphi (Class.cv alphaDummy008)))))).fv ∪ ((Class.cab alphaDummy007
            (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                (synCphi (Class.cv alphaDummy008)))))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((Class.cab alphaDummy009 (synWrex alphaDummy010 A
              (Wff.classEq (Class.cv alphaDummy009)
                (synCphi (Class.cv alphaDummy010)))))).fv ∪ ((Class.cab alphaDummy009
            (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                (synCphi (Class.cv alphaDummy010)))))).fv) 0)
  let alphaDummy015 : Var := (freshVar (((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy016 : Var := (freshVar (((Class.cv alphaDummy008)).fv) 1)
  let alphaDummy017 : Var := (freshVar (((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy018 : Var := (freshVar (((Class.cv alphaDummy010)).fv) 1)
  let alphaDummy019 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy015) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy015) (synC1c))).fv ∪
        ((Class.cv alphaDummy015)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy017) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy017) (synC1c))).fv ∪
        ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy027 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy023))).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv ∪
        ((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy025)).fv ∪ ((Class.cv alphaDummy026)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy025))).fv ∪
        ((synCcompl (Class.cv alphaDummy026))).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((Class.cv alphaDummy025)).fv ∪ ((Class.cv alphaDummy025)).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((Class.cv alphaDummy023)).fv ∪ ((Class.cv alphaDummy023)).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((Class.cv alphaDummy026)).fv ∪ ((Class.cv alphaDummy026)).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy007)
                (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy007)
                (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy009)
                (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy009)
                (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c))))))).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy008)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy040 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy010)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy041 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy008))).fv ∪
        ((synCphi (Class.cv alphaDummy008))).fv) 0)
  let alphaDummy042 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy010))).fv ∪
        ((synCphi (Class.cv alphaDummy010))).fv) 0)
  let alphaDummy043 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy044 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  have fresh_000 :
    alphaDummy003 ∉
      (((Class.cab alphaDummy001 (Wff.classEq
            (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
            (synCsn (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy001 (Wff.classEq
              (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
              (synCsn (Class.cv alphaDummy001))))).fv)
        0
  have fresh_001 :
    alphaDummy004 ∉
      (((Class.cab alphaDummy001 (Wff.classEq
            (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
            (synCsn (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy001 (Wff.classEq
              (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
              (synCsn (Class.cv alphaDummy001))))).fv)
        1
  have fresh_003 :
    alphaDummy005 ∉
      (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
            (synCsn (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
              (synCsn (Class.cv alphaDummy002))))).fv)
        0
  have fresh_004 :
    alphaDummy006 ∉
      (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
            (synCsn (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
              (synCsn (Class.cv alphaDummy002))))).fv)
        1
  have fresh_007 :
    alphaDummy013 ∉
      (((Class.cab alphaDummy007 (synWrex alphaDummy008 A
              (Wff.classEq (Class.cv alphaDummy007)
                (synCphi (Class.cv alphaDummy008)))))).fv ∪ ((Class.cab alphaDummy007
            (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                (synCphi (Class.cv alphaDummy008)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy007 (synWrex alphaDummy008 A
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008)))))).fv ∪ ((Class.cab alphaDummy007
              (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008)))))).fv)
        0
  have fresh_009 :
    alphaDummy014 ∉
      (((Class.cab alphaDummy009 (synWrex alphaDummy010 A
              (Wff.classEq (Class.cv alphaDummy009)
                (synCphi (Class.cv alphaDummy010)))))).fv ∪ ((Class.cab alphaDummy009
            (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                (synCphi (Class.cv alphaDummy010)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy009 (synWrex alphaDummy010 A
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010)))))).fv ∪ ((Class.cab alphaDummy009
              (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010)))))).fv)
        0
  have fresh_038 :
    alphaDummy011 ∉
      (((synCcompl (Class.cab alphaDummy007 (synWrex alphaDummy008 A
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCun (synCphi (Class.cv alphaDummy008))
                    (synCsn (synC0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCcompl (Class.cab alphaDummy007 (synWrex alphaDummy008 A
                  (Wff.classEq (Class.cv alphaDummy007)
                    (synCphi (Class.cv alphaDummy008))))))).fv ∪ ((synCcompl
              (Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
                  (Wff.classEq (Class.cv alphaDummy007)
                    (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c)))))))).fv)
        0
  have fresh_039 :
    alphaDummy012 ∉
      (((synCcompl (Class.cab alphaDummy009 (synWrex alphaDummy010 A
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCun (synCphi (Class.cv alphaDummy010))
                    (synCsn (synC0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCcompl (Class.cab alphaDummy009 (synWrex alphaDummy010 A
                  (Wff.classEq (Class.cv alphaDummy009)
                    (synCphi (Class.cv alphaDummy010))))))).fv ∪ ((synCcompl
              (Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
                  (Wff.classEq (Class.cv alphaDummy009)
                    (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c)))))))).fv)
        0
  have fresh_048 : alphaDummy007 ∉ ((A).fv ∪ ((Class.cv alphaDummy000)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 0
  have fresh_049 : alphaDummy008 ∉ ((A).fv ∪ ((Class.cv alphaDummy000)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 1
  have fresh_051 : alphaDummy009 ∉ ((A).fv ∪ ((Class.cv x)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv x)).fv) 0
  have fresh_052 : alphaDummy010 ∉ ((A).fv ∪ ((Class.cv x)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv x)).fv) 1
  have fresh_054 : alphaDummy000 ∉ ((F).fv ∪ (A).fv) := by
    exact freshVar_not_mem ((F).fv ∪ (A).fv) 0
  have fresh_055 :
    alphaDummy001 ∉
      (({ alphaDummy000 } : Finset Var) ∪ ((synWbr A F (Class.cv alphaDummy000))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ alphaDummy000 } : Finset Var) ∪ ((synWbr A F (Class.cv alphaDummy000))).fv)
        0
  have fresh_056 :
    alphaDummy002 ∉ (({ x } : Finset Var) ∪ ((synWbr A F (Class.cv x))).fv) := by
    exact freshVar_not_mem (({ x } : Finset Var) ∪ ((synWbr A F (Class.cv x))).fv) 0
  have support_mem_0000 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alphaDummy015 ∈
      (((Wff.classMem (Class.cv alphaDummy015) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy015) (synC1c))).fv ∪
        ((Class.cv alphaDummy015)).fv) :=
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
    alphaDummy017 ∈
      (((Wff.classMem (Class.cv alphaDummy017) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy017) (synC1c))).fv ∪
        ((Class.cv alphaDummy017)).fv) :=
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
    alphaDummy015 ∈ (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alphaDummy017 ∈ (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
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
  have support_mem_0007 :
    alphaDummy025 ∈
      (((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv ∪
        ((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alphaDummy025 ∈
      (((Class.cv alphaDummy025)).fv ∪ ((Class.cv alphaDummy026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
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
  have support_mem_0011 :
    alphaDummy026 ∈
      (((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv ∪
        ((synCnin (Class.cv alphaDummy025) (Class.cv alphaDummy026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alphaDummy023 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alphaDummy026 ∈
      (((Class.cv alphaDummy025)).fv ∪ ((Class.cv alphaDummy026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alphaDummy022 ∈
      (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy025 ∈
      (((synCcompl (Class.cv alphaDummy025))).fv ∪
        ((synCcompl (Class.cv alphaDummy026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy025 ∈
      (((Class.cv alphaDummy025)).fv ∪ ((Class.cv alphaDummy025)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy023 ∈
      (((synCcompl (Class.cv alphaDummy022))).fv ∪
        ((synCcompl (Class.cv alphaDummy023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy026 ∈
      (((synCcompl (Class.cv alphaDummy025))).fv ∪
        ((synCcompl (Class.cv alphaDummy026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy023 ∈
      (((Class.cv alphaDummy023)).fv ∪ ((Class.cv alphaDummy023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy026 ∈
      (((Class.cv alphaDummy026)).fv ∪ ((Class.cv alphaDummy026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 : alphaDummy000 ∈ ((A).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy007 (synWrex alphaDummy008 A
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy007)
                  (synCun (synCphi (Class.cv alphaDummy008))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0024 : x ∈ ((A).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    x ∈
      (((synCcompl (Class.cab alphaDummy009 (synWrex alphaDummy010 A
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
                (Wff.classEq (Class.cv alphaDummy009)
                  (synCun (synCphi (Class.cv alphaDummy010))
                    (synCsn (synC0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alphaDummy000 ∈
      (((Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy007)
                (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy007)
                (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0027 :
    x ∈
      (((Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy009)
                (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
              (Wff.classEq (Class.cv alphaDummy009)
                (synCun (synCphi (Class.cv alphaDummy010)) (synCsn (synC0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alphaDummy008 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy008)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alphaDummy010 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy010)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0030 :
    alphaDummy008 ∈
      (((synCphi (Class.cv alphaDummy008))).fv ∪
        ((synCphi (Class.cv alphaDummy008))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    alphaDummy010 ∈
      (((synCphi (Class.cv alphaDummy010))).fv ∪
        ((synCphi (Class.cv alphaDummy010))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0032 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0033 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((F).fv ∪ (A).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0001 : alphaDummy001 ∉ A.fv :=
    by
    change
      freshVar
          (({ alphaDummy000 } : Finset Var) ∪ ((synWbr A F (Class.cv alphaDummy000))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
              (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))))
  have focused_notmem_0002 : alphaDummy003 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy001 (Wff.classEq
                (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                (synCsn (Class.cv alphaDummy001))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alphaDummy001 (Wff.classEq
                  (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                  (synCsn (Class.cv alphaDummy001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                      (synCsn (Class.cv alphaDummy001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alphaDummy000
                          (synWbr A F (Class.cv alphaDummy000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
                            (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0000 : alphaDummy003 ∉ (A).fv := by exact focused_notmem_0002
  have focused_notmem_0003 : alphaDummy002 ∉ A.fv :=
    by
    change freshVar (({ x } : Finset Var) ∪ ((synWbr A F (Class.cv x))).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_wbr A F (Class.cv x)).symm ▸
              (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))))
  have focused_notmem_0004 : alphaDummy005 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                (synCsn (Class.cv alphaDummy002))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alphaDummy002
                (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                  (synCsn (Class.cv alphaDummy002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0003) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (synWbr A F (Class.cv x)))
                      (synCsn (Class.cv alphaDummy002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (synWbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0001 : alphaDummy005 ∉ (A).fv := by exact focused_notmem_0004
  have focused_notmem_0005 : alphaDummy004 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy001 (Wff.classEq
                (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                (synCsn (Class.cv alphaDummy001))))).fv)
          1 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alphaDummy001 (Wff.classEq
                  (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                  (synCsn (Class.cv alphaDummy001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                      (synCsn (Class.cv alphaDummy001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alphaDummy000
                          (synWbr A F (Class.cv alphaDummy000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
                            (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0002 : alphaDummy004 ∉ (A).fv := by exact focused_notmem_0005
  have focused_notmem_0006 : alphaDummy006 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                (synCsn (Class.cv alphaDummy002))))).fv)
          1 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alphaDummy002
                (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                  (synCsn (Class.cv alphaDummy002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0003) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (synWbr A F (Class.cv x)))
                      (synCsn (Class.cv alphaDummy002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (synWbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0003 : alphaDummy006 ∉ (A).fv := by exact focused_notmem_0006
  have wpp_notmem_0004 : alphaDummy001 ∉ (A).fv := by exact focused_notmem_0001
  have wpp_notmem_0005 : alphaDummy002 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0006 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0007 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0007 : alphaDummy008 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0008 : alphaDummy007 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv alphaDummy000)).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0009 : alphaDummy011 ∉ A.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab alphaDummy007 (synWrex alphaDummy008 A
                    (Wff.classEq (Class.cv alphaDummy007)
                      (synCphi (Class.cv alphaDummy008))))))).fv ∪ ((synCcompl
                (Class.cab alphaDummy007 (synWrex alphaDummy008 (Class.cv alphaDummy000)
                    (Wff.classEq (Class.cv alphaDummy007)
                      (synCun (synCphi (Class.cv alphaDummy008))
                        (synCsn (synC0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alphaDummy007
                    (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                        (synCphi (Class.cv alphaDummy008)))))).symm ▸
              (((fv_class_cab alphaDummy007 (synWrex alphaDummy008 A
                      (Wff.classEq (Class.cv alphaDummy007)
                        (synCphi (Class.cv alphaDummy008))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0008) (h_eq ▸ hu)),
                    (((fv_syn_wrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                            (synCphi (Class.cv alphaDummy008)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0008 : alphaDummy011 ∉ (A).fv := by exact focused_notmem_0009
  have focused_notmem_0010 : alphaDummy010 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv x)).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0011 : alphaDummy009 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv x)).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0012 : alphaDummy012 ∉ A.fv :=
    by
    change
      freshVar
          (((synCcompl (Class.cab alphaDummy009 (synWrex alphaDummy010 A
                    (Wff.classEq (Class.cv alphaDummy009)
                      (synCphi (Class.cv alphaDummy010))))))).fv ∪ ((synCcompl
                (Class.cab alphaDummy009 (synWrex alphaDummy010 (Class.cv x)
                    (Wff.classEq (Class.cv alphaDummy009)
                      (synCun (synCphi (Class.cv alphaDummy010))
                        (synCsn (synC0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alphaDummy009
                    (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                        (synCphi (Class.cv alphaDummy010)))))).symm ▸
              (((fv_class_cab alphaDummy009 (synWrex alphaDummy010 A
                      (Wff.classEq (Class.cv alphaDummy009)
                        (synCphi (Class.cv alphaDummy010))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0011) (h_eq ▸ hu)),
                    (((fv_syn_wrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                            (synCphi (Class.cv alphaDummy010)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0010) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0009 : alphaDummy012 ∉ (A).fv := by exact focused_notmem_0012
  have focused_notmem_0013 : alphaDummy013 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy007 (synWrex alphaDummy008 A
                  (Wff.classEq (Class.cv alphaDummy007)
                    (synCphi (Class.cv alphaDummy008)))))).fv ∪ ((Class.cab alphaDummy007
                (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                    (synCphi (Class.cv alphaDummy008)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alphaDummy007
                  (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                      (synCphi (Class.cv alphaDummy008))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0008) (h_eq ▸ hu)),
                  (((fv_syn_wrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                          (synCphi (Class.cv alphaDummy008)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0010 : alphaDummy013 ∉ (A).fv := by exact focused_notmem_0013
  have focused_notmem_0014 : alphaDummy014 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy009 (synWrex alphaDummy010 A
                  (Wff.classEq (Class.cv alphaDummy009)
                    (synCphi (Class.cv alphaDummy010)))))).fv ∪ ((Class.cab alphaDummy009
                (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                    (synCphi (Class.cv alphaDummy010)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alphaDummy009
                  (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                      (synCphi (Class.cv alphaDummy010))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0011) (h_eq ▸ hu)),
                  (((fv_syn_wrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                          (synCphi (Class.cv alphaDummy010)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0010) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0011 : alphaDummy014 ∉ (A).fv := by exact focused_notmem_0014
  have wpp_notmem_0012 : alphaDummy007 ∉ (A).fv := by exact focused_notmem_0008
  have wpp_notmem_0013 : alphaDummy009 ∉ (A).fv := by exact focused_notmem_0011
  have wpp_notmem_0014 : alphaDummy008 ∉ (A).fv := by exact focused_notmem_0007
  have wpp_notmem_0015 : alphaDummy010 ∉ (A).fv := by exact focused_notmem_0010
  have wpp_refl_0000 :
    TReflOn
      [(alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (A).fv :=
    by
    intro u hu
    exact
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
                      (TAlphaVar.free (by simp) (by simp))))))))))
  have wpp_notmem_0016 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alphaDummy013 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy014 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0028 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0029 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0031 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy016 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0033 : alphaDummy018 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy015 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0035 : alphaDummy017 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0036 : alphaDummy019 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0037 : alphaDummy020 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0038 : alphaDummy021 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0039 : alphaDummy024 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0040 : alphaDummy022 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0041 : alphaDummy025 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0042 : alphaDummy023 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0043 : alphaDummy026 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have wpp_notmem_0044 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0052 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0053 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0054 : alphaDummy013 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0055 : alphaDummy014 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0056 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0057 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0058 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0059 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0060 : alphaDummy016 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0061 : alphaDummy018 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0062 : alphaDummy015 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0063 : alphaDummy017 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0064 : alphaDummy019 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0065 : alphaDummy020 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0066 : alphaDummy021 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0067 : alphaDummy024 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0068 : alphaDummy022 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0069 : alphaDummy025 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0070 : alphaDummy023 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0071 : alphaDummy026 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      ((synC0)).fv :=
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
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy022) (Class.cv alphaDummy023))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy021)
            (synCun (Class.cv alphaDummy022) (Class.cv alphaDummy023)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy025) (Class.cv alphaDummy026))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy024)
            (synCun (Class.cv alphaDummy025) (Class.cv alphaDummy026))))) :=
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
                                  (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
            (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
            (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
            (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
            (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
            (alphaDummy000, x), (alphaDummy001, alphaDummy002),
            (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
  have wpp_notmem_0072 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0073 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0074 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0075 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0076 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0077 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0078 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0079 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0080 : alphaDummy011 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0081 : alphaDummy012 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0082 : alphaDummy013 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alphaDummy014 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alphaDummy007 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alphaDummy009 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alphaDummy008 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alphaDummy010 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0088 : alphaDummy016 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0089 : alphaDummy018 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0090 : alphaDummy015 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0091 : alphaDummy017 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0092 : alphaDummy019 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0093 : alphaDummy020 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alphaDummy019, alphaDummy020), (alphaDummy015, alphaDummy017),
        (alphaDummy016, alphaDummy018), (alphaDummy008, alphaDummy010),
        (alphaDummy007, alphaDummy009), (alphaDummy013, alphaDummy014),
        (alphaDummy011, alphaDummy012), (alphaDummy000, x),
        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                            (TAlphaVar.free (by simp) (by simp)))))))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy008) A) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy007) (synCphi (Class.cv alphaDummy008)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy010) A) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy009) (synCphi (Class.cv alphaDummy010))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfReflOn
          [(alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
            (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
            (alphaDummy000, x), (alphaDummy001, alphaDummy002),
            (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
          A wpp_refl_0000)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective ((A).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy008)).fv) (by decide))
                      (freshVar_injective (((Class.cv alphaDummy010)).fv) (by decide))
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
        [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy013, alphaDummy014), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg splitAlpha0000)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy019, alphaDummy020),
                                (alphaDummy015, alphaDummy017),
                                (alphaDummy016, alphaDummy018),
                                (alphaDummy008, alphaDummy010),
                                (alphaDummy007, alphaDummy009),
                                (alphaDummy013, alphaDummy014),
                                (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                                (alphaDummy001, alphaDummy002),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy003, alphaDummy005)]
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
                              [(alphaDummy019, alphaDummy020),
                                (alphaDummy015, alphaDummy017),
                                (alphaDummy016, alphaDummy018),
                                (alphaDummy008, alphaDummy010),
                                (alphaDummy007, alphaDummy009),
                                (alphaDummy013, alphaDummy014),
                                (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                                (alphaDummy001, alphaDummy002),
                                (alphaDummy004, alphaDummy006),
                                (alphaDummy003, alphaDummy005)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0094 : alphaDummy037 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0095 : alphaDummy038 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0096 : alphaDummy039 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0097 : alphaDummy040 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0098 : alphaDummy041 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0099 : alphaDummy042 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy041, alphaDummy042), (alphaDummy039, alphaDummy040),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy037, alphaDummy038), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0098) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0099) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0096) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0097) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there
                                      (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                                      (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                                      (TAlphaVar.free (by simp) (by simp))))))))))))))))))
  have wpp_notmem_0100 : alphaDummy037 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0101 : alphaDummy038 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0102 : alphaDummy039 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0103 : alphaDummy040 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0104 : alphaDummy041 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0105 : alphaDummy042 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy041, alphaDummy042), (alphaDummy039, alphaDummy040),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy037, alphaDummy038), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      ((synC0)).fv :=
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0100) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0101) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there
                                      (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
                                      (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
                                      (TAlphaVar.free (by simp) (by simp))))))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
        (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
        (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy041, alphaDummy042), (alphaDummy039, alphaDummy040),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy037, alphaDummy038), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy022) (Class.cv alphaDummy023))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy021)
            (synCun (Class.cv alphaDummy022) (Class.cv alphaDummy023)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy025) (Class.cv alphaDummy026))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy024)
            (synCun (Class.cv alphaDummy025) (Class.cv alphaDummy026))))) :=
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
                                  (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy023, alphaDummy026), (alphaDummy022, alphaDummy025),
            (alphaDummy021, alphaDummy024), (alphaDummy019, alphaDummy020),
            (alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
            (alphaDummy041, alphaDummy042), (alphaDummy039, alphaDummy040),
            (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
            (alphaDummy037, alphaDummy038), (alphaDummy011, alphaDummy012),
            (alphaDummy000, x), (alphaDummy001, alphaDummy002),
            (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
          (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy015)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy017)).fv ∪ ((synC1c)).fv)
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
  have wpp_notmem_0106 : alphaDummy037 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0107 : alphaDummy038 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0108 : alphaDummy039 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0109 : alphaDummy040 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0110 : alphaDummy041 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0111 : alphaDummy042 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alphaDummy019, alphaDummy020), (alphaDummy015, alphaDummy017),
        (alphaDummy016, alphaDummy018), (alphaDummy041, alphaDummy042),
        (alphaDummy039, alphaDummy040), (alphaDummy008, alphaDummy010),
        (alphaDummy007, alphaDummy009), (alphaDummy037, alphaDummy038),
        (alphaDummy011, alphaDummy012), (alphaDummy000, x),
        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      ((synCnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy015, alphaDummy017), (alphaDummy016, alphaDummy018),
        (alphaDummy041, alphaDummy042), (alphaDummy039, alphaDummy040),
        (alphaDummy008, alphaDummy010), (alphaDummy007, alphaDummy009),
        (alphaDummy037, alphaDummy038), (alphaDummy011, alphaDummy012),
        (alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.neg (synWa (Wff.classMem (Class.cv alphaDummy015) (Class.cv alphaDummy008))
          (Wff.classEq (Class.cv alphaDummy016)
            (synCif (Wff.classMem (Class.cv alphaDummy015) (synCnnc))
              (synCplc (Class.cv alphaDummy015) (synC1c)) (Class.cv alphaDummy015)))))
      (Wff.neg (synWa (Wff.classMem (Class.cv alphaDummy017) (Class.cv alphaDummy010))
          (Wff.classEq (Class.cv alphaDummy018)
            (synCif (Wff.classMem (Class.cv alphaDummy017) (synCnnc))
              (synCplc (Class.cv alphaDummy017) (synC1c)) (Class.cv alphaDummy017))))) :=
    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alphaDummy008)).fv) (by decide))
              (freshVar_injective (((Class.cv alphaDummy010)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed [(alphaDummy023, alphaDummy026),
                                    (alphaDummy022, alphaDummy025),
                                    (alphaDummy021, alphaDummy024),
                                    (alphaDummy019, alphaDummy020),
                                    (alphaDummy015, alphaDummy017),
                                    (alphaDummy016, alphaDummy018),
                                    (alphaDummy041, alphaDummy042),
                                    (alphaDummy039, alphaDummy040),
                                    (alphaDummy008, alphaDummy010),
                                    (alphaDummy007, alphaDummy009),
                                    (alphaDummy037, alphaDummy038),
                                    (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                                    (alphaDummy001, alphaDummy002),
                                    (alphaDummy004, alphaDummy006),
                                    (alphaDummy003, alphaDummy005)]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy019, alphaDummy020), (alphaDummy015, alphaDummy017),
                        (alphaDummy016, alphaDummy018), (alphaDummy041, alphaDummy042),
                        (alphaDummy039, alphaDummy040), (alphaDummy008, alphaDummy010),
                        (alphaDummy007, alphaDummy009), (alphaDummy037, alphaDummy038),
                        (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
                        (alphaDummy003, alphaDummy005)]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy019, alphaDummy020), (alphaDummy015, alphaDummy017),
                        (alphaDummy016, alphaDummy018), (alphaDummy041, alphaDummy042),
                        (alphaDummy039, alphaDummy040), (alphaDummy008, alphaDummy010),
                        (alphaDummy007, alphaDummy009), (alphaDummy037, alphaDummy038),
                        (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
                        (alphaDummy003, alphaDummy005)]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))))))))
  have wpp_notmem_0112 : alphaDummy003 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0113 : alphaDummy005 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0114 : alphaDummy004 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0115 : alphaDummy006 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0116 : alphaDummy001 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0117 : alphaDummy002 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0118 : alphaDummy000 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0119 : x ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0120 : alphaDummy011 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0121 : alphaDummy012 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0122 : alphaDummy037 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0123 : alphaDummy038 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0124 : alphaDummy007 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0125 : alphaDummy009 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0126 : alphaDummy008 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0127 : alphaDummy010 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0128 : alphaDummy039 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0129 : alphaDummy040 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alphaDummy039, alphaDummy040), (alphaDummy008, alphaDummy010),
        (alphaDummy007, alphaDummy009), (alphaDummy037, alphaDummy038),
        (alphaDummy011, alphaDummy012), (alphaDummy000, x),
        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      ((synCcompl (synCsn (synC0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0128) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0129) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0124) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0125) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0122) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0123) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0120) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0121) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0118) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0119) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0112) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0113) (h_eq ▸ hu))
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have splitAlpha0004 :
    TAlphaWff
      [(alphaDummy011, alphaDummy012), (alphaDummy000, x),
        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy011) (synCcompl (Class.cab alphaDummy007
              (synWrex alphaDummy008 A (Wff.classEq (Class.cv alphaDummy007)
                  (synCphi (Class.cv alphaDummy008))))))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy011) (synCcompl (Class.cab alphaDummy007
                (synWrex alphaDummy008 (Class.cv alphaDummy000)
                  (Wff.classEq (Class.cv alphaDummy007)
                    (synCun (synCphi (Class.cv alphaDummy008)) (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy012) (synCcompl (Class.cab alphaDummy009
              (synWrex alphaDummy010 A (Wff.classEq (Class.cv alphaDummy009)
                  (synCphi (Class.cv alphaDummy010))))))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy012) (synCcompl (Class.cab alphaDummy009
                (synWrex alphaDummy010 (Class.cv x) (Wff.classEq (Class.cv alphaDummy009)
                    (synCun (synCphi (Class.cv alphaDummy010))
                      (synCsn (synC0c)))))))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001))))))))
      (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                ((A).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
                              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all splitAlpha0003)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all splitAlpha0003)))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [(alphaDummy039, alphaDummy040),
                                      (alphaDummy008, alphaDummy010),
                                      (alphaDummy007, alphaDummy009),
                                      (alphaDummy037, alphaDummy038),
                                      (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                                      (alphaDummy001, alphaDummy002),
                                      (alphaDummy004, alphaDummy006),
                                      (alphaDummy003, alphaDummy005)]
                                    (synCcompl (synCsn (synC0c))) (by
                                      simp only [fv_syn_ccompl, fv_syn_csn,
                                        fv_syn_c0c])))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                ((A).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
                              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all splitAlpha0003)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all splitAlpha0003)))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [(alphaDummy039, alphaDummy040),
                                      (alphaDummy008, alphaDummy010),
                                      (alphaDummy007, alphaDummy009),
                                      (alphaDummy037, alphaDummy038),
                                      (alphaDummy011, alphaDummy012), (alphaDummy000, x),
                                      (alphaDummy001, alphaDummy002),
                                      (alphaDummy004, alphaDummy006),
                                      (alphaDummy003, alphaDummy005)]
                                    (synCcompl (synCsn (synC0c))) (by
                                      simp only [fv_syn_ccompl, fv_syn_csn,
                                        fv_syn_c0c])))))))))))))))))
  have focused_notmem_0015 : alphaDummy000 ∉ F.fv :=
    by
    change freshVar ((F).fv ∪ (A).fv) 0 ∉ F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0016 : alphaDummy001 ∉ F.fv :=
    by
    change
      freshVar
          (({ alphaDummy000 } : Finset Var) ∪ ((synWbr A F (Class.cv alphaDummy000))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
              (Finset.mem_union_right _ (hu)))))
  have focused_notmem_0017 : alphaDummy003 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy001 (Wff.classEq
                (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                (synCsn (Class.cv alphaDummy001))))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alphaDummy001 (Wff.classEq
                  (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                  (synCsn (Class.cv alphaDummy001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0016) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                      (synCsn (Class.cv alphaDummy001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alphaDummy000
                          (synWbr A F (Class.cv alphaDummy000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0015) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0130 : alphaDummy003 ∉ (F).fv := by exact focused_notmem_0017
  have focused_notmem_0018 : alphaDummy002 ∉ F.fv :=
    by
    change freshVar (({ x } : Finset Var) ∪ ((synWbr A F (Class.cv x))).fv) 0 ∉ F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_right _ (hu)))))
  have focused_notmem_0019 : alphaDummy005 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                (synCsn (Class.cv alphaDummy002))))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alphaDummy002
                (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                  (synCsn (Class.cv alphaDummy002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0018) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (synWbr A F (Class.cv x)))
                      (synCsn (Class.cv alphaDummy002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (synWbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_F_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0131 : alphaDummy005 ∉ (F).fv := by exact focused_notmem_0019
  have focused_notmem_0020 : alphaDummy004 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy001 (Wff.classEq
                (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                (synCsn (Class.cv alphaDummy001))))).fv)
          1 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alphaDummy001 (Wff.classEq
                  (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                  (synCsn (Class.cv alphaDummy001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0016) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                      (synCsn (Class.cv alphaDummy001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alphaDummy000
                          (synWbr A F (Class.cv alphaDummy000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0015) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alphaDummy000)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0132 : alphaDummy004 ∉ (F).fv := by exact focused_notmem_0020
  have focused_notmem_0021 : alphaDummy006 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                (synCsn (Class.cv alphaDummy002))))).fv)
          1 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alphaDummy002
                (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                  (synCsn (Class.cv alphaDummy002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0018) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (synWbr A F (Class.cv x)))
                      (synCsn (Class.cv alphaDummy002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (synWbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_F_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0133 : alphaDummy006 ∉ (F).fv := by exact focused_notmem_0021
  have wpp_notmem_0134 : alphaDummy001 ∉ (F).fv := by exact focused_notmem_0016
  have wpp_notmem_0135 : alphaDummy002 ∉ (F).fv := by exact focused_notmem_0018
  have wpp_notmem_0136 : alphaDummy000 ∉ (F).fv := by exact focused_notmem_0015
  have wpp_notmem_0137 : x ∉ (F).fv := by exact dv_F_x
  have wpp_refl_0008 :
    TReflOn
      [(alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (F).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0136) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0137) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy001 (Wff.classEq
                        (Class.cab alphaDummy000 (synWbr A F (Class.cv alphaDummy000)))
                        (synCsn (Class.cv alphaDummy001))))).fv) (by decide))
                (freshVar_injective (((Class.cab alphaDummy002
                      (Wff.classEq (Class.cab x (synWbr A F (Class.cv x)))
                        (synCsn (Class.cv alphaDummy002))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg splitAlpha0004)))
                      (TAlphaClass.reflOfReflOn
                        [(alphaDummy000, x), (alphaDummy001, alphaDummy002),
                          (alphaDummy004, alphaDummy006),
                          (alphaDummy003, alphaDummy005)] F wpp_refl_0008)))
                  (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                          (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
