/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001029Evenfin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_evenfin`. -/
@[expose]
noncomputable def nominalDfEvenfin (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf
      (.classEq (synCevenfin) (.cab x
          (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
            (synWne (.cv x) (synC0))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy002 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 1)
  let alphaDummy004 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy006 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy007 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy008 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy011 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv ∪
        ((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy009))).fv ∪
        ((synCcompl (Class.cv alphaDummy010))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv) 2)
  let alphaDummy020 : Var := (freshVar (((Class.cv n)).fv ∪ ((Class.cv n)).fv) 0)
  let alphaDummy021 : Var := (freshVar (((Class.cv n)).fv ∪ ((Class.cv n)).fv) 1)
  let alphaDummy022 : Var := (freshVar (((Class.cv n)).fv ∪ ((Class.cv n)).fv) 2)
  let alphaDummy023 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv ∪
        ((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy022)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy021))).fv ∪
        ((synCcompl (Class.cv alphaDummy022))).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) 0)
  have support_part_0000 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0000)
  have support_part_0001 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0001
  have support_part_0002 :
    alphaDummy009 ∈
      (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0002 :
    alphaDummy009 ∈
      (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv ∪
        ((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv)
        support_part_0002)
  have support_part_0003 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy010)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy010)).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy010 ∈
      (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alphaDummy010 ∈
      (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv ∪
        ((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv)
        support_part_0004)
  have support_part_0005 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alphaDummy010 ∈
      (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy010)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy009)).fv) support_part_0005)
  have support_part_0006 :
    alphaDummy009 ∈ (((synCcompl (Class.cv alphaDummy009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0006 :
    alphaDummy009 ∈
      (((synCcompl (Class.cv alphaDummy009))).fv ∪
        ((synCcompl (Class.cv alphaDummy010))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy010))).fv) support_part_0006)
  have support_part_0007 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy009)).fv) support_part_0007)
  have support_part_0008 :
    alphaDummy010 ∈ (((synCcompl (Class.cv alphaDummy010))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alphaDummy010 ∈
      (((synCcompl (Class.cv alphaDummy009))).fv ∪
        ((synCcompl (Class.cv alphaDummy010))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy009))).fv) support_part_0008)
  have support_part_0009 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alphaDummy010 ∈
      (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy010)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy010)).fv) support_part_0009)
  have support_part_0010 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy000)).fv) support_part_0010)
  have support_part_0011 : n ∈ (((Class.cv n)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 : n ∈ (((Class.cv n)).fv ∪ ((Class.cv n)).fv) := by
    exact (Finset.mem_union_left (((Class.cv n)).fv) support_part_0011)
  have support_part_0012 :
    alphaDummy018 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0012 :
    alphaDummy018 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv)
        support_part_0012)
  have support_part_0013 :
    alphaDummy021 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0013 :
    alphaDummy021 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv ∪
        ((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv)
        support_part_0013)
  have support_part_0014 : alphaDummy018 ∈ (((Class.cv alphaDummy018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy019)).fv) support_part_0014)
  have support_part_0015 : alphaDummy021 ∈ (((Class.cv alphaDummy021)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0015 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy022)).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0016 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv)
        support_part_0016)
  have support_part_0017 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0017 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv ∪
        ((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv)
        support_part_0017)
  have support_part_0018 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0018 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy018)).fv) support_part_0018)
  have support_part_0019 : alphaDummy022 ∈ (((Class.cv alphaDummy022)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy021)).fv) support_part_0019)
  have support_part_0020 :
    alphaDummy018 ∈ (((synCcompl (Class.cv alphaDummy018))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0020 :
    alphaDummy018 ∈
      (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy019))).fv) support_part_0020)
  have support_part_0021 :
    alphaDummy021 ∈ (((synCcompl (Class.cv alphaDummy021))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0021 :
    alphaDummy021 ∈
      (((synCcompl (Class.cv alphaDummy021))).fv ∪
        ((synCcompl (Class.cv alphaDummy022))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy022))).fv) support_part_0021)
  have support_part_0022 : alphaDummy018 ∈ (((Class.cv alphaDummy018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0022 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy018)).fv) support_part_0022)
  have support_part_0023 : alphaDummy021 ∈ (((Class.cv alphaDummy021)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy021)).fv) support_part_0023)
  have support_part_0024 :
    alphaDummy019 ∈ (((synCcompl (Class.cv alphaDummy019))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0024 :
    alphaDummy019 ∈
      (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy018))).fv) support_part_0024)
  have support_part_0025 :
    alphaDummy022 ∈ (((synCcompl (Class.cv alphaDummy022))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0025 :
    alphaDummy022 ∈
      (((synCcompl (Class.cv alphaDummy021))).fv ∪
        ((synCcompl (Class.cv alphaDummy022))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy021))).fv) support_part_0025)
  have support_part_0026 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy019)).fv) support_part_0026)
  have support_part_0027 : alphaDummy022 ∈ (((Class.cv alphaDummy022)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy022)).fv) support_part_0027)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy010, alphaDummy010), (alphaDummy009, alphaDummy009),
        (alphaDummy008, alphaDummy008), (alphaDummy001, alphaDummy001),
        (alphaDummy000, alphaDummy000), (alphaDummy003, alphaDummy003),
        (alphaDummy002, alphaDummy002), (alphaDummy000, n), (alphaDummy001, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy009) (Class.cv alphaDummy010))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy008)
            (synCun (Class.cv alphaDummy009) (Class.cv alphaDummy010)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy009) (Class.cv alphaDummy010))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy008)
            (synCun (Class.cv alphaDummy009) (Class.cv alphaDummy010))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy019, alphaDummy022), (alphaDummy018, alphaDummy021),
        (alphaDummy017, alphaDummy020), (alphaDummy000, n), (alphaDummy001, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy018) (Class.cv alphaDummy019))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy017)
            (synCun (Class.cv alphaDummy018) (Class.cv alphaDummy019)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy021) (Class.cv alphaDummy022))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy020)
            (synCun (Class.cv alphaDummy021) (Class.cv alphaDummy022))))) :=
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
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy000)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
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
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy000)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
              (freshVar_injective (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
              (TAlphaVar.there (freshVar_injective
                  (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy000)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv n)).fv ∪ ((Class.cv n)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))))))
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
  have splitAlpha0002 :
    TAlphaWff [(alphaDummy000, n), (alphaDummy001, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy000) (synCnnc)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy001)
            (synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy000)))))
      (Wff.imp (Wff.classMem (Class.cv n) (synCnnc))
        (Wff.neg (Wff.classEq (Class.cv x) (synCplc (Class.cv n) (Class.cv n))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.all (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.all (TAlphaWff.imp
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg splitAlpha0000)))))) (TAlphaClass.cv
                            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                  (freshVar_injective (((Class.cab alphaDummy000
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                          (synWral alphaDummy001 (Class.cv alphaDummy000)
                            (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                              (Class.cv alphaDummy000)))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alphaDummy000
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                          (synWral alphaDummy001 (Class.cv alphaDummy000)
                            (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                              (Class.cv alphaDummy000)))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
              (Ne.symm dv_n_x) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 2))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 2)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.neg splitAlpha0001)))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.conj (TAlphaWff.ex (TAlphaWff.neg splitAlpha0002))
          (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                  (TAlphaVar.here _ _ _))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
        (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                  (TAlphaVar.here _ _ _))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
        (TAlphaVar.here _ _ _)))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
