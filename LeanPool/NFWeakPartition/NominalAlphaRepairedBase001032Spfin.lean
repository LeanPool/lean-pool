/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001032Spfin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_spfin`. -/
@[expose]
noncomputable def nominalDfSpfin (x : Var) (z : Var) (a : Var) (dv_a_x : a ≠ x)
    (dv_a_z : a ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.classEq (synCspfin) (synCint (.cab a
            (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
                (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synCncfin (synCvv)) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000) (Wff.all alphaDummy002
                (Wff.imp (synWsfin (Class.cv alphaDummy002) (Class.cv alphaDummy001))
                  (Wff.objMem alphaDummy002 alphaDummy000))))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synCncfin (synCvv)) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000) (Wff.all alphaDummy002
                (Wff.imp (synWsfin (Class.cv alphaDummy002) (Class.cv alphaDummy001))
                  (Wff.objMem alphaDummy002 alphaDummy000))))))).fv) 1)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cab a (synWa (Wff.classMem (synCncfin (synCvv)) (Class.cv a))
            (synWral x (Class.cv a) (Wff.all z
                (Wff.imp (synWsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a))))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((Class.cab a (synWa (Wff.classMem (synCncfin (synCvv)) (Class.cv a))
            (synWral x (Class.cv a) (Wff.all z
                (Wff.imp (synWsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a))))))).fv) 1)
  let alphaDummy007 : Var := (freshVar (((synCvv)).fv) 0)
  let alphaDummy008 : Var :=
    (freshVar (({ alphaDummy007 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
            (Wff.classMem (synCvv) (Class.cv alphaDummy007)))).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cab alphaDummy008 (Wff.classEq (Class.cab alphaDummy007
              (synWa (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
                (Wff.classMem (synCvv) (Class.cv alphaDummy007))))
            (synCsn (Class.cv alphaDummy008))))).fv) 0)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cab alphaDummy008 (Wff.classEq (Class.cab alphaDummy007
              (synWa (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
                (Wff.classMem (synCvv) (Class.cv alphaDummy007))))
            (synCsn (Class.cv alphaDummy008))))).fv) 1)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 1)
  let alphaDummy013 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy015 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy016 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy020 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)
  let alphaDummy026 : Var := (freshVar (((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy028 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv x)).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((synCpw (Class.cv alphaDummy027))).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((synCpw (Class.cv alphaDummy028))).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy033 : Var := (freshVar (((Class.cv alphaDummy027)).fv) 0)
  let alphaDummy034 : Var := (freshVar (((Class.cv alphaDummy028)).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv ∪
        ((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv ∪
        ((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((Class.cv alphaDummy033)).fv ∪ ((Class.cv alphaDummy027)).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((Class.cv alphaDummy034)).fv ∪ ((Class.cv alphaDummy028)).fv) 0)
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
    alphaDummy018 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0002 :
    alphaDummy018 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv)
        support_part_0002)
  have support_part_0003 : alphaDummy018 ∈ (((Class.cv alphaDummy018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy019)).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv ∪
        ((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy018) (Class.cv alphaDummy019))).fv)
        support_part_0004)
  have support_part_0005 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy018)).fv) support_part_0005)
  have support_part_0006 :
    alphaDummy018 ∈ (((synCcompl (Class.cv alphaDummy018))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0006 :
    alphaDummy018 ∈
      (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy019))).fv) support_part_0006)
  have support_part_0007 : alphaDummy018 ∈ (((Class.cv alphaDummy018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alphaDummy018 ∈
      (((Class.cv alphaDummy018)).fv ∪ ((Class.cv alphaDummy018)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy018)).fv) support_part_0007)
  have support_part_0008 :
    alphaDummy019 ∈ (((synCcompl (Class.cv alphaDummy019))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alphaDummy019 ∈
      (((synCcompl (Class.cv alphaDummy018))).fv ∪
        ((synCcompl (Class.cv alphaDummy019))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy018))).fv) support_part_0008)
  have support_part_0009 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy019)).fv) support_part_0009)
  have support_part_0010 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    exact support_part_0010
  have support_part_0011 :
    alphaDummy033 ∈
      (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0011 :
    alphaDummy033 ∈
      (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv ∪
        ((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv)
        support_part_0011)
  have support_part_0012 :
    alphaDummy034 ∈
      (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0012 :
    alphaDummy034 ∈
      (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv ∪
        ((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv)
        support_part_0012)
  have support_part_0013 : alphaDummy033 ∈ (((Class.cv alphaDummy033)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0013 :
    alphaDummy033 ∈
      (((Class.cv alphaDummy033)).fv ∪ ((Class.cv alphaDummy027)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy027)).fv) support_part_0013)
  have support_part_0014 : alphaDummy034 ∈ (((Class.cv alphaDummy034)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alphaDummy034 ∈
      (((Class.cv alphaDummy034)).fv ∪ ((Class.cv alphaDummy028)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy028)).fv) support_part_0014)
  have support_part_0015 :
    alphaDummy027 ∈ (((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0015 :
    alphaDummy027 ∈
      (((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))).fv)
        support_part_0015)
  have support_part_0016 :
    alphaDummy028 ∈ (((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0016 :
    alphaDummy028 ∈
      (((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))).fv)
        support_part_0016)
  have support_part_0017 :
    alphaDummy027 ∈ (((synCpw (Class.cv alphaDummy027))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0017 :
    alphaDummy027 ∈ (((synCpw (Class.cv alphaDummy027))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0017)
  have support_part_0018 :
    alphaDummy028 ∈ (((synCpw (Class.cv alphaDummy028))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0018 :
    alphaDummy028 ∈ (((synCpw (Class.cv alphaDummy028))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0018)
  have support_part_0019 : alphaDummy027 ∈ (((Class.cv alphaDummy027)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 : alphaDummy027 ∈ (((Class.cv alphaDummy027)).fv) := by
    exact support_part_0019
  have support_part_0020 : alphaDummy028 ∈ (((Class.cv alphaDummy028)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0020 : alphaDummy028 ∈ (((Class.cv alphaDummy028)).fv) := by
    exact support_part_0020
  have support_part_0021 :
    alphaDummy027 ∈
      (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0021 :
    alphaDummy027 ∈
      (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv ∪
        ((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy033) (Class.cv alphaDummy027))).fv)
        support_part_0021)
  have support_part_0022 :
    alphaDummy028 ∈
      (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0022 :
    alphaDummy028 ∈
      (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv ∪
        ((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy034) (Class.cv alphaDummy028))).fv)
        support_part_0022)
  have support_part_0023 : alphaDummy027 ∈ (((Class.cv alphaDummy027)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 :
    alphaDummy027 ∈
      (((Class.cv alphaDummy033)).fv ∪ ((Class.cv alphaDummy027)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy033)).fv) support_part_0023)
  have support_part_0024 : alphaDummy028 ∈ (((Class.cv alphaDummy028)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0024 :
    alphaDummy028 ∈
      (((Class.cv alphaDummy034)).fv ∪ ((Class.cv alphaDummy028)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy034)).fv) support_part_0024)
  have support_part_0025 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0025 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy001)).fv) support_part_0025)
  have support_part_0026 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv x)).fv) := by
    exact (Finset.mem_union_left (((Class.cv x)).fv) support_part_0026)
  have support_part_0027 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy002)).fv) support_part_0027)
  have support_part_0028 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 : x ∈ (((Class.cv z)).fv ∪ ((Class.cv x)).fv) := by
    exact (Finset.mem_union_right (((Class.cv z)).fv) support_part_0028)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy019, alphaDummy019), (alphaDummy018, alphaDummy018),
        (alphaDummy017, alphaDummy017), (alphaDummy001, alphaDummy001),
        (alphaDummy000, alphaDummy000), (alphaDummy012, alphaDummy012),
        (alphaDummy011, alphaDummy011), (alphaDummy007, alphaDummy007),
        (alphaDummy008, alphaDummy008), (alphaDummy010, alphaDummy010),
        (alphaDummy009, alphaDummy009), (alphaDummy000, a),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy018) (Class.cv alphaDummy019))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy017)
            (synCun (Class.cv alphaDummy018) (Class.cv alphaDummy019)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy018) (Class.cv alphaDummy019))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy017)
            (synCun (Class.cv alphaDummy018) (Class.cv alphaDummy019))))) :=
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
      [(alphaDummy007, alphaDummy007), (alphaDummy008, alphaDummy008),
        (alphaDummy010, alphaDummy010), (alphaDummy009, alphaDummy009),
        (alphaDummy000, a), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
        (Wff.neg (Wff.classMem (synCvv) (Class.cv alphaDummy007))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
        (Wff.neg (Wff.classMem (synCvv) (Class.cv alphaDummy007)))) :=
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
        (TAlphaWff.classMem (TAlphaClass.cab
            (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))
          (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy019, alphaDummy019), (alphaDummy018, alphaDummy018),
        (alphaDummy017, alphaDummy017), (alphaDummy001, alphaDummy001),
        (alphaDummy000, alphaDummy000), (alphaDummy012, alphaDummy012),
        (alphaDummy011, alphaDummy011), (alphaDummy002, z), (alphaDummy001, x),
        (alphaDummy000, a), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy018) (Class.cv alphaDummy019))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy017)
            (synCun (Class.cv alphaDummy018) (Class.cv alphaDummy019)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy018) (Class.cv alphaDummy019))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy017)
            (synCun (Class.cv alphaDummy018) (Class.cv alphaDummy019))))) :=
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
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy002, z), (alphaDummy001, x), (alphaDummy000, a),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.classMem (Class.cv alphaDummy001) (synCnnc))
      (Wff.classMem (Class.cv x) (synCnnc)) :=
    (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg splitAlpha0002)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy000
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                        (synWral alphaDummy001 (Class.cv alphaDummy000)
                          (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                            (Class.cv alphaDummy000)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alphaDummy000
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                        (synWral alphaDummy001 (Class.cv alphaDummy000)
                          (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                            (Class.cv alphaDummy000)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  have splitAlpha0004 :
    TAlphaWff
      [(alphaDummy002, z), (alphaDummy001, x), (alphaDummy000, a),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv alphaDummy002) (synCnnc))
          (Wff.neg (Wff.classMem (Class.cv alphaDummy001) (synCnnc)))))
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv z) (synCnnc))
          (Wff.neg (Wff.classMem (Class.cv x) (synCnnc))))) :=
    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
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
                                    (TAlphaWff.neg splitAlpha0002)))))) (TAlphaClass.cv
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
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) splitAlpha0003)
  have splitAlpha0005 :
    TAlphaWff
      [(alphaDummy029, alphaDummy030), (alphaDummy027, alphaDummy028),
        (alphaDummy002, z), (alphaDummy001, x), (alphaDummy000, a),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy029)
          (synCnin (synCpw (Class.cv alphaDummy027)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy029)
            (synCnin (synCpw (Class.cv alphaDummy027)) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy030)
          (synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy030)
            (synCnin (synCpw (Class.cv alphaDummy028)) (synC1c))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _)))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _)))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0006 :
    TAlphaWff
      [(alphaDummy000, a), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (synCncfin (synCvv)) (Class.cv alphaDummy000)) (Wff.neg
          (synWral alphaDummy001 (Class.cv alphaDummy000) (Wff.all alphaDummy002
              (Wff.imp (synWsfin (Class.cv alphaDummy002) (Class.cv alphaDummy001))
                (Wff.objMem alphaDummy002 alphaDummy000))))))
      (Wff.imp (Wff.classMem (synCncfin (synCvv)) (Class.cv a)) (Wff.neg
          (synWral x (Class.cv a) (Wff.all z
              (Wff.imp (synWsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                    (((Class.cab alphaDummy008 (Wff.classEq (Class.cab alphaDummy007
                            (synWa (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
                              (Wff.classMem (synCvv) (Class.cv alphaDummy007))))
                          (synCsn (Class.cv alphaDummy008))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alphaDummy008 (Wff.classEq
                          (Class.cab alphaDummy007
                            (synWa (Wff.classMem (Class.cv alphaDummy007) (synCnnc))
                              (Wff.classMem (synCvv) (Class.cv alphaDummy007))))
                          (synCsn (Class.cv alphaDummy008))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg splitAlpha0001))
                    (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                            (TAlphaVar.here _ _ _)))))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                (TAlphaWff.conj splitAlpha0004 (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg splitAlpha0005)))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020
        0)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020
        0)) (TAlphaVar.here _ _ _))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                              (TAlphaVar.here _ _ _))))))))
                (TAlphaWff.objMem (TAlphaVar.here _ _ _)
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_z
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      dv_a_x (TAlphaVar.here _ _ _))))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg splitAlpha0006))) (TAlphaWff.objMem
              (TAlphaVar.there (freshVar_injective (((Class.cab alphaDummy000 (synWa
                        (Wff.classMem (synCncfin (synCvv)) (Class.cv alphaDummy000))
                        (synWral alphaDummy001 (Class.cv alphaDummy000)
                          (Wff.all alphaDummy002 (Wff.imp
                              (synWsfin (Class.cv alphaDummy002) (Class.cv alphaDummy001))
                              (Wff.objMem alphaDummy002 alphaDummy000))))))).fv)
                  (by decide)) (freshVar_injective (((Class.cab a
                      (synWa (Wff.classMem (synCncfin (synCvv)) (Class.cv a))
                        (synWral x (Class.cv a) (Wff.all z
                            (Wff.imp (synWsfin (Class.cv z) (Class.cv x))
                              (Wff.objMem z a))))))).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
