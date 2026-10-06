/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001026Ltfin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_ltfin`. -/
@[expose]
noncomputable def nominalDfLtfin (x : Var) (m : Var) (n : Var) (p : Var)
    (dv_m_n : m ≠ n) (dv_m_p : m ≠ p) (dv_m_x : m ≠ x) (dv_n_p : n ≠ p) (dv_n_x : n ≠ x)
    (__dv_p_x : p ≠ x) :
    Nominal.NPrf
      (.classEq (synCltfin) (.cab x (synWex m (synWex n
              (synWa (.classEq (.cv x) (synCopk (.cv m) (.cv n)))
                (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc) (.classEq (.cv n)
                      (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alphaDummy003 : Var := (freshVar ((∅ : Finset Var)) 3)
  let alphaDummy004 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv m))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv m) (Class.cv n))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv m)))).fv ∪ ((synCsn (synCsn (Class.cv m)))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy009 : Var := (freshVar (((synCsn (Class.cv m))).fv) 0)
  let alphaDummy010 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy011 : Var := (freshVar (((Class.cv m)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv ∪
        ((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy015 : Var := (freshVar (((synCpr (Class.cv m) (Class.cv n))).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv m)))).fv ∪
        ((synCcompl (synCsn (Class.cv n)))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy000))).fv ∪
        ((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCsn (Class.cv m))).fv ∪ ((synCsn (Class.cv m))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy001))).fv ∪
        ((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCsn (Class.cv n))).fv ∪ ((synCsn (Class.cv n))).fv) 0)
  let alphaDummy022 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy023 : Var := (freshVar (((Class.cv n)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy025 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy026 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 1)
  let alphaDummy029 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy032 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy033 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((Class.cv alphaDummy032)).fv ∪ ((Class.cv alphaDummy032)).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
        ((synC1c)).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
        ((synC1c)).fv) 1)
  let alphaDummy040 : Var :=
    (freshVar (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
        ((synC1c)).fv) 2)
  let alphaDummy041 : Var :=
    (freshVar (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy042 : Var :=
    (freshVar (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy043 : Var :=
    (freshVar (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy044 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy045 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) 1)
  let alphaDummy046 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) 2)
  let alphaDummy047 : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv p)).fv) 0)
  let alphaDummy048 : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv p)).fv) 1)
  let alphaDummy049 : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv p)).fv) 2)
  let alphaDummy050 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv ∪
        ((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv) 0)
  let alphaDummy051 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv ∪
        ((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv) 0)
  let alphaDummy052 : Var :=
    (freshVar (((Class.cv alphaDummy045)).fv ∪ ((Class.cv alphaDummy046)).fv) 0)
  let alphaDummy053 : Var :=
    (freshVar (((Class.cv alphaDummy048)).fv ∪ ((Class.cv alphaDummy049)).fv) 0)
  let alphaDummy054 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy045))).fv ∪
        ((synCcompl (Class.cv alphaDummy046))).fv) 0)
  let alphaDummy055 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy048))).fv ∪
        ((synCcompl (Class.cv alphaDummy049))).fv) 0)
  let alphaDummy056 : Var :=
    (freshVar (((Class.cv alphaDummy045)).fv ∪ ((Class.cv alphaDummy045)).fv) 0)
  let alphaDummy057 : Var :=
    (freshVar (((Class.cv alphaDummy048)).fv ∪ ((Class.cv alphaDummy048)).fv) 0)
  let alphaDummy058 : Var :=
    (freshVar (((Class.cv alphaDummy046)).fv ∪ ((Class.cv alphaDummy046)).fv) 0)
  let alphaDummy059 : Var :=
    (freshVar (((Class.cv alphaDummy049)).fv ∪ ((Class.cv alphaDummy049)).fv) 0)
  let alphaDummy060 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv ∪
        ((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv) 0)
  let alphaDummy061 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv ∪
        ((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv) 0)
  let alphaDummy062 : Var :=
    (freshVar (((Class.cv alphaDummy039)).fv ∪ ((Class.cv alphaDummy040)).fv) 0)
  let alphaDummy063 : Var :=
    (freshVar (((Class.cv alphaDummy042)).fv ∪ ((Class.cv alphaDummy043)).fv) 0)
  let alphaDummy064 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy039))).fv ∪
        ((synCcompl (Class.cv alphaDummy040))).fv) 0)
  let alphaDummy065 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy042))).fv ∪
        ((synCcompl (Class.cv alphaDummy043))).fv) 0)
  let alpha_dummy_066 : Var :=
    (freshVar (((Class.cv alphaDummy039)).fv ∪ ((Class.cv alphaDummy039)).fv) 0)
  let alpha_dummy_067 : Var :=
    (freshVar (((Class.cv alphaDummy042)).fv ∪ ((Class.cv alphaDummy042)).fv) 0)
  let alpha_dummy_068 : Var :=
    (freshVar (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy040)).fv) 0)
  let alpha_dummy_069 : Var :=
    (freshVar (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy043)).fv) 0)
  have support_part_0000 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv)
        support_part_0000)
  have support_part_0001 : m ∈ (((synCcompl (synCsn (synCsn (Class.cv m))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    m ∈
      (((synCcompl (synCsn (synCsn (Class.cv m))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv m) (Class.cv n))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (synCpr (Class.cv m) (Class.cv n))))).fv)
        support_part_0001)
  have support_part_0002 :
    alphaDummy000 ∈ (((synCsn (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy000 ∈
      (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0002)
  have support_part_0003 : m ∈ (((synCsn (synCsn (Class.cv m)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    m ∈ (((synCsn (synCsn (Class.cv m)))).fv ∪ ((synCsn (synCsn (Class.cv m)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv m)))).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) :=
    by exact support_part_0004
  have support_part_0005 : m ∈ (((synCsn (Class.cv m))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : m ∈ (((synCsn (Class.cv m))).fv) := by exact support_part_0005
  have support_part_0006 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0006
  have support_part_0007 : m ∈ (((Class.cv m)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : m ∈ (((Class.cv m)).fv) := by exact support_part_0007
  have support_part_0008 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0008)
  have support_part_0009 : m ∈ (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    m ∈
      (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv ∪
        ((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv)
        support_part_0009)
  have support_part_0010 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0010
  have support_part_0011 : m ∈ (((synCpr (Class.cv m) (Class.cv n))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : m ∈ (((synCpr (Class.cv m) (Class.cv n))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alphaDummy000 ∈ (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0012)
  have support_part_0013 : m ∈ (((synCcompl (synCsn (Class.cv m)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    m ∈
      (((synCcompl (synCsn (Class.cv m)))).fv ∪ ((synCcompl (synCsn (Class.cv n)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv n)))).fv) support_part_0013)
  have support_part_0014 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy000 ∈
      (((synCsn (Class.cv alphaDummy000))).fv ∪ ((synCsn (Class.cv alphaDummy000))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy000))).fv) support_part_0014)
  have support_part_0015 : m ∈ (((synCsn (Class.cv m))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    m ∈ (((synCsn (Class.cv m))).fv ∪ ((synCsn (Class.cv m))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv m))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy001 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv)
        support_part_0016)
  have support_part_0017 :
    n ∈ (((synCcompl (synCsn (synCpr (Class.cv m) (Class.cv n))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    n ∈
      (((synCcompl (synCsn (synCsn (Class.cv m))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv m) (Class.cv n))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv m))))).fv)
        support_part_0017)
  have support_part_0018 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0018)
  have support_part_0019 : n ∈ (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    n ∈
      (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv ∪
        ((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv m) (Class.cv n)))).fv)
        support_part_0019)
  have support_part_0020 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0020
  have support_part_0021 : n ∈ (((synCpr (Class.cv m) (Class.cv n))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : n ∈ (((synCpr (Class.cv m) (Class.cv n))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alphaDummy001 ∈ (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0022)
  have support_part_0023 : n ∈ (((synCcompl (synCsn (Class.cv n)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    n ∈
      (((synCcompl (synCsn (Class.cv m)))).fv ∪ ((synCcompl (synCsn (Class.cv n)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv m)))).fv) support_part_0023)
  have support_part_0024 :
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy001 ∈
      (((synCsn (Class.cv alphaDummy001))).fv ∪ ((synCsn (Class.cv alphaDummy001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy001))).fv) support_part_0024)
  have support_part_0025 : n ∈ (((synCsn (Class.cv n))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    n ∈ (((synCsn (Class.cv n))).fv ∪ ((synCsn (Class.cv n))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv n))).fv) support_part_0025)
  have support_part_0026 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0026
  have support_part_0027 : n ∈ (((Class.cv n)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : n ∈ (((Class.cv n)).fv) := by exact support_part_0027
  have support_part_0028 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 :
    alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0028)
  have support_part_0029 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0029 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv)
        support_part_0029)
  have support_part_0030 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0030 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy032)).fv) support_part_0030)
  have support_part_0031 :
    alphaDummy032 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0031 :
    alphaDummy032 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv)
        support_part_0031)
  have support_part_0032 : alphaDummy032 ∈ (((Class.cv alphaDummy032)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0032 :
    alphaDummy032 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy031)).fv) support_part_0032)
  have support_part_0033 :
    alphaDummy031 ∈ (((synCcompl (Class.cv alphaDummy031))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0033 :
    alphaDummy031 ∈
      (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy032))).fv) support_part_0033)
  have support_part_0034 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0034 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy031)).fv) support_part_0034)
  have support_part_0035 :
    alphaDummy032 ∈ (((synCcompl (Class.cv alphaDummy032))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0035 :
    alphaDummy032 ∈
      (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy031))).fv) support_part_0035)
  have support_part_0036 : alphaDummy032 ∈ (((Class.cv alphaDummy032)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0036 :
    alphaDummy032 ∈
      (((Class.cv alphaDummy032)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy032)).fv) support_part_0036)
  have support_part_0037 :
    alphaDummy000 ∈
      (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cplc, eq_self,
      true_or]
  have support_mem_0037 :
    alphaDummy000 ∈
      (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
        ((synC1c)).fv) :=
    by exact (Finset.mem_union_left (((synC1c)).fv) support_part_0037)
  have support_part_0038 : m ∈ (((synCplc (Class.cv m) (Class.cv p))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cplc, eq_self,
      true_or]
  have support_mem_0038 :
    m ∈ (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0038)
  have support_part_0039 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0039 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy002)).fv) support_part_0039)
  have support_part_0040 : m ∈ (((Class.cv m)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0040 : m ∈ (((Class.cv m)).fv ∪ ((Class.cv p)).fv) := by
    exact (Finset.mem_union_left (((Class.cv p)).fv) support_part_0040)
  have support_part_0041 :
    alphaDummy002 ∈
      (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cplc, eq_self,
      or_true]
  have support_mem_0041 :
    alphaDummy002 ∈
      (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
        ((synC1c)).fv) :=
    by exact (Finset.mem_union_left (((synC1c)).fv) support_part_0041)
  have support_part_0042 : p ∈ (((synCplc (Class.cv m) (Class.cv p))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cplc, eq_self,
      or_true]
  have support_mem_0042 :
    p ∈ (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0042)
  have support_part_0043 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0043 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy000)).fv) support_part_0043)
  have support_part_0044 : p ∈ (((Class.cv p)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0044 : p ∈ (((Class.cv m)).fv ∪ ((Class.cv p)).fv) := by
    exact (Finset.mem_union_right (((Class.cv m)).fv) support_part_0044)
  have support_part_0045 :
    alphaDummy045 ∈
      (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0045 :
    alphaDummy045 ∈
      (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv ∪
        ((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv)
        support_part_0045)
  have support_part_0046 :
    alphaDummy048 ∈
      (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0046 :
    alphaDummy048 ∈
      (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv ∪
        ((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv)
        support_part_0046)
  have support_part_0047 : alphaDummy045 ∈ (((Class.cv alphaDummy045)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0047 :
    alphaDummy045 ∈
      (((Class.cv alphaDummy045)).fv ∪ ((Class.cv alphaDummy046)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy046)).fv) support_part_0047)
  have support_part_0048 : alphaDummy048 ∈ (((Class.cv alphaDummy048)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0048 :
    alphaDummy048 ∈
      (((Class.cv alphaDummy048)).fv ∪ ((Class.cv alphaDummy049)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy049)).fv) support_part_0048)
  have support_part_0049 :
    alphaDummy046 ∈
      (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0049 :
    alphaDummy046 ∈
      (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv ∪
        ((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy045) (Class.cv alphaDummy046))).fv)
        support_part_0049)
  have support_part_0050 :
    alphaDummy049 ∈
      (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0050 :
    alphaDummy049 ∈
      (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv ∪
        ((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy048) (Class.cv alphaDummy049))).fv)
        support_part_0050)
  have support_part_0051 : alphaDummy046 ∈ (((Class.cv alphaDummy046)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0051 :
    alphaDummy046 ∈
      (((Class.cv alphaDummy045)).fv ∪ ((Class.cv alphaDummy046)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy045)).fv) support_part_0051)
  have support_part_0052 : alphaDummy049 ∈ (((Class.cv alphaDummy049)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0052 :
    alphaDummy049 ∈
      (((Class.cv alphaDummy048)).fv ∪ ((Class.cv alphaDummy049)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy048)).fv) support_part_0052)
  have support_part_0053 :
    alphaDummy045 ∈ (((synCcompl (Class.cv alphaDummy045))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0053 :
    alphaDummy045 ∈
      (((synCcompl (Class.cv alphaDummy045))).fv ∪
        ((synCcompl (Class.cv alphaDummy046))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy046))).fv) support_part_0053)
  have support_part_0054 :
    alphaDummy048 ∈ (((synCcompl (Class.cv alphaDummy048))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0054 :
    alphaDummy048 ∈
      (((synCcompl (Class.cv alphaDummy048))).fv ∪
        ((synCcompl (Class.cv alphaDummy049))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy049))).fv) support_part_0054)
  have support_part_0055 : alphaDummy045 ∈ (((Class.cv alphaDummy045)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0055 :
    alphaDummy045 ∈
      (((Class.cv alphaDummy045)).fv ∪ ((Class.cv alphaDummy045)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy045)).fv) support_part_0055)
  have support_part_0056 : alphaDummy048 ∈ (((Class.cv alphaDummy048)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0056 :
    alphaDummy048 ∈
      (((Class.cv alphaDummy048)).fv ∪ ((Class.cv alphaDummy048)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy048)).fv) support_part_0056)
  have support_part_0057 :
    alphaDummy046 ∈ (((synCcompl (Class.cv alphaDummy046))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0057 :
    alphaDummy046 ∈
      (((synCcompl (Class.cv alphaDummy045))).fv ∪
        ((synCcompl (Class.cv alphaDummy046))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy045))).fv) support_part_0057)
  have support_part_0058 :
    alphaDummy049 ∈ (((synCcompl (Class.cv alphaDummy049))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0058 :
    alphaDummy049 ∈
      (((synCcompl (Class.cv alphaDummy048))).fv ∪
        ((synCcompl (Class.cv alphaDummy049))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy048))).fv) support_part_0058)
  have support_part_0059 : alphaDummy046 ∈ (((Class.cv alphaDummy046)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0059 :
    alphaDummy046 ∈
      (((Class.cv alphaDummy046)).fv ∪ ((Class.cv alphaDummy046)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy046)).fv) support_part_0059)
  have support_part_0060 : alphaDummy049 ∈ (((Class.cv alphaDummy049)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0060 :
    alphaDummy049 ∈
      (((Class.cv alphaDummy049)).fv ∪ ((Class.cv alphaDummy049)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy049)).fv) support_part_0060)
  have support_part_0061 :
    alphaDummy039 ∈
      (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0061 :
    alphaDummy039 ∈
      (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv ∪
        ((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv)
        support_part_0061)
  have support_part_0062 :
    alphaDummy042 ∈
      (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0062 :
    alphaDummy042 ∈
      (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv ∪
        ((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv)
        support_part_0062)
  have support_part_0063 : alphaDummy039 ∈ (((Class.cv alphaDummy039)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0063 :
    alphaDummy039 ∈
      (((Class.cv alphaDummy039)).fv ∪ ((Class.cv alphaDummy040)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy040)).fv) support_part_0063)
  have support_part_0064 : alphaDummy042 ∈ (((Class.cv alphaDummy042)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0064 :
    alphaDummy042 ∈
      (((Class.cv alphaDummy042)).fv ∪ ((Class.cv alphaDummy043)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy043)).fv) support_part_0064)
  have support_part_0065 :
    alphaDummy040 ∈
      (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0065 :
    alphaDummy040 ∈
      (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv ∪
        ((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy039) (Class.cv alphaDummy040))).fv)
        support_part_0065)
  have support_part_0066 :
    alphaDummy043 ∈
      (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0066 :
    alphaDummy043 ∈
      (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv ∪
        ((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy042) (Class.cv alphaDummy043))).fv)
        support_part_0066)
  have support_part_0067 : alphaDummy040 ∈ (((Class.cv alphaDummy040)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0067 :
    alphaDummy040 ∈
      (((Class.cv alphaDummy039)).fv ∪ ((Class.cv alphaDummy040)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy039)).fv) support_part_0067)
  have support_part_0068 : alphaDummy043 ∈ (((Class.cv alphaDummy043)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0068 :
    alphaDummy043 ∈
      (((Class.cv alphaDummy042)).fv ∪ ((Class.cv alphaDummy043)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy042)).fv) support_part_0068)
  have support_part_0069 :
    alphaDummy039 ∈ (((synCcompl (Class.cv alphaDummy039))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0069 :
    alphaDummy039 ∈
      (((synCcompl (Class.cv alphaDummy039))).fv ∪
        ((synCcompl (Class.cv alphaDummy040))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy040))).fv) support_part_0069)
  have support_part_0070 :
    alphaDummy042 ∈ (((synCcompl (Class.cv alphaDummy042))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0070 :
    alphaDummy042 ∈
      (((synCcompl (Class.cv alphaDummy042))).fv ∪
        ((synCcompl (Class.cv alphaDummy043))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy043))).fv) support_part_0070)
  have support_part_0071 : alphaDummy039 ∈ (((Class.cv alphaDummy039)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0071 :
    alphaDummy039 ∈
      (((Class.cv alphaDummy039)).fv ∪ ((Class.cv alphaDummy039)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy039)).fv) support_part_0071)
  have support_part_0072 : alphaDummy042 ∈ (((Class.cv alphaDummy042)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0072 :
    alphaDummy042 ∈
      (((Class.cv alphaDummy042)).fv ∪ ((Class.cv alphaDummy042)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy042)).fv) support_part_0072)
  have support_part_0073 :
    alphaDummy040 ∈ (((synCcompl (Class.cv alphaDummy040))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0073 :
    alphaDummy040 ∈
      (((synCcompl (Class.cv alphaDummy039))).fv ∪
        ((synCcompl (Class.cv alphaDummy040))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy039))).fv) support_part_0073)
  have support_part_0074 :
    alphaDummy043 ∈ (((synCcompl (Class.cv alphaDummy043))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0074 :
    alphaDummy043 ∈
      (((synCcompl (Class.cv alphaDummy042))).fv ∪
        ((synCcompl (Class.cv alphaDummy043))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy042))).fv) support_part_0074)
  have support_part_0075 : alphaDummy040 ∈ (((Class.cv alphaDummy040)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0075 :
    alphaDummy040 ∈
      (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy040)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy040)).fv) support_part_0075)
  have support_part_0076 : alphaDummy043 ∈ (((Class.cv alphaDummy043)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0076 :
    alphaDummy043 ∈
      (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy043)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy043)).fv) support_part_0076)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy016, alphaDummy017), (alphaDummy014, alphaDummy015),
        (alphaDummy012, alphaDummy013), (alphaDummy004, alphaDummy005),
        (alphaDummy001, n), (alphaDummy000, m), (alphaDummy003, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy016)
          (synCcompl (synCsn (Class.cv alphaDummy000)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy016)
            (synCcompl (synCsn (Class.cv alphaDummy001))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy017) (synCcompl (synCsn (Class.cv m))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy017)
            (synCcompl (synCsn (Class.cv n)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_m_n (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_m_n (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy032, alphaDummy032), (alphaDummy031, alphaDummy031),
        (alphaDummy030, alphaDummy030), (alphaDummy001, alphaDummy001),
        (alphaDummy000, alphaDummy000), (alphaDummy028, alphaDummy028),
        (alphaDummy027, alphaDummy027), (alphaDummy002, p), (alphaDummy001, n),
        (alphaDummy000, m), (alphaDummy003, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy031) (Class.cv alphaDummy032))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy030)
            (synCun (Class.cv alphaDummy031) (Class.cv alphaDummy032)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy031) (Class.cv alphaDummy032))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy030)
            (synCun (Class.cv alphaDummy031) (Class.cv alphaDummy032))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
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
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy046, alphaDummy049), (alphaDummy045, alphaDummy048),
        (alphaDummy044, alphaDummy047), (alphaDummy039, alphaDummy042),
        (alphaDummy038, alphaDummy041), (alphaDummy002, p), (alphaDummy001, n),
        (alphaDummy000, m), (alphaDummy003, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy045) (Class.cv alphaDummy046))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy044)
            (synCun (Class.cv alphaDummy045) (Class.cv alphaDummy046)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy048) (Class.cv alphaDummy049))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy047)
            (synCun (Class.cv alphaDummy048) (Class.cv alphaDummy049))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
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
                (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv) (by decide))
              (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
              (TAlphaVar.there (freshVar_injective
                  (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy002)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy002)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪
                                      ((Class.cv alphaDummy002)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv m)).fv ∪ ((Class.cv p)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy040, alphaDummy043), (alphaDummy039, alphaDummy042),
        (alphaDummy038, alphaDummy041), (alphaDummy002, p), (alphaDummy001, n),
        (alphaDummy000, m), (alphaDummy003, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy039) (Class.cv alphaDummy040))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy038)
            (synCun (Class.cv alphaDummy039) (Class.cv alphaDummy040)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy042) (Class.cv alphaDummy043))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy041)
            (synCun (Class.cv alphaDummy042) (Class.cv alphaDummy043))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((synCplc (Class.cv alphaDummy000)
                                        (Class.cv alphaDummy002))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((synCplc (Class.cv alphaDummy000)
                                        (Class.cv alphaDummy002))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
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
                (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
                  ((synC1c)).fv) (by decide)) (freshVar_injective
                (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.there (freshVar_injective
                  (((synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))).fv ∪
                    ((synC1c)).fv) (by decide)) (freshVar_injective
                  (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((synCplc (Class.cv alphaDummy000)
        (Class.cv alphaDummy002))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
                                    (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((synCplc (Class.cv alphaDummy000)
        (Class.cv alphaDummy002))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
                                    (((synCplc (Class.cv m) (Class.cv p))).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0004 :
    TAlphaWff
      [(alphaDummy002, p), (alphaDummy001, n), (alphaDummy000, m),
        (alphaDummy003, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy002) (synCnnc)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy001)
            (synCplc (synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))
              (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv p) (synCnnc)) (Wff.neg (Wff.classEq (Class.cv n)
            (synCplc (synCplc (Class.cv m) (Class.cv p)) (synC1c))))) :=
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
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg splitAlpha0001)))))) (TAlphaClass.cv
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
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_n_p
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_m_p
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_m_n (TAlphaVar.here _ _ _))))))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 2))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 2))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0041 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0042 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0041 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0042 0)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.neg splitAlpha0002))))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                    (TAlphaVar.here _ _ _)))))))))
                    (TAlphaWff.neg splitAlpha0003)))))))))
  have splitAlpha0005 :
    TAlphaWff [(alphaDummy001, n), (alphaDummy000, m), (alphaDummy003, x)]
      (Wff.imp (Wff.classEq (Class.cv alphaDummy003)
          (synCopk (Class.cv alphaDummy000) (Class.cv alphaDummy001))) (Wff.neg
          (synWa (synWne (Class.cv alphaDummy000) (synC0))
            (synWrex alphaDummy002 (synCnnc) (Wff.classEq (Class.cv alphaDummy001)
                (synCplc (synCplc (Class.cv alphaDummy000) (Class.cv alphaDummy002))
                  (synC1c)))))))
      (Wff.imp (Wff.classEq (Class.cv x) (synCopk (Class.cv m) (Class.cv n))) (Wff.neg
          (synWa (synWne (Class.cv m) (synC0)) (synWrex p (synCnnc)
              (Wff.classEq (Class.cv n)
                (synCplc (synCplc (Class.cv m) (Class.cv p)) (synC1c))))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_n_x)
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
              (Ne.symm dv_m_x) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_m_n (TAlphaVar.here _ _ _))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_m_n (TAlphaVar.here _ _ _))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg splitAlpha0000))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg splitAlpha0000))))))))))))))
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_m_n (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.ex (TAlphaWff.neg splitAlpha0004)))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg splitAlpha0005))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
