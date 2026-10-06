/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001036Proj2Reflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_proj2`. -/
@[expose]
noncomputable def nominalDfProj2 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (synCproj2 A)
        (.cab x (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) A))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar (((synCcompl (synCphi (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy002 : Var :=
    (freshVar
      (((synCcompl (synCphi (Class.cv x)))).fv ∪ ((synCcompl (synCsn (synC0c)))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((synCphi (Class.cv alphaDummy000))).fv ∪
        ((synCphi (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((synCphi (Class.cv x))).fv ∪ ((synCphi (Class.cv x))).fv) 0)
  let alphaDummy005 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy006 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy007 : Var := (freshVar (((Class.cv x)).fv) 0)
  let alphaDummy008 : Var := (freshVar (((Class.cv x)).fv) 1)
  let alphaDummy009 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy005) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy005) (synC1c))).fv ∪
        ((Class.cv alphaDummy005)).fv) 0)
  let alphaDummy010 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy007) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy007) (synC1c))).fv ∪
        ((Class.cv alphaDummy007)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy013 : Var :=
    (freshVar (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy014 : Var :=
    (freshVar (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy017 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv ∪
        ((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv ∪
        ((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy013)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy016)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy012))).fv ∪
        ((synCcompl (Class.cv alphaDummy013))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy015))).fv ∪
        ((synCcompl (Class.cv alphaDummy016))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy015)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy013)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) 0)
  have fresh_034 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_mem_0000 :
    alphaDummy000 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 :
    x ∈
      (((synCcompl (synCphi (Class.cv x)))).fv ∪ ((synCcompl (synCsn (synC0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alphaDummy000 ∈
      (((synCphi (Class.cv alphaDummy000))).fv ∪
        ((synCphi (Class.cv alphaDummy000))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    x ∈ (((synCphi (Class.cv x))).fv ∪ ((synCphi (Class.cv x))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0004 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 : x ∈ (((Class.cv x)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
    alphaDummy005 ∈
      (((Wff.classMem (Class.cv alphaDummy005) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy005) (synC1c))).fv ∪
        ((Class.cv alphaDummy005)).fv) :=
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
  have support_mem_0007 :
    alphaDummy007 ∈
      (((Wff.classMem (Class.cv alphaDummy007) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy007) (synC1c))).fv ∪
        ((Class.cv alphaDummy007)).fv) :=
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
  have support_mem_0008 :
    alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alphaDummy007 ∈ (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
    alphaDummy012 ∈
      (((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv ∪
        ((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alphaDummy015 ∈
      (((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv ∪
        ((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy013)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alphaDummy015 ∈
      (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy016)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alphaDummy013 ∈
      (((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv ∪
        ((synCnin (Class.cv alphaDummy012) (Class.cv alphaDummy013))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy016 ∈
      (((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv ∪
        ((synCnin (Class.cv alphaDummy015) (Class.cv alphaDummy016))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy013 ∈
      (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy013)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy016)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy012 ∈
      (((synCcompl (Class.cv alphaDummy012))).fv ∪
        ((synCcompl (Class.cv alphaDummy013))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy015 ∈
      (((synCcompl (Class.cv alphaDummy015))).fv ∪
        ((synCcompl (Class.cv alphaDummy016))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy015 ∈
      (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy015)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alphaDummy013 ∈
      (((synCcompl (Class.cv alphaDummy012))).fv ∪
        ((synCcompl (Class.cv alphaDummy013))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alphaDummy016 ∈
      (((synCcompl (Class.cv alphaDummy015))).fv ∪
        ((synCcompl (Class.cv alphaDummy016))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alphaDummy013 ∈
      (((Class.cv alphaDummy013)).fv ∪ ((Class.cv alphaDummy013)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have wpp_notmem_0000 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0001 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0002 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0003 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0004 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alphaDummy014 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alphaDummy015 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alphaDummy013 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy016 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0000 :
    TReflOn
      [(alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy011, alphaDummy014), (alphaDummy009, alphaDummy010),
        (alphaDummy005, alphaDummy007), (alphaDummy006, alphaDummy008),
        (alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
        (alphaDummy000, x)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have wpp_notmem_0018 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0019 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0023 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0026 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0028 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : alphaDummy014 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alphaDummy015 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy013 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alphaDummy016 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy011, alphaDummy014), (alphaDummy009, alphaDummy010),
        (alphaDummy005, alphaDummy007), (alphaDummy006, alphaDummy008),
        (alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
        (alphaDummy000, x)]
      ((synC0)).fv :=
    by
    intro u hu
    exact
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
                        (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu))
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy011, alphaDummy014), (alphaDummy009, alphaDummy010),
        (alphaDummy005, alphaDummy007), (alphaDummy006, alphaDummy008),
        (alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
        (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy012) (Class.cv alphaDummy013))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy011)
            (synCun (Class.cv alphaDummy012) (Class.cv alphaDummy013)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy015) (Class.cv alphaDummy016))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy014)
            (synCun (Class.cv alphaDummy015) (Class.cv alphaDummy016))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
            (alphaDummy011, alphaDummy014), (alphaDummy009, alphaDummy010),
            (alphaDummy005, alphaDummy007), (alphaDummy006, alphaDummy008),
            (alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
            (alphaDummy000, x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy005)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy007)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0036 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0037 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0038 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0039 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0040 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0041 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0042 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0043 : alphaDummy008 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0044 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0045 : alphaDummy007 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0046 : alphaDummy009 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0047 : alphaDummy010 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy009, alphaDummy010), (alphaDummy005, alphaDummy007),
        (alphaDummy006, alphaDummy008), (alphaDummy003, alphaDummy004),
        (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
      ((synCnnc)).fv :=
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
                  (TAlphaVar.free (by simp) (by simp))))))))
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
        (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy003) (synCphi (Class.cv alphaDummy000)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy003)
            (synCphi (Class.cv alphaDummy000)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy004) (synCphi (Class.cv x)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy004) (synCphi (Class.cv x))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy000)).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy013, alphaDummy016),
        (alphaDummy012, alphaDummy015), (alphaDummy011, alphaDummy014),
        (alphaDummy009, alphaDummy010), (alphaDummy005, alphaDummy007),
        (alphaDummy006, alphaDummy008), (alphaDummy003, alphaDummy004),
        (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg splitAlpha0000))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy009, alphaDummy010),
                              (alphaDummy005, alphaDummy007),
                              (alphaDummy006, alphaDummy008),
                              (alphaDummy003, alphaDummy004),
                              (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy009, alphaDummy010),
                              (alphaDummy005, alphaDummy007),
                              (alphaDummy006, alphaDummy008),
                              (alphaDummy003, alphaDummy004),
                              (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                            (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy000)).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.reflOfClosed
        [(alphaDummy013, alphaDummy016), (alphaDummy012, alphaDummy015),
        (alphaDummy011, alphaDummy014), (alphaDummy009, alphaDummy010),
        (alphaDummy005, alphaDummy007), (alphaDummy006, alphaDummy008),
        (alphaDummy003, alphaDummy004), (alphaDummy001, alphaDummy002),
        (alphaDummy000, x)] (synC1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg splitAlpha0000))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy009, alphaDummy010),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy006, alphaDummy008),
                                (alphaDummy003, alphaDummy004),
                                (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy009, alphaDummy010),
                                (alphaDummy005, alphaDummy007),
                                (alphaDummy006, alphaDummy008),
                                (alphaDummy003, alphaDummy004),
                                (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0048 : alphaDummy000 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0049 : x ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0050 : alphaDummy001 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_notmem_0051 : alphaDummy002 ∉ ((synCcompl (synCsn (synC0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (synC0c)) ▸ h_mem))) ((fv_syn_ccompl (synCsn (synC0c))) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn [(alphaDummy001, alphaDummy002), (alphaDummy000, x)]
      ((synCcompl (synCsn (synC0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))
  have focused_notmem_0000 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((A).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => hu)
  have wpp_notmem_0052 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0053 : x ∉ (A).fv := by exact dv_A_x
  have wpp_refl_0004 : TReflOn [(alphaDummy000, x)] (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg splitAlpha0001))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [(alphaDummy001, alphaDummy002), (alphaDummy000, x)]
                    (synCcompl (synCsn (synC0c)))
                    (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))
          (TAlphaClass.reflOfReflOn [(alphaDummy000, x)] A wpp_refl_0004)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
