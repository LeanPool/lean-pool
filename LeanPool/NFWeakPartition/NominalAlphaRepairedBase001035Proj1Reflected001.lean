/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001035Proj1Reflected001. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_proj1`. -/
@[expose]
noncomputable def nominalDfProj1 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCproj1 A) (.cab x (.classMem (synCphi (.cv x)) A))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy002 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy003 : Var := (freshVar (((Class.cv x)).fv) 0)
  let alphaDummy004 : Var := (freshVar (((Class.cv x)).fv) 1)
  let alphaDummy005 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy001) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy001) (synC1c))).fv ∪
        ((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy003) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy003) (synC1c))).fv ∪
        ((Class.cv alphaDummy003)).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy008 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy012 : Var :=
    (freshVar (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy013 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) 0)
  have fresh_030 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_mem_0000 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 : x ∈ (((Class.cv x)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alphaDummy001 ∈
      (((Wff.classMem (Class.cv alphaDummy001) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy001) (synC1c))).fv ∪
        ((Class.cv alphaDummy001)).fv) :=
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
    alphaDummy003 ∈
      (((Wff.classMem (Class.cv alphaDummy003) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy003) (synC1c))).fv ∪
        ((Class.cv alphaDummy003)).fv) :=
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
    alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
    alphaDummy008 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 :
    alphaDummy011 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alphaDummy008 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
    alphaDummy009 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alphaDummy012 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alphaDummy008 ∈
      (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alphaDummy011 ∈
      (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alphaDummy008 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy008)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alphaDummy009 ∈
      (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alphaDummy012 ∈
      (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have wpp_notmem_0000 : alphaDummy000 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0001 : x ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0002 : alphaDummy002 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0003 : alphaDummy004 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0004 : alphaDummy001 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : alphaDummy003 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alphaDummy005 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : alphaDummy006 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alphaDummy007 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alphaDummy010 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alphaDummy008 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alphaDummy011 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alphaDummy009 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alphaDummy012 ∉ ((synC1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0000 :
    TReflOn
      [(alphaDummy009, alphaDummy012), (alphaDummy008, alphaDummy011),
        (alphaDummy007, alphaDummy010), (alphaDummy005, alphaDummy006),
        (alphaDummy001, alphaDummy003), (alphaDummy002, alphaDummy004),
        (alphaDummy000, x)]
      ((synC1c)).fv :=
    by
    intro u hu
    exact
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
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have wpp_notmem_0014 : alphaDummy000 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0015 : x ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0016 : alphaDummy002 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0017 : alphaDummy004 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0018 : alphaDummy001 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0019 : alphaDummy003 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0020 : alphaDummy005 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0021 : alphaDummy006 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0022 : alphaDummy007 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0023 : alphaDummy010 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0024 : alphaDummy008 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0025 : alphaDummy011 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0026 : alphaDummy009 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0027 : alphaDummy012 ∉ ((synC0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alphaDummy009, alphaDummy012), (alphaDummy008, alphaDummy011),
        (alphaDummy007, alphaDummy010), (alphaDummy005, alphaDummy006),
        (alphaDummy001, alphaDummy003), (alphaDummy002, alphaDummy004),
        (alphaDummy000, x)]
      ((synC0)).fv :=
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
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy009, alphaDummy012), (alphaDummy008, alphaDummy011),
        (alphaDummy007, alphaDummy010), (alphaDummy005, alphaDummy006),
        (alphaDummy001, alphaDummy003), (alphaDummy002, alphaDummy004),
        (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy008) (Class.cv alphaDummy009))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy007)
            (synCun (Class.cv alphaDummy008) (Class.cv alphaDummy009)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy011) (Class.cv alphaDummy012))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy010)
            (synCun (Class.cv alphaDummy011) (Class.cv alphaDummy012))))) :=
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
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
          [(alphaDummy009, alphaDummy012), (alphaDummy008, alphaDummy011),
            (alphaDummy007, alphaDummy010), (alphaDummy005, alphaDummy006),
            (alphaDummy001, alphaDummy003), (alphaDummy002, alphaDummy004),
            (alphaDummy000, x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy003)).fv ∪ ((synC1c)).fv)
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
  have wpp_notmem_0028 : alphaDummy000 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0030 : alphaDummy002 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0031 : alphaDummy004 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0032 : alphaDummy001 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0033 : alphaDummy003 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0034 : alphaDummy005 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0035 : alphaDummy006 ∉ ((synCnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alphaDummy005, alphaDummy006), (alphaDummy001, alphaDummy003),
        (alphaDummy002, alphaDummy004), (alphaDummy000, x)]
      ((synCnnc)).fv :=
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
              (TAlphaVar.free (by simp) (by simp))))))
  have focused_notmem_0000 : alphaDummy000 ∉ A.fv :=
    by
    change freshVar ((A).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => hu)
  have wpp_notmem_0036 : alphaDummy000 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0037 : x ∉ (A).fv := by exact dv_A_x
  have wpp_refl_0003 : TReflOn [(alphaDummy000, x)] (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alphaDummy000)).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv) (by decide))
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
        [(alphaDummy009, alphaDummy012), (alphaDummy008, alphaDummy011),
        (alphaDummy007, alphaDummy010), (alphaDummy005, alphaDummy006),
        (alphaDummy001, alphaDummy003), (alphaDummy002, alphaDummy004),
        (alphaDummy000, x)] (synC1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg splitAlpha0000))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                              [(alphaDummy005, alphaDummy006),
                                (alphaDummy001, alphaDummy003),
                                (alphaDummy002, alphaDummy004), (alphaDummy000, x)]
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
                              [(alphaDummy005, alphaDummy006),
                                (alphaDummy001, alphaDummy003),
                                (alphaDummy002, alphaDummy004), (alphaDummy000, x)]
                              (synCnnc) (by simp only [fv_syn_cnnc])))))))))))
          (TAlphaClass.reflOfReflOn [(alphaDummy000, x)] A wpp_refl_0003)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
