/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block002

/-! NF weak partition development: NAR4C067C001Part009. -/


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

theorem nb067_support_mem_0320 :
    (nb067AlphaDummy297) ∈
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0321 (f : Var) :
    (nb067AlphaDummy300 f) ∈
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0322 :
    (nb067AlphaDummy296) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy296)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0323 (f : Var) :
    (nb067AlphaDummy299 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy299 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0324 :
    (nb067AlphaDummy296) ∈
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy296))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0325 (f : Var) :
    (nb067AlphaDummy299 f) ∈
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy299 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0326 :
    (nb067AlphaDummy297) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy296)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0327 (f : Var) :
    (nb067AlphaDummy300 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy299 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0328 :
    (nb067AlphaDummy297) ∈
      (((Class.cv (nb067AlphaDummy297))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0329 (f : Var) :
    (nb067AlphaDummy300 f) ∈
      (((Class.cv (nb067AlphaDummy300 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0330 :
    (nb067AlphaDummy277) ∈
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0331 :
    (nb067AlphaDummy277) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCphi (Class.cv (nb067AlphaDummy282)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0332 (f : Var) :
    (nb067AlphaDummy279 f) ∈
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0333 (f : Var) :
    (nb067AlphaDummy279 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCphi (Class.cv (nb067AlphaDummy284 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0334 :
    (nb067AlphaDummy277) ∈
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0335 (f : Var) :
    (nb067AlphaDummy279 f) ∈
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0336 :
    (nb067AlphaDummy282) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy282))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0337 (f : Var) :
    (nb067AlphaDummy284 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy284 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0338 :
    (nb067AlphaDummy282) ∈
      (((synCphi (Class.cv (nb067AlphaDummy282)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy282)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0339 (f : Var) :
    (nb067AlphaDummy284 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0340 :
    (nb067AlphaDummy000) ∈
      (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0341 (f : Var) :
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0342 :
    (nb067AlphaDummy322) ∈
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0343 :
    (nb067AlphaDummy322) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCphi (Class.cv (nb067AlphaDummy326)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0344 (f : Var) :
    (nb067AlphaDummy324 f) ∈
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0345 (f : Var) :
    (nb067AlphaDummy324 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCphi (Class.cv (nb067AlphaDummy328 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0346 :
    (nb067AlphaDummy322) ∈
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv ∪
        ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0347 (f : Var) :
    (nb067AlphaDummy324 f) ∈
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0348 :
    (nb067AlphaDummy326) ∈ (((Class.cv (nb067AlphaDummy326))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0349 (f : Var) :
    (nb067AlphaDummy328 f) ∈ (((Class.cv (nb067AlphaDummy328 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0350 :
    (nb067AlphaDummy333) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy333))).fv) :=
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

theorem nb067_support_mem_0351 (f : Var) :
    (nb067AlphaDummy335 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy335 f))).fv) :=
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

theorem nb067_support_mem_0352 :
    (nb067AlphaDummy333) ∈
      (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0353 (f : Var) :
    (nb067AlphaDummy335 f) ∈
      (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0354 :
    (nb067AlphaDummy340) ∈
      (((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy340))
            (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0355 (f : Var) :
    (nb067AlphaDummy343 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0356 :
    (nb067AlphaDummy340) ∈
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0357 (f : Var) :
    (nb067AlphaDummy343 f) ∈
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0358 :
    (nb067AlphaDummy341) ∈
      (((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy340))
            (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0359 (f : Var) :
    (nb067AlphaDummy344 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0360 :
    (nb067AlphaDummy341) ∈
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0361 (f : Var) :
    (nb067AlphaDummy344 f) ∈
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0362 :
    (nb067AlphaDummy340) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy340)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0363 (f : Var) :
    (nb067AlphaDummy343 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy343 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0364 :
    (nb067AlphaDummy340) ∈
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy340))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0365 (f : Var) :
    (nb067AlphaDummy343 f) ∈
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy343 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0366 :
    (nb067AlphaDummy341) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy340)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0367 (f : Var) :
    (nb067AlphaDummy344 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy343 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0368 :
    (nb067AlphaDummy341) ∈
      (((Class.cv (nb067AlphaDummy341))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0369 (f : Var) :
    (nb067AlphaDummy344 f) ∈
      (((Class.cv (nb067AlphaDummy344 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0370 :
    (nb067AlphaDummy321) ∈
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0371 :
    (nb067AlphaDummy321) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCphi (Class.cv (nb067AlphaDummy326)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0372 (f : Var) :
    (nb067AlphaDummy323 f) ∈
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0373 (f : Var) :
    (nb067AlphaDummy323 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCphi (Class.cv (nb067AlphaDummy328 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0374 :
    (nb067AlphaDummy321) ∈
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0375 (f : Var) :
    (nb067AlphaDummy323 f) ∈
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0376 :
    (nb067AlphaDummy326) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy326))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0377 (f : Var) :
    (nb067AlphaDummy328 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy328 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0378 :
    (nb067AlphaDummy326) ∈
      (((synCphi (Class.cv (nb067AlphaDummy326)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy326)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0379 (f : Var) :
    (nb067AlphaDummy328 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0380 :
    (nb067AlphaDummy000) ∈
      (((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0381 (x : Var) (f : Var) :
    f ∈
      (((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0382 :
    (nb067AlphaDummy000) ∈
      (((synCrn (Class.cv (nb067AlphaDummy000)))).fv ∪
        ((Class.cv (nb067AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0383 (x : Var) (f : Var) :
    f ∈ (((synCrn (Class.cv f))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0384 :
    (nb067AlphaDummy000) ∈
      (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0385 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0386 :
    (nb067AlphaDummy001) ∈
      (((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0387 (x : Var) (f : Var) :
    x ∈
      (((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0388 :
    (nb067AlphaDummy001) ∈
      (((synCrn (Class.cv (nb067AlphaDummy000)))).fv ∪
        ((Class.cv (nb067AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0389 (x : Var) (f : Var) :
    x ∈ (((synCrn (Class.cv f))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_compact_fv_empty_0028 : (nb067AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0029 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0030 : (nb067AlphaDummy002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0031 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0032 : (nb067AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0034 : (nb067AlphaDummy005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0035 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy006 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
