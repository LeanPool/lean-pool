/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block002

/-! NF weak partition development: NAR4C077C001Part009. -/


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

theorem nb077_support_mem_0304 (F : Class) (I : Class) :
    (nb077AlphaDummy297 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy296 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0305 (x : Var) :
    (nb077AlphaDummy300 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy299 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0306 (F : Class) (I : Class) :
    (nb077AlphaDummy297 F I) ∈
      (((Class.cv (nb077AlphaDummy297 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0307 (x : Var) :
    (nb077AlphaDummy300 x) ∈
      (((Class.cv (nb077AlphaDummy300 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0308 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0309 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy311 F I) from (by
          unfold nb077AlphaDummy311;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy312 F I) from (by
            unfold nb077AlphaDummy312;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0310 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0311 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCphi (Class.cv (nb077AlphaDummy314 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold nb077AlphaDummy313;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy314 x) from (by
            unfold nb077AlphaDummy314;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0312 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy311 F I) from (by
          unfold nb077AlphaDummy311;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy312 F I) from (by
            unfold nb077AlphaDummy312;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0313 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold nb077AlphaDummy313;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy314 x) from (by
            unfold nb077AlphaDummy314;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0314 (F : Class) (I : Class) :
    (nb077AlphaDummy312 F I) ∈ (((Class.cv (nb077AlphaDummy312 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0315 (x : Var) :
    (nb077AlphaDummy314 x) ∈ (((Class.cv (nb077AlphaDummy314 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0316 (F : Class) (I : Class) :
    (nb077AlphaDummy319 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy319 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy319 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy319 F I))).fv) :=
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

theorem nb077_support_mem_0317 (x : Var) :
    (nb077AlphaDummy321 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy321 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy321 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy321 x))).fv) :=
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

theorem nb077_support_mem_0318 (F : Class) (I : Class) :
    (nb077AlphaDummy319 F I) ∈
      (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0319 (x : Var) :
    (nb077AlphaDummy321 x) ∈
      (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0320 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0321 (x : Var) :
    (nb077AlphaDummy329 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0322 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ∈
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0323 (x : Var) :
    (nb077AlphaDummy329 x) ∈
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0324 (F : Class) (I : Class) :
    (nb077AlphaDummy327 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0325 (x : Var) :
    (nb077AlphaDummy330 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0326 (F : Class) (I : Class) :
    (nb077AlphaDummy327 F I) ∈
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0327 (x : Var) :
    (nb077AlphaDummy330 x) ∈
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0328 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy326 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0329 (x : Var) :
    (nb077AlphaDummy329 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy329 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0330 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ∈
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy326 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0331 (x : Var) :
    (nb077AlphaDummy329 x) ∈
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy329 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0332 (F : Class) (I : Class) :
    (nb077AlphaDummy327 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy326 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0333 (x : Var) :
    (nb077AlphaDummy330 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy329 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0334 (F : Class) (I : Class) :
    (nb077AlphaDummy327 F I) ∈
      (((Class.cv (nb077AlphaDummy327 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0335 (x : Var) :
    (nb077AlphaDummy330 x) ∈
      (((Class.cv (nb077AlphaDummy330 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0336 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0337 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy311 F I) from (by
          unfold nb077AlphaDummy311;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from (by
            unfold nb077AlphaDummy312;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0338 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0339 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCphi (Class.cv (nb077AlphaDummy314 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold nb077AlphaDummy313;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
            unfold nb077AlphaDummy314;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0340 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy311 F I) from (by
          unfold nb077AlphaDummy311;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from (by
            unfold nb077AlphaDummy312;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0341 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold nb077AlphaDummy313;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
            unfold nb077AlphaDummy314;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0342 (F : Class) (I : Class) :
    (nb077AlphaDummy312 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy312 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0343 (x : Var) :
    (nb077AlphaDummy314 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy314 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0344 (F : Class) (I : Class) :
    (nb077AlphaDummy312 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0345 (x : Var) :
    (nb077AlphaDummy314 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_compact_fv_empty_0000 (F : Class) (I : Class) :
    (nb077AlphaDummy009 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0000 (F : Class) (I : Class) :
    (nb077AlphaDummy009 F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0000 (F : Class) (I : Class) :
    (nb077AlphaDummy009 F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy009, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0000 F I) (nb077_focused_notmem_0000 F I))

theorem nb077_compact_fv_empty_0001 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy010 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0001 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy010 x F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0001 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy010 x F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy010, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0001 x F I) (nb077_focused_notmem_0001 x F I))

theorem nb077_compact_fv_empty_0002 (F : Class) (I : Class) :
    (nb077AlphaDummy007 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0002 (F : Class) (I : Class) :
    (nb077AlphaDummy007 F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCnin (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
          ((synCnin (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I)))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0002 (F : Class) (I : Class) :
    (nb077AlphaDummy007 F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy007, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0002 F I) (nb077_focused_notmem_0002 F I))

theorem nb077_compact_fv_empty_0003 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy008 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0003 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy008 x F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCnin (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
          ((synCnin (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy002 x F I)))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCsn (synCop (synC0c) I))
      (Class.cv (nb077AlphaDummy002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0003 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy008 x F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy008, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0003 x F I) (nb077_focused_notmem_0003 x F I))

theorem nb077_compact_fv_empty_0004 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0004 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪ ((synCpprod
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0004 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy001, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0004 F I) (nb077_focused_notmem_0004 F I))

theorem nb077_compact_fv_empty_0005 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0005 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉ I.fv :=
  by
  change
    freshVar
        (((synCsn (synCop (synC0c) I))).fv ∪
          ((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_csn (synCop (synC0c) I)]
  rw [fv_syn_cop (synC0c) I]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0005 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy002, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0005 x F I) (nb077_focused_notmem_0005 x F I))

theorem nb077_compact_fv_empty_0006 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0006 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉ I.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy001 F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
              (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                      (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy001 F I)))
                (Class.cv (nb077AlphaDummy001 F I)))))).fv)
        1 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy001 F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0004 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_csn (synCop (synC0c) I)]
    rw [fv_syn_cop (synC0c) I]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0006 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy004, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0006 F I) (nb077_focused_notmem_0006 F I))

theorem nb077_compact_fv_empty_0007 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0007 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉ I.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy002 x F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
              (synWss (synCima
                  (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy002 x F I)))
                (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
        1 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy002 x F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0005 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I))) (Class.cv (nb077AlphaDummy002 x F I)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss (synCsn (synCop (synC0c) I))
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_csn (synCop (synC0c) I)]
    rw [fv_syn_cop (synC0c) I]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0007 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy006, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0007 x F I) (nb077_focused_notmem_0007 x F I))

theorem nb077_compact_fv_empty_0008 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0008 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉ I.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy001 F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
              (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                      (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy001 F I)))
                (Class.cv (nb077AlphaDummy001 F I)))))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy001 F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0004 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
        (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_csn (synCop (synC0c) I)]
    rw [fv_syn_cop (synC0c) I]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0008 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy003, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0008 F I) (nb077_focused_notmem_0008 F I))

theorem nb077_compact_fv_empty_0009 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0009 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉ I.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077AlphaDummy002 x F I) (synWa
              (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
              (synWss (synCima
                  (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                  (Class.cv (nb077AlphaDummy002 x F I)))
                (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
        0 ∉
      I.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077AlphaDummy002 x F I)
      (synWa (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0005 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
        (synWss (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I))) (Class.cv (nb077AlphaDummy002 x F I)))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_wss (synCsn (synCop (synC0c) I))
        (Class.cv (nb077AlphaDummy002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_csn (synCop (synC0c) I)]
    rw [fv_syn_cop (synC0c) I]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0009 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉ ((synCsn (synCop (synC0c) I))).fv := by
  simpa only [nb077AlphaDummy005, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c,
    not_or] using
    (And.intro (nb077_compact_fv_empty_0009 x F I) (nb077_focused_notmem_0009 x F I))

theorem nb077_compact_envfresh_0000 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy009 F I), (nb077AlphaDummy010 x F I)),
        ((nb077AlphaDummy007 F I), (nb077AlphaDummy008 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCsn (synCop (synC0c) I))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077AlphaDummy009 F I) (nb077AlphaDummy010 x F I)
      (nb077_wpp_notmem_0000 F I) (nb077_wpp_notmem_0001 x F I)
      (TEnvFresh.consFresh (nb077AlphaDummy007 F I) (nb077AlphaDummy008 x F I)
        (nb077_wpp_notmem_0002 F I) (nb077_wpp_notmem_0003 x F I)
        (TEnvFresh.consFresh (nb077AlphaDummy001 F I) (nb077AlphaDummy002 x F I)
          (nb077_wpp_notmem_0004 F I) (nb077_wpp_notmem_0005 x F I)
          (TEnvFresh.consFresh (nb077AlphaDummy004 F I) (nb077AlphaDummy006 x F I)
            (nb077_wpp_notmem_0006 F I) (nb077_wpp_notmem_0007 x F I)
            (TEnvFresh.consFresh (nb077AlphaDummy003 F I) (nb077AlphaDummy005 x F I)
              (nb077_wpp_notmem_0008 F I) (nb077_wpp_notmem_0009 x F I)
              (TEnvFresh.nil ((synCsn (synCop (synC0c) I))).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0000`. -/
@[expose]
noncomputable def nb077WppRefl0000 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy009 F I), (nb077AlphaDummy010 x F I)),
        ((nb077AlphaDummy007 F I), (nb077AlphaDummy008 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCsn (synCop (synC0c) I))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0000 x F I)

theorem nb077_compact_envfresh_0001 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCsn (synCop (synC0c) I))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077AlphaDummy001 F I) (nb077AlphaDummy002 x F I)
      (nb077_wpp_notmem_0004 F I) (nb077_wpp_notmem_0005 x F I)
      (TEnvFresh.consFresh (nb077AlphaDummy004 F I) (nb077AlphaDummy006 x F I)
        (nb077_wpp_notmem_0006 F I) (nb077_wpp_notmem_0007 x F I)
        (TEnvFresh.consFresh (nb077AlphaDummy003 F I) (nb077AlphaDummy005 x F I)
          (nb077_wpp_notmem_0008 F I) (nb077_wpp_notmem_0009 x F I)
          (TEnvFresh.nil ((synCsn (synCop (synC0c) I))).fv))))

/-- Checked nominal proof certificate identified upstream as `nb077_wpp_refl_0001`. -/
@[expose]
noncomputable def nb077WppRefl0001 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      ((synCsn (synCop (synC0c) I))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0001 x F I)

theorem nb077_compact_fv_empty_0030 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0031 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0032 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0033 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0034 (F : Class) (I : Class) :
    (nb077AlphaDummy013 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0035 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy014 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0036 (F : Class) (I : Class) :
    (nb077AlphaDummy011 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0037 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy012 x F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
