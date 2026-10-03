/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C068C001Part012

/-! NF weak partition development: NAR4C068C001Part013. -/


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

theorem nb068_support_mem_0498 :
    (nb068_alpha_dummy_450) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0499 (f : Var) :
    (nb068_alpha_dummy_452 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0500 :
    (nb068_alpha_dummy_000) ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0501 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0502 :
    (nb068_alpha_dummy_000) ∈
      (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0503 (f : Var) :
    f ∈
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0504 :
    (nb068_alpha_dummy_000) ∈
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0505 :
    (nb068_alpha_dummy_000) ∈
      (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
                (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
                (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_329) from (by
          unfold nb068_alpha_dummy_329;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0506 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0507 (f : Var) :
    f ∈
      (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb068_alpha_dummy_332 f) from (by
          unfold nb068_alpha_dummy_332;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0508 :
    (nb068_alpha_dummy_000) ∈
      (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_407)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0509 (f : Var) :
    f ∈
      (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0510 :
    (nb068_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0511 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0512 :
    (nb068_alpha_dummy_329) ∈
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0513 :
    (nb068_alpha_dummy_329) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_485) from (by
          unfold nb068_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_486) from (by
            unfold nb068_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0514 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0515 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_487 f) from (by
          unfold nb068_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_488 f) from (by
            unfold nb068_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0516 :
    (nb068_alpha_dummy_329) ∈
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_485) from (by
          unfold nb068_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_329) ≠ (nb068_alpha_dummy_486) from (by
            unfold nb068_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0517 (f : Var) :
    (nb068_alpha_dummy_332 f) ∈
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_487 f) from (by
          unfold nb068_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_332 f) ≠ (nb068_alpha_dummy_488 f) from (by
            unfold nb068_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0518 :
    (nb068_alpha_dummy_486) ∈ (((Class.cv (nb068_alpha_dummy_486))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0519 (f : Var) :
    (nb068_alpha_dummy_488 f) ∈ (((Class.cv (nb068_alpha_dummy_488 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0520 :
    (nb068_alpha_dummy_493) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_493))).fv) :=
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

theorem nb068_support_mem_0521 (f : Var) :
    (nb068_alpha_dummy_495 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_495 f))).fv) :=
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

theorem nb068_support_mem_0522 :
    (nb068_alpha_dummy_493) ∈
      (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0523 (f : Var) :
    (nb068_alpha_dummy_495 f) ∈
      (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0524 :
    (nb068_alpha_dummy_500) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_500))
            (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0525 (f : Var) :
    (nb068_alpha_dummy_503 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0526 :
    (nb068_alpha_dummy_500) ∈
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0527 (f : Var) :
    (nb068_alpha_dummy_503 f) ∈
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0528 :
    (nb068_alpha_dummy_501) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_500))
            (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0529 (f : Var) :
    (nb068_alpha_dummy_504 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0530 :
    (nb068_alpha_dummy_501) ∈
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0531 (f : Var) :
    (nb068_alpha_dummy_504 f) ∈
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0532 :
    (nb068_alpha_dummy_500) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0533 (f : Var) :
    (nb068_alpha_dummy_503 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0534 :
    (nb068_alpha_dummy_500) ∈
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0535 (f : Var) :
    (nb068_alpha_dummy_503 f) ∈
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0536 :
    (nb068_alpha_dummy_501) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0537 (f : Var) :
    (nb068_alpha_dummy_504 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0538 :
    (nb068_alpha_dummy_501) ∈
      (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0539 (f : Var) :
    (nb068_alpha_dummy_504 f) ∈
      (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0540 :
    (nb068_alpha_dummy_328) ∈
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0541 :
    (nb068_alpha_dummy_328) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_485) from (by
          unfold nb068_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_486) from (by
            unfold nb068_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0542 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0543 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_487 f) from (by
          unfold nb068_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_488 f) from (by
            unfold nb068_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0544 :
    (nb068_alpha_dummy_328) ∈
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_485) from (by
          unfold nb068_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_486) from (by
            unfold nb068_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0545 (f : Var) :
    (nb068_alpha_dummy_331 f) ∈
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_487 f) from (by
          unfold nb068_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_488 f) from (by
            unfold nb068_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0546 :
    (nb068_alpha_dummy_486) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0547 (f : Var) :
    (nb068_alpha_dummy_488 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0548 :
    (nb068_alpha_dummy_486) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0549 (f : Var) :
    (nb068_alpha_dummy_488 f) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_compact_fv_empty_0020 : (nb068_alpha_dummy_002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0022 : (nb068_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0024 : (nb068_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0025 (x : Var) (y : Var) (f : Var) :
    (nb068_alpha_dummy_004 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
