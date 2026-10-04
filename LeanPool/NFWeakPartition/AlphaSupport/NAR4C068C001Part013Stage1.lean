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
    (nb068AlphaDummy450) ∈
      (((synCphi (Class.cv (nb068AlphaDummy450)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy450)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0499 (f : Var) :
    (nb068AlphaDummy452 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0500 :
    (nb068AlphaDummy000) ∈
      (((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv) :=
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
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv) :=
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
    (nb068AlphaDummy000) ∈
      (((synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
            (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000)))))).fv ∪ ((synCid)).fv) :=
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
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv) :=
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
    (nb068AlphaDummy000) ∈
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0505 :
    (nb068AlphaDummy000) ∈
      (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
                (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
                (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy329) from (by
          unfold nb068AlphaDummy329;
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
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0507 (f : Var) :
    f ∈
      (({(nb068AlphaDummy330 f)} : Finset Var) ∪ ({(nb068AlphaDummy331 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy332 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy330 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
              (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb068AlphaDummy332 f) from (by
          unfold nb068AlphaDummy332;
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
    (nb068AlphaDummy000) ∈
      (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy407)))).fv) :=
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
      (({(nb068AlphaDummy409 f)} : Finset Var) ∪ ({(nb068AlphaDummy410 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f)))).fv) :=
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
    (nb068AlphaDummy000) ∈ (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0511 (f : Var) : f ∈ (((synCcnv (Class.cv f))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0512 :
    (nb068AlphaDummy329) ∈
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0513 :
    (nb068AlphaDummy329) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCphi (Class.cv (nb068AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from (by
          unfold nb068AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
            unfold nb068AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0514 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0515 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCphi (Class.cv (nb068AlphaDummy488 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy487 f) from (by
          unfold nb068AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy488 f) from (by
            unfold nb068AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0516 :
    (nb068AlphaDummy329) ∈
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv ∪
        ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from (by
          unfold nb068AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
            unfold nb068AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0517 (f : Var) :
    (nb068AlphaDummy332 f) ∈
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy487 f) from (by
          unfold nb068AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy332 f) ≠ (nb068AlphaDummy488 f) from (by
            unfold nb068AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0518 :
    (nb068AlphaDummy486) ∈ (((Class.cv (nb068AlphaDummy486))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0519 (f : Var) :
    (nb068AlphaDummy488 f) ∈ (((Class.cv (nb068AlphaDummy488 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0520 :
    (nb068AlphaDummy493) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy493))).fv) :=
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
    (nb068AlphaDummy495 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy495 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy495 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy495 f))).fv) :=
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
    (nb068AlphaDummy493) ∈
      (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0523 (f : Var) :
    (nb068AlphaDummy495 f) ∈
      (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0524 :
    (nb068AlphaDummy500) ∈
      (((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy500))
            (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0525 (f : Var) :
    (nb068AlphaDummy503 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0526 :
    (nb068AlphaDummy500) ∈
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0527 (f : Var) :
    (nb068AlphaDummy503 f) ∈
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0528 :
    (nb068AlphaDummy501) ∈
      (((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy500))
            (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0529 (f : Var) :
    (nb068AlphaDummy504 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0530 :
    (nb068AlphaDummy501) ∈
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0531 (f : Var) :
    (nb068AlphaDummy504 f) ∈
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0532 :
    (nb068AlphaDummy500) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0533 (f : Var) :
    (nb068AlphaDummy503 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy503 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0534 :
    (nb068AlphaDummy500) ∈
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy500))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0535 (f : Var) :
    (nb068AlphaDummy503 f) ∈
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy503 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0536 :
    (nb068AlphaDummy501) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0537 (f : Var) :
    (nb068AlphaDummy504 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy503 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0538 :
    (nb068AlphaDummy501) ∈
      (((Class.cv (nb068AlphaDummy501))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0539 (f : Var) :
    (nb068AlphaDummy504 f) ∈
      (((Class.cv (nb068AlphaDummy504 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0540 :
    (nb068AlphaDummy328) ∈
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0541 :
    (nb068AlphaDummy328) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCphi (Class.cv (nb068AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy485) from (by
          unfold nb068AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy486) from (by
            unfold nb068AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0542 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0543 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCphi (Class.cv (nb068AlphaDummy488 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy487 f) from (by
          unfold nb068AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy488 f) from (by
            unfold nb068AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0544 :
    (nb068AlphaDummy328) ∈
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy485) from (by
          unfold nb068AlphaDummy485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy486) from (by
            unfold nb068AlphaDummy486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0545 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy487 f) from (by
          unfold nb068AlphaDummy487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy488 f) from (by
            unfold nb068AlphaDummy488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0546 :
    (nb068AlphaDummy486) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0547 (f : Var) :
    (nb068AlphaDummy488 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy488 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0548 :
    (nb068AlphaDummy486) ∈
      (((synCphi (Class.cv (nb068AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy486)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0549 (f : Var) :
    (nb068AlphaDummy488 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_compact_fv_empty_0020 : (nb068AlphaDummy002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0022 : (nb068AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0024 : (nb068AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0025 (x : Var) (y : Var) (f : Var) :
    (nb068AlphaDummy004 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
