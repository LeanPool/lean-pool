/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part026`. -/


section

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

theorem nb078_support_mem_0596 :
    (nb078AlphaDummy569) ∈
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv ∪
        ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy577) from (by
          unfold nb078AlphaDummy577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy578) from (by
            unfold nb078AlphaDummy578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0597 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy579 g) from (by
          unfold nb078AlphaDummy579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy580 g) from (by
            unfold nb078AlphaDummy580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0598 :
    (nb078AlphaDummy578) ∈ (((Class.cv (nb078AlphaDummy578))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0599 (g : Var) :
    (nb078AlphaDummy580 g) ∈ (((Class.cv (nb078AlphaDummy580 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0600 :
    (nb078AlphaDummy585) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy585)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy585)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy585))).fv) :=
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

theorem nb078_support_mem_0601 (g : Var) :
    (nb078AlphaDummy587 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy587 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy587 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy587 g))).fv) :=
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

theorem nb078_support_mem_0602 :
    (nb078AlphaDummy585) ∈
      (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0603 (g : Var) :
    (nb078AlphaDummy587 g) ∈
      (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0604 :
    (nb078AlphaDummy592) ∈
      (((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy592))
            (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0605 (g : Var) :
    (nb078AlphaDummy595 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0606 :
    (nb078AlphaDummy592) ∈
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0607 (g : Var) :
    (nb078AlphaDummy595 g) ∈
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0608 :
    (nb078AlphaDummy593) ∈
      (((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy592))
            (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0609 (g : Var) :
    (nb078AlphaDummy596 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0610 :
    (nb078AlphaDummy593) ∈
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0611 (g : Var) :
    (nb078AlphaDummy596 g) ∈
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0612 :
    (nb078AlphaDummy592) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy592)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0613 (g : Var) :
    (nb078AlphaDummy595 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy595 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0614 :
    (nb078AlphaDummy592) ∈
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy592))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0615 (g : Var) :
    (nb078AlphaDummy595 g) ∈
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy595 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0616 :
    (nb078AlphaDummy593) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy592)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0617 (g : Var) :
    (nb078AlphaDummy596 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy595 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0618 :
    (nb078AlphaDummy593) ∈
      (((Class.cv (nb078AlphaDummy593))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0619 (g : Var) :
    (nb078AlphaDummy596 g) ∈
      (((Class.cv (nb078AlphaDummy596 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0620 :
    (nb078AlphaDummy570) ∈
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0621 :
    (nb078AlphaDummy570) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCphi (Class.cv (nb078AlphaDummy578)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy577) from (by
          unfold nb078AlphaDummy577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy578) from (by
            unfold nb078AlphaDummy578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0622 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0623 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCphi (Class.cv (nb078AlphaDummy580 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy579 g) from (by
          unfold nb078AlphaDummy579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy580 g) from (by
            unfold nb078AlphaDummy580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0624 :
    (nb078AlphaDummy570) ∈
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy577) from (by
          unfold nb078AlphaDummy577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy578) from (by
            unfold nb078AlphaDummy578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0625 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy579 g) from (by
          unfold nb078AlphaDummy579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy580 g) from (by
            unfold nb078AlphaDummy580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0626 :
    (nb078AlphaDummy578) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy578))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0627 (g : Var) :
    (nb078AlphaDummy580 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy580 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0628 :
    (nb078AlphaDummy578) ∈
      (((synCphi (Class.cv (nb078AlphaDummy578)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy578)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0629 (g : Var) :
    (nb078AlphaDummy580 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0630 :
    (nb078AlphaDummy569) ∈
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0631 :
    (nb078AlphaDummy569) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCphi (Class.cv (nb078AlphaDummy614)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy614) from (by
            unfold nb078AlphaDummy614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0632 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0633 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCphi (Class.cv (nb078AlphaDummy616 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy616 g) from (by
            unfold nb078AlphaDummy616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0634 :
    (nb078AlphaDummy569) ∈
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv ∪
        ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy614) from (by
            unfold nb078AlphaDummy614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0635 (g : Var) :
    (nb078AlphaDummy572 g) ∈
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy616 g) from (by
            unfold nb078AlphaDummy616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0636 :
    (nb078AlphaDummy614) ∈ (((Class.cv (nb078AlphaDummy614))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0637 (g : Var) :
    (nb078AlphaDummy616 g) ∈ (((Class.cv (nb078AlphaDummy616 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0638 :
    (nb078AlphaDummy621) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy621)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy621)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy621))).fv) :=
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

theorem nb078_support_mem_0639 (g : Var) :
    (nb078AlphaDummy623 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy623 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy623 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy623 g))).fv) :=
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

theorem nb078_support_mem_0640 :
    (nb078AlphaDummy621) ∈
      (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0641 (g : Var) :
    (nb078AlphaDummy623 g) ∈
      (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0642 :
    (nb078AlphaDummy628) ∈
      (((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy628))
            (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0643 (g : Var) :
    (nb078AlphaDummy631 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0644 :
    (nb078AlphaDummy628) ∈
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0645 (g : Var) :
    (nb078AlphaDummy631 g) ∈
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0646 :
    (nb078AlphaDummy629) ∈
      (((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy628))
            (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0647 (g : Var) :
    (nb078AlphaDummy632 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0648 :
    (nb078AlphaDummy629) ∈
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0649 (g : Var) :
    (nb078AlphaDummy632 g) ∈
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0650 :
    (nb078AlphaDummy628) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy628)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0651 (g : Var) :
    (nb078AlphaDummy631 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy631 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0652 :
    (nb078AlphaDummy628) ∈
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy628))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0653 (g : Var) :
    (nb078AlphaDummy631 g) ∈
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy631 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0654 :
    (nb078AlphaDummy629) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy628)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0655 (g : Var) :
    (nb078AlphaDummy632 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy631 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0656 :
    (nb078AlphaDummy629) ∈
      (((Class.cv (nb078AlphaDummy629))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0657 (g : Var) :
    (nb078AlphaDummy632 g) ∈
      (((Class.cv (nb078AlphaDummy632 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0658 :
    (nb078AlphaDummy571) ∈
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0659 :
    (nb078AlphaDummy571) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCphi (Class.cv (nb078AlphaDummy614)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy614) from (by
            unfold nb078AlphaDummy614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0660 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0661 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCphi (Class.cv (nb078AlphaDummy616 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy616 g) from (by
            unfold nb078AlphaDummy616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0662 :
    (nb078AlphaDummy571) ∈
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy613) from (by
          unfold nb078AlphaDummy613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy614) from (by
            unfold nb078AlphaDummy614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0663 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy615 g) from (by
          unfold nb078AlphaDummy615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy616 g) from (by
            unfold nb078AlphaDummy616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0664 :
    (nb078AlphaDummy614) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy614))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0665 (g : Var) :
    (nb078AlphaDummy616 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy616 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0666 :
    (nb078AlphaDummy614) ∈
      (((synCphi (Class.cv (nb078AlphaDummy614)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy614)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0667 (g : Var) :
    (nb078AlphaDummy616 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0668 :
    (nb078AlphaDummy649) ∈
      (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy650))
            (synCcnv (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy649)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0669 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (({(nb078AlphaDummy651 g)} : Finset Var) ∪ ({(nb078AlphaDummy652 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
            (Class.cv (nb078AlphaDummy651 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0670 :
    (nb078AlphaDummy650) ∈
      (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy650))
            (synCcnv (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy649)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0671 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (({(nb078AlphaDummy651 g)} : Finset Var) ∪ ({(nb078AlphaDummy652 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
            (Class.cv (nb078AlphaDummy651 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0672 :
    (nb078AlphaDummy649) ∈
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0673 :
    (nb078AlphaDummy649) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCphi (Class.cv (nb078AlphaDummy656)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy656) from (by
            unfold nb078AlphaDummy656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0674 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0675 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCphi (Class.cv (nb078AlphaDummy658 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy658 g) from (by
            unfold nb078AlphaDummy658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0676 :
    (nb078AlphaDummy649) ∈
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv ∪
        ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy656) from (by
            unfold nb078AlphaDummy656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0677 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy658 g) from (by
            unfold nb078AlphaDummy658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0678 :
    (nb078AlphaDummy656) ∈ (((Class.cv (nb078AlphaDummy656))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0679 (g : Var) :
    (nb078AlphaDummy658 g) ∈ (((Class.cv (nb078AlphaDummy658 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0680 :
    (nb078AlphaDummy663) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy663)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy663)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy663))).fv) :=
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

theorem nb078_support_mem_0681 (g : Var) :
    (nb078AlphaDummy665 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy665 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy665 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy665 g))).fv) :=
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

theorem nb078_support_mem_0682 :
    (nb078AlphaDummy663) ∈
      (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0683 (g : Var) :
    (nb078AlphaDummy665 g) ∈
      (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0684 :
    (nb078AlphaDummy670) ∈
      (((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy670))
            (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0685 (g : Var) :
    (nb078AlphaDummy673 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0686 :
    (nb078AlphaDummy670) ∈
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0687 (g : Var) :
    (nb078AlphaDummy673 g) ∈
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0688 :
    (nb078AlphaDummy671) ∈
      (((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy670))
            (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0689 (g : Var) :
    (nb078AlphaDummy674 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0690 :
    (nb078AlphaDummy671) ∈
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0691 (g : Var) :
    (nb078AlphaDummy674 g) ∈
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0692 :
    (nb078AlphaDummy670) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy670)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0693 (g : Var) :
    (nb078AlphaDummy673 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy673 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0694 :
    (nb078AlphaDummy670) ∈
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy670))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0695 (g : Var) :
    (nb078AlphaDummy673 g) ∈
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy673 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0696 :
    (nb078AlphaDummy671) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy670)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0697 (g : Var) :
    (nb078AlphaDummy674 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy673 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0698 :
    (nb078AlphaDummy671) ∈
      (((Class.cv (nb078AlphaDummy671))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0699 (g : Var) :
    (nb078AlphaDummy674 g) ∈
      (((Class.cv (nb078AlphaDummy674 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0700 :
    (nb078AlphaDummy650) ∈
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0701 :
    (nb078AlphaDummy650) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCphi (Class.cv (nb078AlphaDummy656)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy656) from (by
            unfold nb078AlphaDummy656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0702 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0703 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCphi (Class.cv (nb078AlphaDummy658 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy658 g) from (by
            unfold nb078AlphaDummy658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0704 :
    (nb078AlphaDummy650) ∈
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy655) from (by
          unfold nb078AlphaDummy655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy656) from (by
            unfold nb078AlphaDummy656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0705 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy657 g) from (by
          unfold nb078AlphaDummy657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy658 g) from (by
            unfold nb078AlphaDummy658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0706 :
    (nb078AlphaDummy656) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy656))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0707 (g : Var) :
    (nb078AlphaDummy658 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy658 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0708 :
    (nb078AlphaDummy656) ∈
      (((synCphi (Class.cv (nb078AlphaDummy656)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy656)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0709 (g : Var) :
    (nb078AlphaDummy658 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0710 :
    (nb078AlphaDummy650) ∈
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0711 :
    (nb078AlphaDummy650) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCphi (Class.cv (nb078AlphaDummy692)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy692) from (by
            unfold nb078AlphaDummy692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0712 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0713 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCphi (Class.cv (nb078AlphaDummy694 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy694 g) from (by
            unfold nb078AlphaDummy694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0714 :
    (nb078AlphaDummy650) ∈
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv ∪
        ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy692) from (by
            unfold nb078AlphaDummy692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0715 (g : Var) :
    (nb078AlphaDummy652 g) ∈
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy694 g) from (by
            unfold nb078AlphaDummy694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0716 :
    (nb078AlphaDummy692) ∈ (((Class.cv (nb078AlphaDummy692))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0717 (g : Var) :
    (nb078AlphaDummy694 g) ∈ (((Class.cv (nb078AlphaDummy694 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0718 :
    (nb078AlphaDummy699) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy699)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy699)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy699))).fv) :=
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

theorem nb078_support_mem_0719 (g : Var) :
    (nb078AlphaDummy701 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy701 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy701 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy701 g))).fv) :=
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

theorem nb078_support_mem_0720 :
    (nb078AlphaDummy699) ∈
      (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0721 (g : Var) :
    (nb078AlphaDummy701 g) ∈
      (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0722 :
    (nb078AlphaDummy706) ∈
      (((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy706))
            (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0723 (g : Var) :
    (nb078AlphaDummy709 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0724 :
    (nb078AlphaDummy706) ∈
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0725 (g : Var) :
    (nb078AlphaDummy709 g) ∈
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0726 :
    (nb078AlphaDummy707) ∈
      (((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy706))
            (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0727 (g : Var) :
    (nb078AlphaDummy710 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0728 :
    (nb078AlphaDummy707) ∈
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0729 (g : Var) :
    (nb078AlphaDummy710 g) ∈
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0730 :
    (nb078AlphaDummy706) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy706)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0731 (g : Var) :
    (nb078AlphaDummy709 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy709 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0732 :
    (nb078AlphaDummy706) ∈
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy706))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0733 (g : Var) :
    (nb078AlphaDummy709 g) ∈
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy709 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0734 :
    (nb078AlphaDummy707) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy706)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0735 (g : Var) :
    (nb078AlphaDummy710 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy709 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0736 :
    (nb078AlphaDummy707) ∈
      (((Class.cv (nb078AlphaDummy707))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0737 (g : Var) :
    (nb078AlphaDummy710 g) ∈
      (((Class.cv (nb078AlphaDummy710 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0738 :
    (nb078AlphaDummy649) ∈
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0739 :
    (nb078AlphaDummy649) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCphi (Class.cv (nb078AlphaDummy692)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy692) from (by
            unfold nb078AlphaDummy692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0740 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part027`. -/


section

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

theorem nb078_support_mem_0741 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCphi (Class.cv (nb078AlphaDummy694 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy694 g) from (by
            unfold nb078AlphaDummy694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0742 :
    (nb078AlphaDummy649) ∈
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy691) from (by
          unfold nb078AlphaDummy691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy692) from (by
            unfold nb078AlphaDummy692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0743 (g : Var) :
    (nb078AlphaDummy651 g) ∈
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy693 g) from (by
          unfold nb078AlphaDummy693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy694 g) from (by
            unfold nb078AlphaDummy694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0744 :
    (nb078AlphaDummy692) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy692))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0745 (g : Var) :
    (nb078AlphaDummy694 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy694 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0746 :
    (nb078AlphaDummy692) ∈
      (((synCphi (Class.cv (nb078AlphaDummy692)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy692)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0747 (g : Var) :
    (nb078AlphaDummy694 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0748 :
    (nb078AlphaDummy001) ∈
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv) :=
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

theorem nb078_support_mem_0749 (g : Var) :
    g ∈
      (((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
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

theorem nb078_support_mem_0750 :
    (nb078AlphaDummy001) ∈
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001)))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0751 (g : Var) :
    g ∈
      (((synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))).fv ∪
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

theorem nb078_support_mem_0752 :
    (nb078AlphaDummy001) ∈
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0753 :
    (nb078AlphaDummy001) ∈
      (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy001) ≠ (nb078AlphaDummy571) from (by
          unfold nb078AlphaDummy571;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0752) 2))))
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

theorem nb078_support_mem_0754 (g : Var) :
    g ∈ (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0755 (g : Var) :
    g ∈
      (({(nb078AlphaDummy572 g)} : Finset Var) ∪ ({(nb078AlphaDummy573 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb078AlphaDummy574 g) from (by
          unfold nb078AlphaDummy574;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0754 g) 2))))
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

theorem nb078_support_mem_0756 :
    (nb078AlphaDummy001) ∈
      (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy650))
            (synCcnv (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy649)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0757 (g : Var) :
    g ∈
      (({(nb078AlphaDummy651 g)} : Finset Var) ∪ ({(nb078AlphaDummy652 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
            (Class.cv (nb078AlphaDummy651 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0758 :
    (nb078AlphaDummy001) ∈ (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0759 (g : Var) : g ∈ (((synCcnv (Class.cv g))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0760 :
    (nb078AlphaDummy571) ∈
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0761 :
    (nb078AlphaDummy571) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCphi (Class.cv (nb078AlphaDummy728)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy728) from (by
            unfold nb078AlphaDummy728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0762 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0763 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCphi (Class.cv (nb078AlphaDummy730 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy730 g) from (by
            unfold nb078AlphaDummy730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0764 :
    (nb078AlphaDummy571) ∈
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv ∪
        ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy571) ≠ (nb078AlphaDummy728) from (by
            unfold nb078AlphaDummy728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0765 (g : Var) :
    (nb078AlphaDummy574 g) ∈
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy574 g) ≠ (nb078AlphaDummy730 g) from (by
            unfold nb078AlphaDummy730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0766 :
    (nb078AlphaDummy728) ∈ (((Class.cv (nb078AlphaDummy728))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0767 (g : Var) :
    (nb078AlphaDummy730 g) ∈ (((Class.cv (nb078AlphaDummy730 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0768 :
    (nb078AlphaDummy735) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy735)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy735)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy735))).fv) :=
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

theorem nb078_support_mem_0769 (g : Var) :
    (nb078AlphaDummy737 g) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy737 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy737 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy737 g))).fv) :=
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

theorem nb078_support_mem_0770 :
    (nb078AlphaDummy735) ∈
      (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0771 (g : Var) :
    (nb078AlphaDummy737 g) ∈
      (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0772 :
    (nb078AlphaDummy742) ∈
      (((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy742))
            (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0773 (g : Var) :
    (nb078AlphaDummy745 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0774 :
    (nb078AlphaDummy742) ∈
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0775 (g : Var) :
    (nb078AlphaDummy745 g) ∈
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0776 :
    (nb078AlphaDummy743) ∈
      (((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy742))
            (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0777 (g : Var) :
    (nb078AlphaDummy746 g) ∈
      (((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0778 :
    (nb078AlphaDummy743) ∈
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0779 (g : Var) :
    (nb078AlphaDummy746 g) ∈
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0780 :
    (nb078AlphaDummy742) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy742)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0781 (g : Var) :
    (nb078AlphaDummy745 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy745 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0782 :
    (nb078AlphaDummy742) ∈
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy742))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0783 (g : Var) :
    (nb078AlphaDummy745 g) ∈
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy745 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0784 :
    (nb078AlphaDummy743) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy742)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0785 (g : Var) :
    (nb078AlphaDummy746 g) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy745 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0786 :
    (nb078AlphaDummy743) ∈
      (((Class.cv (nb078AlphaDummy743))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0787 (g : Var) :
    (nb078AlphaDummy746 g) ∈
      (((Class.cv (nb078AlphaDummy746 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0788 :
    (nb078AlphaDummy570) ∈
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0789 :
    (nb078AlphaDummy570) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCphi (Class.cv (nb078AlphaDummy728)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy728) from (by
            unfold nb078AlphaDummy728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0790 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0791 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCphi (Class.cv (nb078AlphaDummy730 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy730 g) from (by
            unfold nb078AlphaDummy730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0792 :
    (nb078AlphaDummy570) ∈
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy727) from (by
          unfold nb078AlphaDummy727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy728) from (by
            unfold nb078AlphaDummy728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0793 (g : Var) :
    (nb078AlphaDummy573 g) ∈
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy729 g) from (by
          unfold nb078AlphaDummy729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy730 g) from (by
            unfold nb078AlphaDummy730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0794 :
    (nb078AlphaDummy728) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy728))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0795 (g : Var) :
    (nb078AlphaDummy730 g) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy730 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0796 :
    (nb078AlphaDummy728) ∈
      (((synCphi (Class.cv (nb078AlphaDummy728)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy728)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0797 (g : Var) :
    (nb078AlphaDummy730 g) ∈
      (((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0798 :
    (nb078AlphaDummy767) ∈
      (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0799 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (({(nb078AlphaDummy770 h)} : Finset Var) ∪ ({(nb078AlphaDummy771 h)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0800 :
    (nb078AlphaDummy768) ∈
      (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0801 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (({(nb078AlphaDummy770 h)} : Finset Var) ∪ ({(nb078AlphaDummy771 h)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0802 :
    (nb078AlphaDummy767) ∈
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0803 :
    (nb078AlphaDummy767) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCphi (Class.cv (nb078AlphaDummy776)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy775) from (by
          unfold nb078AlphaDummy775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy776) from (by
            unfold nb078AlphaDummy776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0804 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0805 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCphi (Class.cv (nb078AlphaDummy778 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy777 h) from (by
          unfold nb078AlphaDummy777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy778 h) from (by
            unfold nb078AlphaDummy778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0806 :
    (nb078AlphaDummy767) ∈
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv ∪
        ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy775) from (by
          unfold nb078AlphaDummy775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy776) from (by
            unfold nb078AlphaDummy776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0807 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy777 h) from (by
          unfold nb078AlphaDummy777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy778 h) from (by
            unfold nb078AlphaDummy778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0808 :
    (nb078AlphaDummy776) ∈ (((Class.cv (nb078AlphaDummy776))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0809 (h : Var) :
    (nb078AlphaDummy778 h) ∈ (((Class.cv (nb078AlphaDummy778 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0810 :
    (nb078AlphaDummy783) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy783)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy783)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy783))).fv) :=
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

theorem nb078_support_mem_0811 (h : Var) :
    (nb078AlphaDummy785 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy785 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy785 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy785 h))).fv) :=
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

theorem nb078_support_mem_0812 :
    (nb078AlphaDummy783) ∈
      (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0813 (h : Var) :
    (nb078AlphaDummy785 h) ∈
      (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0814 :
    (nb078AlphaDummy790) ∈
      (((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy790))
            (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0815 (h : Var) :
    (nb078AlphaDummy793 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0816 :
    (nb078AlphaDummy790) ∈
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0817 (h : Var) :
    (nb078AlphaDummy793 h) ∈
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0818 :
    (nb078AlphaDummy791) ∈
      (((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy790))
            (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0819 (h : Var) :
    (nb078AlphaDummy794 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0820 :
    (nb078AlphaDummy791) ∈
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0821 (h : Var) :
    (nb078AlphaDummy794 h) ∈
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0822 :
    (nb078AlphaDummy790) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy790)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0823 (h : Var) :
    (nb078AlphaDummy793 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy793 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0824 :
    (nb078AlphaDummy790) ∈
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy790))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0825 (h : Var) :
    (nb078AlphaDummy793 h) ∈
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy793 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0826 :
    (nb078AlphaDummy791) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy790)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0827 (h : Var) :
    (nb078AlphaDummy794 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy793 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0828 :
    (nb078AlphaDummy791) ∈
      (((Class.cv (nb078AlphaDummy791))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0829 (h : Var) :
    (nb078AlphaDummy794 h) ∈
      (((Class.cv (nb078AlphaDummy794 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0830 :
    (nb078AlphaDummy768) ∈
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0831 :
    (nb078AlphaDummy768) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCphi (Class.cv (nb078AlphaDummy776)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy775) from (by
          unfold nb078AlphaDummy775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy776) from (by
            unfold nb078AlphaDummy776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0832 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0833 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCphi (Class.cv (nb078AlphaDummy778 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy777 h) from (by
          unfold nb078AlphaDummy777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy778 h) from (by
            unfold nb078AlphaDummy778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0834 :
    (nb078AlphaDummy768) ∈
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy775) from (by
          unfold nb078AlphaDummy775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy776) from (by
            unfold nb078AlphaDummy776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0835 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy777 h) from (by
          unfold nb078AlphaDummy777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy778 h) from (by
            unfold nb078AlphaDummy778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0836 :
    (nb078AlphaDummy776) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy776))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0837 (h : Var) :
    (nb078AlphaDummy778 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy778 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0838 :
    (nb078AlphaDummy776) ∈
      (((synCphi (Class.cv (nb078AlphaDummy776)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy776)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0839 (h : Var) :
    (nb078AlphaDummy778 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0840 :
    (nb078AlphaDummy767) ∈
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0841 :
    (nb078AlphaDummy767) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCphi (Class.cv (nb078AlphaDummy812)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy812) from (by
            unfold nb078AlphaDummy812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0842 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0843 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCphi (Class.cv (nb078AlphaDummy814 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy814 h) from (by
            unfold nb078AlphaDummy814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0844 :
    (nb078AlphaDummy767) ∈
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv ∪
        ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy812) from (by
            unfold nb078AlphaDummy812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0845 (h : Var) :
    (nb078AlphaDummy770 h) ∈
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy814 h) from (by
            unfold nb078AlphaDummy814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0846 :
    (nb078AlphaDummy812) ∈ (((Class.cv (nb078AlphaDummy812))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0847 (h : Var) :
    (nb078AlphaDummy814 h) ∈ (((Class.cv (nb078AlphaDummy814 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0848 :
    (nb078AlphaDummy819) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy819)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy819)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy819))).fv) :=
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

theorem nb078_support_mem_0849 (h : Var) :
    (nb078AlphaDummy821 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy821 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy821 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy821 h))).fv) :=
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

theorem nb078_support_mem_0850 :
    (nb078AlphaDummy819) ∈
      (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0851 (h : Var) :
    (nb078AlphaDummy821 h) ∈
      (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0852 :
    (nb078AlphaDummy826) ∈
      (((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy826))
            (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0853 (h : Var) :
    (nb078AlphaDummy829 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0854 :
    (nb078AlphaDummy826) ∈
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0855 (h : Var) :
    (nb078AlphaDummy829 h) ∈
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0856 :
    (nb078AlphaDummy827) ∈
      (((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy826))
            (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0857 (h : Var) :
    (nb078AlphaDummy830 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0858 :
    (nb078AlphaDummy827) ∈
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0859 (h : Var) :
    (nb078AlphaDummy830 h) ∈
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0860 :
    (nb078AlphaDummy826) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy826)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0861 (h : Var) :
    (nb078AlphaDummy829 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy829 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0862 :
    (nb078AlphaDummy826) ∈
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy826))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0863 (h : Var) :
    (nb078AlphaDummy829 h) ∈
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy829 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0864 :
    (nb078AlphaDummy827) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy826)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0865 (h : Var) :
    (nb078AlphaDummy830 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy829 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0866 :
    (nb078AlphaDummy827) ∈
      (((Class.cv (nb078AlphaDummy827))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0867 (h : Var) :
    (nb078AlphaDummy830 h) ∈
      (((Class.cv (nb078AlphaDummy830 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0868 :
    (nb078AlphaDummy769) ∈
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0869 :
    (nb078AlphaDummy769) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCphi (Class.cv (nb078AlphaDummy812)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy812) from (by
            unfold nb078AlphaDummy812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0870 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0871 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCphi (Class.cv (nb078AlphaDummy814 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy814 h) from (by
            unfold nb078AlphaDummy814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0872 :
    (nb078AlphaDummy769) ∈
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy812) from (by
            unfold nb078AlphaDummy812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0873 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy814 h) from (by
            unfold nb078AlphaDummy814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0874 :
    (nb078AlphaDummy812) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy812))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0875 (h : Var) :
    (nb078AlphaDummy814 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy814 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0876 :
    (nb078AlphaDummy812) ∈
      (((synCphi (Class.cv (nb078AlphaDummy812)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy812)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0877 (h : Var) :
    (nb078AlphaDummy814 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
